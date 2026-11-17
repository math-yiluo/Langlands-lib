import Langlands.GroupScheme.MatrixRepresentation.NonAffineNormalFixedCoordinates
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.QuasiCompactHomImage
import Langlands.GroupScheme.SmoothFieldComponent
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # Unipotent extensions and radical preimages without affine sources -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- An fpqc extension of unipotent group schemes is unipotent, without
an affineness assumption on the source or kernel. -/
theorem isUnipotent_of_kernel_of_quotient_of_fpqc (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hK : IsUnipotent (kernel q)) (hQ : IsUnipotent Q) : IsUnipotent G := by
  intro n _ _ _ ρ
  classical
  obtain ⟨v, hv, hfix⟩ := hK n (ρ.restrict (kernelι q))
  let W := (ρ.restrict (kernelι q)).fixedSubmodule
  let w : W := ⟨v, hfix⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have hd : 0 < Module.finrank k W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w, hw⟩
  let : Nonempty (Fin (Module.finrank k W)) := ⟨⟨0, hd⟩⟩
  obtain ⟨B, C, hCB, hcols, hproj⟩ := MatrixRepresentation.exists_fixed_coordinates W
  have hN : (SubgroupFunctor.range (kernelι q)).IsNormal := by
    intro T g x _ hx
    apply (mem_range_kernelι_iff q _).mpr
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
      (mem_range_kernelι_iff q x).mp hx]
    simp
  have hs : ρ.IsStableCoordinates B C :=
    ρ.normal_fixed_coordinates_of_affine_tests (kernelι q) hN B C hcols hproj
  let r := ρ.restrictCoordinates B C hCB hs
  let d := ρ.quotientFixedCoordinates q B C hCB hs hcols
  obtain ⟨z, hz, hdz⟩ := hQ (Fin (Module.finrank k W)) d
  have hrz : r.IsFixedVector z := by
    have h := (MatrixRepresentation.isFixedVector_restrict_iff d q z).2 hdz
    change MatrixRepresentation.IsFixedVector (q ≫ d) z at h
    have hfac : q ≫ d = r := ρ.quotientFixedCoordinates_fac q B C hCB hs hcols
    rwa [hfac] at h
  refine ⟨B *ᵥ z, ?_, ρ.isFixedVector_mulVec_restrictCoordinates B C hCB hs hrz⟩
  intro hbz
  apply hz
  exact MatrixRepresentation.coordinateInclusion_injective B C hCB
    (hbz.trans (Matrix.mulVec_zero B).symm)


namespace SmoothUnipotentQuotient

variable (q : G ⟶ Q) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]

/-- The image of a smooth connected normal unipotent subgroup lies in a
supplied target radical, even when the source group is not affine. -/
theorem range_le_comap_radical
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    (i : U ⟶ G) (j : V ⟶ Q)
    (hsm : Smooth U.X.hom) (hc : ConnectedSpace U.X.left)
    (hu : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
    (hj : IsUnipotentRadical j) :
    SubgroupFunctor.range i ≤ (SubgroupFunctor.range j).comap q := by
  have : Smooth U.X.hom := hsm
  have : ConnectedSpace U.X.left := hc
  have : QuasiCompact U.X.hom := quasiCompact_of_smooth_connected U
  have : CompactSpace U.X.left := QuasiCompact.compactSpace_of_compactSpace U.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : QuasiCompact (i ≫ q).hom.hom.left := inferInstance
  let d := QuasiCompactHomImage.ofSmoothConnected (i ≫ q)
  have : IsClosedImmersion d.inclusion.hom.hom.left := d.isClosedSubgroup
  have : Mono d.inclusion.hom.hom := Over.mono_of_mono_left _
  have : Flat d.projection.hom.hom.left := d.flat
  have : Surjective d.projection.hom.hom.left := d.surjective
  have : QuasiCompact d.projection.hom.hom.left := d.quasiCompact
  have hdu : IsUnipotent d.D := hu.of_flat_surjective d.projection
  have hdn : (SubgroupFunctor.range d.inclusion).IsNormal :=
    SubgroupFunctor.isNormal_range_of_fpqc_square i q d.projection d.inclusion
      d.factorization.symm hn
  have hle := hj.greatest d.D d.inclusion d.isClosedSubgroup
    d.smooth d.connected hdu hdn
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply hle T
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ d.projection.hom.hom, ?_⟩
  change (y ≫ d.projection.hom.hom) ≫ d.inclusion.hom.hom =
    (y ≫ i.hom.hom) ≫ q.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, d.factorization,
    Grp.comp_hom_hom, ← Category.assoc]

/-- The full inverse image of a target radical is a radical under a supplied
smooth surjective quasi-compact map with smooth connected unipotent kernel.
The source and the kernel are permitted to be nonaffine. -/
theorem isUnipotentRadical_preimage
    (hq : HasSmoothConnectedUnipotentKernel q)
    {V : GroupScheme (Spec (CommRingCat.of k))} (j : V ⟶ Q)
    (hj : IsUnipotentRadical j) :
    IsUnipotentRadical (SubgroupPreimage.inclusion q j) := by
  have : Smooth (kernel q).X.hom := hq.1
  have : ConnectedSpace (kernel q).X.left := hq.2.1
  have : QuasiCompact (kernel q).X.hom := quasiCompact_of_smooth_connected _
  have : GeometricallyConnected (kernel q).X.hom :=
    geometricallyConnected_of_connected (kernel q)
  have : Smooth V.X.hom := hj.smooth
  have : ConnectedSpace V.X.left := hj.connectedSpace
  have : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  have : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.surjective_projection q j
  have : QuasiCompact (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.quasiCompact_projection q j
  refine ⟨SubgroupPreimage.isClosedSubgroup q j hj.isClosedSubgroup,
    SubgroupPreimage.smooth q j,
    SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q j,
    isUnipotent_of_kernel_of_quotient_of_fpqc (SubgroupPreimage.projection q j)
      (SubgroupPreimage.isUnipotent_kernel q j hq.2.2) hj.isUnipotent,
    SubgroupPreimage.isNormal q j hj.isNormal, ?_⟩
  intro H i hi hs hc hu hn
  rw [SubgroupPreimage.range_inclusion]
  exact range_le_comap_radical q i j hs hc hu hn hj

/-- The source radical is the inverse image of the target radical on every
scheme test. -/
theorem radical_comap_eq
    (hq : HasSmoothConnectedUnipotentKernel q)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i := by
  rw [← SubgroupPreimage.range_inclusion]
  exact (isUnipotentRadical_preimage q hq j hj).range_eq hi

/-- An actual source comparison from a supplied radical to the inverse image
of a target radical. -/
def radicalPreimageIso
    (hq : HasSmoothConnectedUnipotentKernel q)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    U ≅ SubgroupPreimage.groupScheme q j :=
  IsClosedSubgroup.sourceIsoOfRangeEq hi.isClosedSubgroup
    (SubgroupPreimage.isClosedSubgroup q j hj.isClosedSubgroup)
    (hi.range_eq (isUnipotentRadical_preimage q hq j hj))

/-- The comparison preserves the actual subgroup inclusions. -/
@[reassoc]
theorem radicalPreimageIso_hom_comp
    (hq : HasSmoothConnectedUnipotentKernel q)
    {U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} {j : V ⟶ Q}
    (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    (radicalPreimageIso q hq hi hj).hom ≫ SubgroupPreimage.inclusion q j = i :=
  IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ _

end SmoothUnipotentQuotient

end Langlands.GroupScheme
