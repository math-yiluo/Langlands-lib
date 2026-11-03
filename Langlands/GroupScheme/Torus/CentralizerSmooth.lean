import Langlands.GroupScheme.Torus.FixedPointLifting
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Rational.TorusNormalizerStatement

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

open Corepresented

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)

/-- The centralizer in reconstructed coordinates lifts through square-zero extensions. -/
theorem centralizer_hasSquareZeroLifting
    [Algebra.FormallySmooth R (algebra G)] :
    HasSquareZeroLifting
      (affineSubgroups (SubgroupFunctor.range (coordinateHom i)).centralizer) := by
  intro C N hN x hx
  let A : CommAlgCat.{u} R := CommAlgCat.of R (C ⧸ N)
  let e := groupSchemeIso G
  let x₀ := (affinePointsEquiv (functor G) (corepresentation G) A).symm x
  have hx₀ : x₀ ∈
      (SubgroupFunctor.range (coordinateHom i)).centralizer.carrier
        ((algSpec R).obj (op A)) := hx
  have hxG : x₀ ≫ e.hom.hom.hom ∈ (torusCentralizer i).carrier
      ((algSpec R).obj (op A)) := by
    rw [torusCentralizer_eq_centralizer_range,
      SubgroupFunctor.centralizer_range_eq_comap_of_iso i e.symm]
    change (x₀ ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈
      (SubgroupFunctor.range (coordinateHom i)).centralizer.carrier _
    simpa only [SubgroupFunctor.comp_hom_comp_inv_hom] using hx₀
  have hxfix : (AutomorphicAction.conjugation i).toPointwiseSchemeAction.IsFixed
      (x₀ ≫ e.hom.hom.hom) := by
    change (x₀ ≫ e.hom.hom.hom) ∈
      (AutomorphicAction.conjugation i).fixedSubgroup.carrier _
    rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
  obtain ⟨y, hy, hred⟩ := PointwiseSchemeAction.exists_fixed_lift
    (AutomorphicAction.conjugation i).toPointwiseSchemeAction N ⟨2, hN⟩
    (x₀ ≫ e.hom.hom.hom) hxfix
  let y₀ := y ≫ e.inv.hom.hom
  have hyG : y ∈ (torusCentralizer i).carrier ((algSpec R).obj (op C)) := by
    rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
    exact hy
  have hy₀ : y₀ ∈ (SubgroupFunctor.range (coordinateHom i)).centralizer.carrier
      ((algSpec R).obj (op C)) := by
    rw [torusCentralizer_eq_centralizer_range,
      SubgroupFunctor.centralizer_range_eq_comap_of_iso i e.symm] at hyG
    exact hyG
  refine ⟨affinePointsEquiv (functor G) (corepresentation G) C y₀, ?_, ?_⟩
  · change (affinePointsEquiv (functor G) (corepresentation G) C).symm
      (affinePointsEquiv (functor G) (corepresentation G) C y₀) ∈
      (SubgroupFunctor.range (coordinateHom i)).centralizer.carrier _
    simpa only [MulEquiv.symm_apply_apply] using hy₀
  · rw [← affinePointsEquiv_naturality]
    have heq : (algSpec R).map (reduction C N).op ≫ y₀ = x₀ := by
      dsimp only [y₀]
      rw [← Category.assoc, hred, SubgroupFunctor.comp_hom_comp_inv_hom]
    rw [heq]
    exact MulEquiv.apply_symm_apply _ x

end AffineCoordinates

/-- A closed diagonalizable subgroup of a smooth affine group over a field has a smooth
closed centralizer on all test schemes. -/
theorem diagonalizableCentralizer_hasSmoothClosedRepresentative
    {k : Type u} [Field k] {M : Type u} [AddCommGroup M]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    (i : (Diagonalizable.groupScheme (CommRingCat.of k) M).toGrp ⟶ G)
    (hi : IsClosedSubgroup i) (hG : Smooth G.X.hom) :
    (torusCentralizer i).HasSmoothClosedRepresentative := by
  have : IsClosedImmersion i.hom.hom.left := hi
  let : Algebra.Smooth (CommRingCat.of k) (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G hG
  obtain ⟨I, hI⟩ := Corepresented.exists_ideal_range (AffineCoordinates.coordinateHom i)
  let hJ := Corepresented.isCutOutBy_affineSubgroups_centralizer hI
  let : Algebra.FormallySmooth (CommRingCat.of k)
      (AffineCoordinates.algebra G ⧸
        Corepresented.subgroupCentralizerIdeal (AffineCoordinates.corepresentation G) I) :=
    Corepresented.formallySmooth_of_hasSquareZeroLifting hJ
      (AffineCoordinates.centralizer_hasSquareZeroLifting i)
  let : Algebra.FinitePresentation (CommRingCat.of k)
      (AffineCoordinates.algebra G ⧸
        Corepresented.subgroupCentralizerIdeal (AffineCoordinates.corepresentation G) I) :=
    Corepresented.finitePresentation_quotient _
  let : Algebra.Smooth (CommRingCat.of k)
      (AffineCoordinates.algebra G ⧸
        Corepresented.subgroupCentralizerIdeal (AffineCoordinates.corepresentation G) I) := {}
  rw [torusCentralizer_eq_centralizer_range]
  exact ⟨_, _, AffineCoordinates.isClosedSubgroup_centralizer_range hI,
    Corepresented.smooth_cutGroupScheme hJ,
    AffineCoordinates.isRepresentedBy_centralizer_range hI⟩

namespace SubgroupFunctor

/-- An isomorphism of the source preserves the range on every test scheme. -/
theorem range_precomp_iso {S : Scheme.{u}} {H H' G : GroupScheme S}
    (e : H' ≅ H) (i : H ⟶ G) : range (e.hom ≫ i) = range i := by
  apply ext
  intro U
  ext g
  rw [mem_range, mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t ≫ e.hom.hom.hom, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc]
  · rintro ⟨t, rfl⟩
    refine ⟨t ≫ e.inv.hom.hom, ?_⟩
    have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X := by
      rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
    rw [Grp.comp_hom_hom, ← Category.assoc, Category.assoc t, he, Category.comp_id]

end SubgroupFunctor

/-- The centralizer of a split subtorus of a smooth affine group over any field has a smooth
closed representative on all test schemes. -/
theorem torusCentralizer_hasSmoothClosedRepresentative
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsSplitSubtorus i) (hG : Smooth G.X.hom) :
    (torusCentralizer i).HasSmoothClosedRepresentative := by
  classical
  obtain ⟨I, hfin, ⟨eT⟩⟩ := hi.1
  let : Fintype I := Fintype.ofFinite I
  let e := Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ)) ≪≫ eT.symm
  have hei : IsClosedSubgroup (e.hom ≫ i) := by
    have : IsClosedImmersion e.hom.hom.hom.left := IsClosedSubgroup.of_iso e
    have : IsClosedImmersion i.hom.hom.left := hi.2
    change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have h := diagonalizableCentralizer_hasSmoothClosedRepresentative (e.hom ≫ i) hei hG
  rw [torusCentralizer_eq_centralizer_range,
    SubgroupFunctor.range_precomp_iso, ← torusCentralizer_eq_centralizer_range] at h
  exact h

/-- A chosen smooth closed group scheme representing the centralizer of a split subtorus. -/
def smoothCentralizerGroupScheme
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsSplitSubtorus i) (hG : Smooth G.X.hom) :
    GroupScheme (Spec (CommRingCat.of k)) :=
  (torusCentralizer_hasSmoothClosedRepresentative i hi hG).choose

/-- The chosen centralizer group scheme admits a closed immersion into `G`, is smooth, and
represents the centralizer on every test scheme. -/
theorem smoothCentralizerGroupScheme_spec
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsSplitSubtorus i) (hG : Smooth G.X.hom) :
    ∃ j : smoothCentralizerGroupScheme i hi hG ⟶ G,
      IsClosedSubgroup j ∧ Smooth (smoothCentralizerGroupScheme i hi hG).X.hom ∧
        (torusCentralizer i).IsRepresentedBy j :=
  (torusCentralizer_hasSmoothClosedRepresentative i hi hG).choose_spec

end Langlands.GroupScheme
