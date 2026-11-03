import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Rational.SemigroupImageTransport
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.ImageEnvelopeStabilityProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Semisimplicity of the source of a central isogeny -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section Epi

variable {S : Scheme.{u}} {C D : GroupScheme S}

/-- A subgroup functor of an affine group with a closed representative is everything
as soon as it contains the range of a homomorphism that is an epimorphism over the base. -/
theorem SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le
    {F : SubgroupFunctor C} [IsAffine C.X.left] (hF : F.HasClosedRepresentative)
    (p : D ⟶ C) [Epi p.hom.hom] (hp : SubgroupFunctor.range p ≤ F) : F = ⊤ := by
  obtain ⟨E, j, hjc, hj⟩ := hF
  have : IsClosedImmersion j.hom.hom.left := hjc
  have hfac : (hj.factorHom p hp).hom.hom ≫ j.hom.hom = p.hom.hom :=
    congrArg (fun a => a.hom.hom) (hj.factorHom_comp p hp)
  have : Epi j.hom.hom := epi_of_epi_fac hfac
  have : IsIso j.hom.hom := isIso_of_isClosedImmersion_of_epi_over j.hom.hom
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    exact Subgroup.mem_top _
  · intro _
    rw [← hj.2]
    refine ⟨x ≫ inv j.hom.hom, ?_⟩
    change (x ≫ inv j.hom.hom) ≫ j.hom.hom = x
    simp

end Epi

section Unipotence

namespace MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} {n : Type} [Fintype n]
  [DecidableEq n]

/-- Restriction along a homomorphism with injective pullback on global functions changes
no fixed-vector equation. -/
theorem isFixedVector_restrict_iff_of_injective (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    (hq : Function.Injective q.hom.hom.left.appTop) (v : n → R) :
    (ρ.restrict q).IsFixedVector v ↔ ρ.IsFixedVector v := by
  constructor
  · intro h
    apply (ρ.isFixedVector_iff_universal v).2
    funext i
    apply hq
    have hi := congrFun (h H.X (𝟙 H.X)) i
    rw [pointMatrix_restrict, Category.id_comp] at hi
    have hmat := ρ.pointMatrix_naturality q.hom.hom (𝟙 G.X)
    rw [Category.comp_id] at hmat
    rw [hmat] at hi
    change (((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)).map
      q.hom.hom.left.appTop.hom) *ᵥ (fun j => scalarMap H.X (v j))) i = _ at hi
    rw [q.hom.hom.left.appTop.hom.map_mulVec]
    simpa only [Function.comp_def, scalarMap_naturality] using hi
  · intro h T x
    rw [pointMatrix_restrict]
    exact h T (x ≫ q.hom.hom)

end MatrixRepresentation

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Unipotence descends along a homomorphism with injective pullback on global functions,
for instance a dominant homomorphism onto a reduced group. -/
theorem IsUnipotent.of_appTop_injective (hH : IsUnipotent H) (q : H ⟶ G)
    (hq : Function.Injective q.hom.hom.left.appTop) : IsUnipotent G := by
  intro n hn hd hne ρ
  obtain ⟨v, hv, hfix⟩ := hH n (ρ.restrict q)
  exact ⟨v, hv, (ρ.isFixedVector_restrict_iff_of_injective q hq v).1 hfix⟩

end Unipotence

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, a homomorphism of affine groups that is an
epimorphism of schemes and has finite full kernel reflects triviality of the unipotent
radical from a smooth target. A smooth connected unipotent normal subgroup `U` of the source
has a smooth connected unipotent generated image in the target, normal because the source
points conjugate the image envelope into itself; so the image is trivial and `U` lies in
the finite kernel, which forces `U` to be trivial. -/
theorem HasTrivialUnipotentRadical.of_epi_of_finite_kernel_algClosed
    {D C : GroupScheme (Spec (CommRingCat.of k))} (p : D ⟶ C)
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [IsAffineHom D.X.hom]
    [Epi p.hom.hom.left] [IsFinite (kernel p).X.hom]
    (hC : HasTrivialUnipotentRadical C) : HasTrivialUnipotentRadical D := by
  intro U i hi hs hc hu hn
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  have : Smooth U.X.hom := hs
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hUint : GeometricallyIntegral U.X.hom :=
    smoothConnectedAffineGeometry.1 k U hs inferInstance hc
  let f : U ⟶ C := i ≫ p
  have horigin : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) ≫ f.hom.hom = 1 :=
    MonObj.one_comp _
  obtain ⟨E, hE⟩ := ImageGeneration.pointedImageGeneration k C inferInstance inferInstance U.X inferInstance
    inferInstance hUint 1 f.hom.hom horigin
  have : Smooth E.group.X.hom := hE.1
  have : IsAffineHom E.group.X.hom := hE.2.1
  have : GeometricallyConnected E.group.X.hom := hE.2.2.1
  have hEc : ConnectedSpace E.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := E.group.X.hom)
  -- The generated image is unipotent: the factor map is dominant onto a reduced group.
  let q := E.factorGroupHom f
  obtain ⟨n, _hn, hDom⟩ := hE.2.2.2
  have : IsDominant q.hom.hom.left := E.factorGroupHom_isDominant f n hDom
  have : IsReduced E.group.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      E.group.X.left E.group.X.hom
  have : IsSchemeTheoreticallyDominant q.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsAffine E.group.X.left := isAffine_of_isAffineHom E.group.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  have hEu : IsUnipotent E.group :=
    hu.of_appTop_injective q (q.hom.hom.left.app_injective ⊤)
  -- The generated image is normal: source points stabilise the image envelope.
  let c : AutomorphicAction D D := AutomorphicAction.conjugation (𝟙 D)
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hstab : c.IsStable (SubgroupFunctor.range i) := by
    intro T h g hg
    rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
    exact hn T h g (Subgroup.mem_top _) hg
  let a := c.onRepresentedSubgroup i hrep hstab
  let b : AutomorphicAction D C := AutomorphicAction.conjugation p
  have hif : a.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction
      f.hom.hom := by
    intro T s x
    change a.act s x ≫ (i.hom.hom ≫ p.hom.hom) = b.act s (x ≫ (i.hom.hom ≫ p.hom.hom))
    rw [← Category.assoc, AutomorphicAction.onRepresentedSubgroup_act_comp,
      AutomorphicAction.conjugation_act, AutomorphicAction.conjugation_act,
      Grp.id_hom_hom, Category.comp_id, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, Category.assoc]
  have hstabE : b.IsStable (closedImageEnvelope f.hom.hom) :=
    b.closedImageEnvelope_isStable inferInstance a.toPointwiseSchemeAction f.hom.hom hif
  have hN : (SubgroupFunctor.range E.inclusion).normalizer.HasClosedRepresentative :=
    (hasClosedRepresentative_normalizer_centralizer_range E.inclusion E.closed).1
  have : Epi p.hom.hom := Over.epi_of_epi_left _
  have hpN : SubgroupFunctor.range p ≤ (SubgroupFunctor.range E.inclusion).normalizer := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro V a' z hz
    rw [E.represents.2] at hz ⊢
    constructor
    · have h := hstabE V (a' ≫ y) z hz
      rw [AutomorphicAction.conjugation_act] at h
      simpa only [Category.assoc] using h
    · have h := hstabE V (a' ≫ y)⁻¹ z hz
      rw [AutomorphicAction.conjugation_act, GrpObj.inv_comp, inv_inv] at h
      simpa only [Category.assoc] using h
  have hNtop := SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le hN p hpN
  have hEn : (SubgroupFunctor.range E.inclusion).IsNormal :=
    SubgroupFunctor.isNormal_of_normalizer_eq_top hNtop
  have hEbot := hC E.group E.inclusion E.closed hE.1 hEc hEu hEn
  -- Hence `U` maps trivially and lies in the finite kernel.
  have hincl : E.inclusion.hom.hom = 1 := by
    have h1 : 𝟙 E.group.X ≫ E.inclusion.hom.hom ∈
        (SubgroupFunctor.range E.inclusion).carrier E.group.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, rfl⟩
    rw [hEbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Category.id_comp] at h1
    exact h1
  have hf1 : i.hom.hom ≫ p.hom.hom = 1 := by
    have h := congrArg (fun g => g.hom.hom) (E.factorGroupHom_comp f)
    change q.hom.hom ≫ E.inclusion.hom.hom = i.hom.hom ≫ p.hom.hom at h
    rw [← h, hincl, MonObj.comp_one]
  obtain ⟨y, hy⟩ :=
    SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff p i.hom.hom).mpr hf1)
  have : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      U.X.left U.X.hom
  have hy1 : η[U.X] ≫ y = η[(kernel p).X] := by
    apply (cancel_mono (kernelι p).hom.hom).mp
    rw [Category.assoc, hy, IsMonHom.one_hom, IsMonHom.one_hom]
  have hy' := finiteTargetOverHom_eq_one_algClosed U (kernel p) y hy1
  have hi1 : i.hom.hom = 1 := by
    rw [← hy, hy', MonObj.one_comp]
  ext T x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨z, rfl⟩
    change z ≫ i.hom.hom = 1
    rw [hi1, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

end AlgClosed

section Field

variable {k : Type u} [Field k]

/-- The full centre of the source of a central isogeny onto an affine group with finite
centre is finite: the source centre maps into the target centre, because the target
points commuting with its image form a closed subgroup containing the epimorphic range. -/
theorem hasFiniteCenter_of_isCentralIsogeny {D C : GroupScheme (Spec (CommRingCat.of k))}
    (p : D ⟶ C) (hp : IsCentralIsogeny p) [IsAffineHom C.X.hom]
    (hC : HasFiniteCenter C) : HasFiniteCenter D := by
  have := hp.isFinite
  have := hp.flat
  have := hp.surjective
  have : IsAffineHom D.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  have : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  have : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  have : Epi p.hom.hom := Over.epi_of_epi_left _
  obtain ⟨Z, z, hz, hzc⟩ := fieldFixedSubgroupRepresentability k D D inferInstance
    (AutomorphicAction.conjugation (𝟙 D))
  have hzr : SubgroupFunctor.range z = center D :=
    hz.2.trans (conjugation_id_fixedSubgroup_eq_center D)
  have : IsClosedImmersion z.hom.hom.left := hzc
  have hZaff : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  let a : AutomorphicAction Z C := AutomorphicAction.conjugation (z ≫ p)
  obtain ⟨F, j, hj, hjc⟩ := fieldFixedSubgroupRepresentability k Z C hZaff a
  have hpF : SubgroupFunctor.range p ≤ a.fixedSubgroup := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro T' b h
    have hm : h ≫ z.hom.hom ∈ (center D).carrier T' := by
      rw [← hzr]
      exact SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩
    have hcz : Commute (h ≫ z.hom.hom) (b ≫ y) := commute_of_mem_center hm (b ≫ y)
    have e : ((h ≫ z.hom.hom) * (b ≫ y) * (h ≫ z.hom.hom)⁻¹) ≫ p.hom.hom =
        (b ≫ y) ≫ p.hom.hom := by
      rw [hcz.eq, mul_inv_cancel_right]
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at e
    rw [AutomorphicAction.conjugation_act]
    simpa only [Grp.comp_hom_hom, Category.assoc] using e
  have hFtop : a.fixedSubgroup = ⊤ :=
    SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le ⟨F, j, hjc, hj⟩ p hpF
  have hcen : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ Z.X),
      h ≫ (z ≫ p).hom.hom ∈ (center C).carrier T := by
    intro T h T' b c
    have hc : c ∈ a.fixedSubgroup.carrier T' := by
      rw [hFtop]
      exact Subgroup.mem_top _
    have e := hc T' (𝟙 T') (b ≫ h)
    rw [Category.id_comp, AutomorphicAction.conjugation_act] at e
    rw [← Category.assoc]
    exact mul_inv_eq_iff_eq_mul.mp e
  obtain ⟨ZC, zc, hzcC, hZCfin⟩ := hC
  have hmem : 𝟙 Z.X ≫ (z ≫ p).hom.hom ∈ (SubgroupFunctor.range zc).carrier Z.X := by
    rw [hzcC.2]
    exact hcen Z.X (𝟙 _)
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hmem
  have : IsClosedImmersion zc.hom.hom.left := hzcC.1
  have hwl : w.left ≫ zc.hom.hom.left = z.hom.hom.left ≫ p.hom.hom.left := by
    have h := congrArg (fun g => g.left) hw
    simpa only [Category.id_comp, Grp.comp_hom_hom, Over.comp_left] using h
  have : IsFinite (w.left ≫ zc.hom.hom.left) := by
    rw [hwl]
    infer_instance
  have : IsFinite w.left := IsFinite.of_comp w.left zc.hom.hom.left
  have : IsFinite ZC.X.hom := hZCfin
  refine ⟨Z, z, ⟨hzc, hzr⟩, ?_⟩
  rw [← Over.w w]
  infer_instance

/-- The source of a central isogeny onto a semisimple group is semisimple as soon as it is
smooth and connected. Affineness follows from finiteness of the isogeny; the geometric
unipotent radical is trivial by the algebraically closed reflection lemma applied to the
base-changed isogeny; the full centre is finite by `hasFiniteCenter_of_isCentralIsogeny`. -/
theorem IsSemisimple.of_isCentralIsogeny {D C : GroupScheme (Spec (CommRingCat.of k))}
    (p : D ⟶ C) (hp : IsCentralIsogeny p) (hC : IsSemisimple C)
    (hDs : Smooth D.X.hom) (hDc : ConnectedSpace D.X.left) : IsSemisimple D := by
  have hCr := hC.isConnectedReductive
  have := hCr.smooth
  have := hCr.isAffineHom
  have := hp.isFinite
  have hDa : IsAffineHom D.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  refine ⟨⟨hDs, hDa, hDc, ?_⟩, hasFiniteCenter_of_isCentralIsogeny p hp hC.hasFiniteCenter⟩
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  have hpK := hp.baseChange e
  have : Smooth (B.obj C).X.hom := MorphismProperty.pullback_snd C.X.hom e inferInstance
  have : IsAffineHom (B.obj C).X.hom :=
    MorphismProperty.pullback_snd C.X.hom e inferInstance
  have : IsAffineHom (B.obj D).X.hom :=
    MorphismProperty.pullback_snd D.X.hom e hDa
  have : Flat (B.map p).hom.hom.left := hpK.flat
  have : Surjective (B.map p).hom.hom.left := hpK.surjective
  have : Epi (B.map p).hom.hom.left := Flat.epi_of_flat_of_surjective _
  have : IsFinite (kernel (B.map p)).X.hom := hpK.kernel_isFinite
  exact HasTrivialUnipotentRadical.of_epi_of_finite_kernel_algClosed (B.map p)
    hCr.hasTrivialGeometricUnipotentRadical

end Field

end Langlands.GroupScheme
