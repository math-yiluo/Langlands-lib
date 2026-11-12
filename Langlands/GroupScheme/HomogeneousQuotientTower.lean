import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.GroupScheme.HomogeneousQuotientGroup
import Langlands.GroupScheme.AffineQuotientProof
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.IdentityComponent

/-! # Affineness of homogeneous quotients along a normal subgroup tower -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientTower

open HomogeneousCosetRelation
open HomogeneousQuotientFromEmbedding (HomogeneousQuotient)

section Base

variable {S : Scheme.{u}} {G H M : GroupScheme S} {i : H ⟶ G}

/-- A point of `H` connecting two points of `G` with the same image in a homogeneous quotient. -/
def cosetWitness (D : HomogeneousQuotient i) {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ D.projection = b ≫ D.projection) : T ⟶ H.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp ((D.fibers T a b).mp h))

theorem cosetWitness_spec (D : HomogeneousQuotient i) {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ D.projection = b ≫ D.projection) :
    cosetWitness D a b h ≫ i.hom.hom = a⁻¹ * b :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp ((D.fibers T a b).mp h))

/-- The right-coset arrow scheme is the kernel pair of every homogeneous quotient projection. -/
theorem isPullback_source_target [Mono i.hom.hom] (D : HomogeneousQuotient i) :
    IsPullback (source i) (target i) D.projection D.projection := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift c.fst (cosetWitness D c.fst c.snd c.condition)) ?_ ?_ ?_⟩⟩
  · apply (D.fibers _ _ _).mpr
    exact (exists_arrow_iff i _ _).mp ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  · intro c
    exact lift_source i _ _
  · intro c
    rw [lift_target, cosetWitness_spec, mul_inv_cancel_left]
  · intro c m hm₁ hm₂
    apply arrow_unique i
    · rw [hm₁, lift_source]
    · rw [hm₂, lift_target, cosetWitness_spec, mul_inv_cancel_left]

/-- Through a monomorphism `i`, membership in the range of `j ≫ i` is membership in the
range of `j`. -/
theorem mem_range_comp_iff [Mono i.hom.hom] (j : M ⟶ H) {T : Over S} (x : T ⟶ H.X) :
    x ≫ i.hom.hom ∈ (SubgroupFunctor.range (j ≫ i)).carrier T ↔
      x ∈ (SubgroupFunctor.range j).carrier T := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, (cancel_mono i.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

variable (j : M ⟶ H) (QM : HomogeneousQuotient (j ≫ i)) (QH : HomogeneousQuotient i)

local instance instHomogeneousQuotientTower1 : Smooth QM.projection.left := QM.smooth_projection
local instance instHomogeneousQuotientTower2 : Surjective QM.projection.left :=
  QM.surjective_projection
local instance instHomogeneousQuotientTower3 : QuasiCompact QM.projection.left :=
  QM.quasiCompact_projection
local instance instHomogeneousQuotientTower4 : Smooth QH.projection.left := QH.smooth_projection
local instance instHomogeneousQuotientTower5 : Surjective QH.projection.left :=
  QH.surjective_projection
local instance instHomogeneousQuotientTower6 : QuasiCompact QH.projection.left :=
  QH.quasiCompact_projection

/-- Points with the same image in `G/M` have the same image in `G/H`. -/
theorem fiber_le (T : Over S) (a b : T ⟶ G.X)
    (h : a ≫ QM.projection = b ≫ QM.projection) :
    a ≫ QH.projection = b ≫ QH.projection := by
  apply (QH.fibers T a b).mpr
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp ((QM.fibers T a b).mp h)
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ j.hom.hom, by rw [Category.assoc, ← hy,
    Grp.comp_hom_hom]⟩

/-- The induced projection `G/M ⟶ G/H`. -/
def towerMap : QM.scheme ⟶ QH.scheme :=
  HomogeneousQuotientComparison.desc QM.projection QH.projection (fiber_le j QM QH)

@[reassoc]
theorem projection_towerMap : QM.projection ≫ towerMap j QM QH = QH.projection :=
  HomogeneousQuotientComparison.fac_desc _ _ _

variable [Mono i.hom.hom]

/-- The arrow `(g, h) ↦ (q_M(g h), g)` into `G/M ×_{G/H} G`. -/
def towerArrow : arrows i ⟶ pullback (towerMap j QM QH) QH.projection :=
  pullback.lift (target i ≫ QM.projection) (source i) (by
    rw [Category.assoc, projection_towerMap]
    exact ((isPullback_source_target QH).w).symm)

@[reassoc (attr := simp)]
theorem towerArrow_fst :
    towerArrow j QM QH ≫ pullback.fst _ _ = target i ≫ QM.projection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem towerArrow_snd : towerArrow j QM QH ≫ pullback.snd _ _ = source i :=
  pullback.lift_snd _ _ _

/-- `towerArrow` is the base change of the projection `G ⟶ G/M` along
`G/M ×_{G/H} G ⟶ G/M`. -/
theorem isPullback_towerArrow :
    IsPullback (towerArrow j QM QH) (target i) (pullback.fst _ _) QM.projection := by
  refine (IsPullback.of_bot (h₁₁ := target i) (v₁₁ := towerArrow j QM QH)
    (v₁₂ := QM.projection) (h₂₁ := pullback.fst _ _) (v₂₁ := pullback.snd _ _)
    (v₂₂ := towerMap j QM QH) (h₃₁ := QH.projection) ?_ (towerArrow_fst j QM QH).symm
    (IsPullback.of_hasPullback _ _)).flip
  rw [towerArrow_snd, projection_towerMap]
  exact (isPullback_source_target QH).flip

theorem effectiveEpi_towerArrow : EffectiveEpi (towerArrow j QM QH).left := by
  have h := (isPullback_towerArrow j QM QH).map (Over.forget S)
  have : Flat (towerArrow j QM QH).left :=
    MorphismProperty.of_isPullback (P := @Flat) h.flip (inferInstance : Flat QM.projection.left)
  have : Surjective (towerArrow j QM QH).left :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip
      (inferInstance : Surjective QM.projection.left)
  have : QuasiCompact (towerArrow j QM QH).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip
      (inferInstance : QuasiCompact QM.projection.left)
  infer_instance

variable (Q' : HomogeneousQuotient j)

local instance instHomogeneousQuotientTower7 : Smooth Q'.projection.left := Q'.smooth_projection
local instance instHomogeneousQuotientTower8 : Surjective Q'.projection.left :=
  Q'.surjective_projection
local instance instHomogeneousQuotientTower9 : QuasiCompact Q'.projection.left :=
  Q'.quasiCompact_projection

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
theorem effectiveEpi_tensorHom : EffectiveEpi (𝟙 G.X ⊗ₘ Q'.projection).left := by
  have hp : fpqcProperty (𝟙 G.X ⊗ₘ Q'.projection).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w (𝟙 G.X)).symm (Over.w Q'.projection).symm
  have : QuasiCompact (𝟙 G.X ⊗ₘ Q'.projection).left := hp.1
  have : Flat (𝟙 G.X ⊗ₘ Q'.projection).left := hp.2.1
  have : Surjective (𝟙 G.X ⊗ₘ Q'.projection).left := hp.2.2
  infer_instance

theorem towerArrow_eq_iff {T : Over S} (a b : T ⟶ arrows i) :
    a ≫ towerArrow j QM QH = b ≫ towerArrow j QM QH ↔
      a ≫ (𝟙 G.X ⊗ₘ Q'.projection) = b ≫ (𝟙 G.X ⊗ₘ Q'.projection) := by
  have hs : a ≫ towerArrow j QM QH = b ≫ towerArrow j QM QH ↔
      a ≫ fst G.X H.X = b ≫ fst G.X H.X ∧
        a ≫ target i ≫ QM.projection = b ≫ target i ≫ QM.projection := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · simpa [source] using congrArg (fun c => c ≫ pullback.snd _ _) h
      · simpa using congrArg (fun c => c ≫ pullback.fst _ _) h
    · rintro ⟨h₁, h₂⟩
      apply pullback.hom_ext
      · simpa using h₂
      · simpa [source] using h₁
  have hr : a ≫ (𝟙 G.X ⊗ₘ Q'.projection) = b ≫ (𝟙 G.X ⊗ₘ Q'.projection) ↔
      a ≫ fst G.X H.X = b ≫ fst G.X H.X ∧
        (a ≫ snd G.X H.X) ≫ Q'.projection = (b ≫ snd G.X H.X) ≫ Q'.projection := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · simpa using congrArg (fun c => c ≫ fst _ _) h
      · simpa using congrArg (fun c => c ≫ snd _ _) h
    · rintro ⟨h₁, h₂⟩
      apply hom_ext
      · simpa using h₁
      · simpa using h₂
  rw [hs, hr]
  refine and_congr_right fun h₁ => ?_
  rw [Q'.fibers, ← mem_range_comp_iff (i := i) j, ← Category.assoc, ← Category.assoc, QM.fibers]
  have ha : a ≫ target i = (a ≫ fst G.X H.X) * ((a ≫ snd G.X H.X) ≫ i.hom.hom) := by
    simp [target, MonObj.comp_mul]
  have hb : b ≫ target i = (a ≫ fst G.X H.X) * ((b ≫ snd G.X H.X) ≫ i.hom.hom) := by
    rw [h₁]
    simp [target, MonObj.comp_mul]
  rw [ha, hb, mul_inv_rev, mul_assoc, inv_mul_cancel_left, MonObj.mul_comp, GrpObj.inv_comp]

/-- The fibre product `G/M ×_{G/H} G` is isomorphic to `G × H/M`. -/
def towerPullbackIso : pullback (towerMap j QM QH) QH.projection ≅ G.X ⊗ Q'.scheme :=
  haveI := effectiveEpi_towerArrow j QM QH
  haveI := effectiveEpi_tensorHom (G := G) j Q'
  HomogeneousQuotientComparison.iso (towerArrow j QM QH) (𝟙 G.X ⊗ₘ Q'.projection)
    (fun _ a b => towerArrow_eq_iff j QM QH Q' a b)

end Base

section Field

variable {k : Type u} [Field k] {G H M : GroupScheme (Spec (CommRingCat.of k))}

/-- Let `M ⊆ H ⊆ G` be closed subgroups of an affine group over a field, with `H` and `M`
smooth and `M` normal in `H`. If the homogeneous quotient `G/H` is affine, then every
homogeneous quotient `G/M` is affine. -/
theorem isAffineHom_of_normal [IsAffineHom G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hH : Smooth H.X.hom) (j : M ⟶ H) (hj : IsClosedSubgroup j) (hM : Smooth M.X.hom)
    (hn : (SubgroupFunctor.range j).IsNormal) (QH : HomogeneousQuotient i)
    (hQH : IsAffineHom QH.scheme.hom) (QM : HomogeneousQuotient (j ≫ i)) :
    IsAffineHom QM.scheme.hom := by
  have : Smooth H.X.hom := hH
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by
    have h : IsAffineHom (i.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨Q₀, q₀, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k H M j hj hM
  let Q' : HomogeneousQuotient j := ⟨Q₀, q₀, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩
  have : IsSeparated (Q'.groupScheme hn).X.hom := hsep
  have : LocallyOfFiniteType (Q'.groupScheme hn).X.hom := hft
  have : QuasiCompact (Q'.groupScheme hn).X.hom := hqc
  have : Smooth (Q'.groupProjection hn).hom.hom.left := hsm
  have : Surjective (Q'.groupProjection hn).hom.hom.left := hsurj
  have : QuasiCompact (Q'.groupProjection hn).hom.hom.left := hqqc
  have : IsAffineHom Q'.scheme.hom :=
    affineGroupSchemeQuotient k H (Q'.groupScheme hn) (Q'.groupProjection hn)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q'.scheme.left := isAffine_of_isAffineHom Q'.scheme.hom
  have : IsAffine QH.scheme.left := isAffine_of_isAffineHom QH.scheme.hom
  have : IsAffine (G.X ⊗ Q'.scheme).left := by
    change IsAffine (pullback G.X.hom Q'.scheme.hom)
    infer_instance
  let e := towerPullbackIso j QM QH Q'
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsAffine (pullback (towerMap j QM QH) QH.projection).left :=
    IsAffine.of_isIso e.hom.left
  have : Smooth QH.projection.left := QH.smooth_projection
  have : Surjective QH.projection.left := QH.surjective_projection
  have h : IsPullback (pullback.fst (towerMap j QM QH) QH.projection).left
      (pullback.snd (towerMap j QM QH) QH.projection).left (towerMap j QM QH).left
      QH.projection.left :=
    (IsPullback.of_hasPullback _ _).map (Over.forget _)
  have : IsAffine QM.scheme.left :=
    Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent.isAffine_of_isPullback h
  infer_instance

/-- If the homogeneous quotient `G/H` by a smooth closed subgroup of an affine group is
affine, then every homogeneous quotient of `G` by the identity component `H⁰` is affine. -/
theorem isAffineHom_identityComponent [IsAffineHom G.X.hom] (i : H ⟶ G)
    (hi : IsClosedSubgroup i) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (QH : HomogeneousQuotient i) (hQH : IsAffineHom QH.scheme.hom)
    (Q₀ : HomogeneousQuotient (identityComponentι H ≫ i)) :
    IsAffineHom Q₀.scheme.hom :=
  isAffineHom_of_normal i hi inferInstance (identityComponentι H)
    (IdentityComponent.isClosedSubgroup_identityComponentι H) inferInstance
    (IdentityComponent.isNormal_range_identityComponentι H) QH hQH Q₀

/-- If the homogeneous quotient `G/H` by a smooth closed subgroup of a smooth affine group is
affine, then every homogeneous quotient of `G` by a smooth closed normal subgroup `N` of the
identity component `H⁰` is affine. -/
theorem isAffineHom_of_normal_identityComponent [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (QH : HomogeneousQuotient i) (hQH : IsAffineHom QH.scheme.hom)
    {N : GroupScheme (Spec (CommRingCat.of k))} (j : N ⟶ identityComponent H)
    (hj : IsClosedSubgroup j) (hN : Smooth N.X.hom) (hn : (SubgroupFunctor.range j).IsNormal)
    (QN : HomogeneousQuotient (j ≫ identityComponentι H ≫ i)) :
    IsAffineHom QN.scheme.hom := by
  have hi₀ : IsClosedSubgroup (identityComponentι H ≫ i) := by
    have : IsClosedImmersion (identityComponentι H).hom.hom.left :=
      IdentityComponent.isClosedSubgroup_identityComponentι H
    have : IsClosedImmersion i.hom.hom.left := hi
    change IsClosedImmersion ((identityComponentι H).hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  obtain ⟨Q₀, q₀, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G (identityComponent H) (identityComponentι H ≫ i) hi₀
      inferInstance
  let Q₀' : HomogeneousQuotient (identityComponentι H ≫ i) :=
    ⟨Q₀, q₀, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩
  exact isAffineHom_of_normal (identityComponentι H ≫ i) hi₀ inferInstance j hj hN hn Q₀'
    (isAffineHom_identityComponent i hi QH hQH Q₀') QN

end Field

end Langlands.GroupScheme.HomogeneousQuotientTower
