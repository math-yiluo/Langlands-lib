import Langlands.GroupScheme.Rational.UnipotentCompactProP

/-! # Compact pro-p subgroups in closed unipotent images -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme

section Embedding

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
  {Δ : Type v} [Group Δ] [TopologicalSpace Δ]

/-- A subgroup contained in an embedded homomorphism's range is canonically
homeomorphic, as a group, to its inverse image. -/
def subgroupComapHomeomorphOfEmbedding
    (f : Γ →* Δ) (hf : IsEmbedding f)
    (K : Subgroup Δ) (hK : K ≤ f.range) : K.comap f ≃ₜ* K := by
  let q : K.comap f →* K :=
    (f.comp (K.comap f).subtype).codRestrict K fun x => x.property
  have hq : Function.Bijective q := by
    constructor
    · intro x y h
      exact Subtype.ext (hf.injective (congrArg Subtype.val h))
    · intro y
      obtain ⟨x, hx⟩ := hK y.property
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      change f x ∈ K
      exact hx.symm ▸ y.property
  let e := MulEquiv.ofBijective q hq
  have he : IsEmbedding e :=
    (hf.comp IsEmbedding.subtypeVal).codRestrict (K : Set Δ) _
  let h := e.toEquiv.toHomeomorphOfIsInducing he.isInducing
  exact
    { toMulEquiv := e
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- The compact pro-p subgroup property passes through a closed embedding,
without changing the topology on the ambient subgroup. -/
theorem isProPSubgroup_of_isCompact_le_range
    {p : ℕ} (f : Γ →* Δ) (hf : IsClosedEmbedding f)
    (hΓ : ∀ L : Subgroup Γ, IsCompact (L : Set Γ) → IsProPSubgroup p L)
    (K : Subgroup Δ) (hK : IsCompact (K : Set Δ)) (hKr : K ≤ f.range) :
    IsProPSubgroup p K := by
  have hL : IsCompact (K.comap f : Set Γ) := hf.isCompact_preimage hK
  exact (hΓ (K.comap f) hL).of_continuousMulEquiv
    (subgroupComapHomeomorphOfEmbedding f hf.isEmbedding K hKr)

end Embedding

section Unipotent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Every compact ambient subgroup contained in the actual rational-point
image of a closed unipotent group of finite type is pro-p. -/
theorem isProPSubgroup_of_isCompact_le_range_of_isUnipotent
    {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [LocallyOfFiniteType U.X.hom] (j : U ⟶ G) (hj : IsClosedSubgroup j)
    (hU : IsUnipotent U) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ K : Subgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
      K ≤ (rationalPoints.map j).range → IsProPSubgroup (ringChar 𝓀[F]) K := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffine U.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
  exact isProPSubgroup_of_isCompact_le_range (rationalPoints.map j)
    (isClosedEmbedding_rationalPointMap F j.hom.hom)
    (isProPSubgroup_of_isCompact_isUnipotent U hU)

end Unipotent

end Langlands.GroupScheme
