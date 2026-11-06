import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.Global.AdelicLeviFiniteVolume

/-! # Norm-one inclusion of actual adelic subgroups with compact rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicSubgroupPoints

open AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : Langlands.GroupScheme.SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)]

local instance : LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

/-- Compactness of the actual principal-image quotient forces every ambient character norm
on the evaluated subgroup to be trivial. -/
theorem adelicPoints_le_normOneSubgroup :
    adelicPoints F G U ≤ normOneSubgroup F G := by
  obtain ⟨K, hK, hcover⟩ :=
    LeftCosetSpace.exists_isCompact_cover (rationalSubgroup F G U)
  intro x hx
  refine (mem_normOneSubgroup F G x).mpr fun χ => ?_
  let φ : adelicPoints F G U →ₜ* ℝ≥0ˣ :=
    { toMonoidHom := (characterNorm F G χ).toMonoidHom.comp (adelicPoints F G U).subtype
      continuous_toFun := (characterNorm F G χ).continuous.comp continuous_subtype_val }
  have hrange : (φ.toMonoidHom.range : Set ℝ≥0ˣ) = φ '' K := by
    apply Subset.antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨γ, ⟨q, rfl⟩, hγ⟩ := hcover y
      refine ⟨_, hγ, ?_⟩
      change φ (rational F G U q * y) = φ y
      simp only [map_mul]
      have hr : φ (rational F G U q) = 1 :=
        characterNorm_rational F G χ q.val
      rw [hr, one_mul]
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
  have hc : IsCompact (φ.toMonoidHom.range : Set ℝ≥0ˣ) :=
    hrange ▸ hK.image φ.continuous
  exact continuousMonoidHom_eq_one_on_compactSubgroup
    (ContinuousMonoidHom.id ℝ≥0ˣ) _ hc ⟨⟨x, hx⟩, rfl⟩

/-- The actual subgroup inclusion, with its codomain restricted to the ambient norm-one
adelic group by compactness of the rational quotient. -/
def normOneInclusion : adelicPoints F G U →ₜ* normOneSubgroup F G where
  toMonoidHom := (adelicPoints F G U).subtype.codRestrict _
    (fun n => adelicPoints_le_normOneSubgroup F G U n.property)
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem normOneInclusion_val (n : adelicPoints F G U) :
    (normOneInclusion F G U n : AdelicGroupPoints F G) = n.val := rfl

@[simp]
theorem normOneInclusion_rational (q : rationalPoints F G U) :
    normOneInclusion F G U (rational F G U q) = rationalNormOne F G q.val := rfl

/-- The actual principal subgroup maps into the actual ambient principal norm-one subgroup. -/
theorem normOneInclusion_rational_mem (n : rationalSubgroup F G U) :
    normOneInclusion F G U n.val ∈ rationalNormOneSubgroup F G := by
  obtain ⟨q, hq⟩ := n.property
  rw [← hq, normOneInclusion_rational]
  exact ⟨q.val, rfl⟩

end Langlands.Global.AdelicSubgroupPoints
