import Langlands.Representation.Classification.HeadQuotientCriterionStatement
import Langlands.Representation.Classification.Cosocle

/-!
# The two-irreducible-quotient criterion for a strong head

Distinct maximal kernels give a surjection onto the actual product. Projection
kernels then characterize a kernel-unique irreducible head, retaining the
obstruction from two copies of the same irreducible representation.
-/

namespace Langlands.Classification

universe uG uV

/-- Irreducible quotient maps with unequal kernels jointly surject. -/
theorem unequalIrreducibleQuotientKernels :
    UnequalIrreducibleQuotientKernelsStatement.{uG, uV} := by
  intro G _ V W₁ W₂ _ _ _ _ _ _ ρ π₁ π₂ hπ₁ hπ₂ q₁ q₂ hq₁ hq₂ hne
  have hne' : q₁.ker ≠ q₂.ker := fun h =>
    hne (congrArg Subrepresentation.toSubmodule h)
  have hsup := ((isIrreducible_iff_isCoatom_ker q₁ hq₁).mp hπ₁).sup_eq_top_of_ne
    ((isIrreducible_iff_isCoatom_ker q₂ hq₂).mp hπ₂) hne'
  have hsum : LinearMap.ker q₁.toLinearMap ⊔ LinearMap.ker q₂.toLinearMap = ⊤ :=
    congrArg Subrepresentation.toSubmodule hsup
  rintro ⟨w₁, w₂⟩
  obtain ⟨x, hx⟩ := hq₁ w₁
  obtain ⟨z, hz⟩ := hq₂ (w₂ - q₂ x)
  have hzmem : z ∈ LinearMap.ker q₁.toLinearMap ⊔ LinearMap.ker q₂.toLinearMap := by
    rw [hsum]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzmem
  change q₁ a = 0 at ha
  change q₂ b = 0 at hb
  rw [← hab, map_add, hb, add_zero] at hz
  refine ⟨x + a, Prod.ext ?_ ?_⟩
  · change q₁ (x + a) = w₁
    rw [map_add, hx, ha, add_zero]
  · change q₂ (x + a) = w₂
    rw [map_add, hz]
    abel

/-- A strong irreducible head exists precisely when an irreducible quotient
exists and no quotient is a product of two irreducibles. -/
theorem irreducibleHeadProductCriterion :
    IrreducibleHeadProductCriterionStatement.{uG, uV} := by
  intro G _ V _ _ ρ
  constructor
  · rintro ⟨W, _, _, π, hπ, q₀, hq₀, huniq⟩
    refine ⟨⟨W, inferInstance, inferInstance, π, hπ, q₀, hq₀⟩, ?_⟩
    intro W₁ W₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂ q hq
    let q₁ := (Representation.IntertwiningMap.fst ℂ π₁ π₂).comp q
    let q₂ := (Representation.IntertwiningMap.snd ℂ π₁ π₂).comp q
    have hq₁ : Function.Surjective q₁ := by
      intro w
      obtain ⟨v, hv⟩ := hq (w, 0)
      exact ⟨v, congrArg Prod.fst hv⟩
    have hq₂ : Function.Surjective q₂ := by
      intro w
      obtain ⟨v, hv⟩ := hq (0, w)
      exact ⟨v, congrArg Prod.snd hv⟩
    have hker : LinearMap.ker q₁.toLinearMap = LinearMap.ker q₂.toLinearMap :=
      (huniq W₁ π₁ hπ₁ q₁ hq₁).trans (huniq W₂ π₂ hπ₂ q₂ hq₂).symm
    let : Representation.IsIrreducible π₁ := hπ₁
    have : Nontrivial W₁ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π₁.asModule
    obtain ⟨w, hw⟩ := exists_ne (0 : W₁)
    obtain ⟨v, hv⟩ := hq (w, 0)
    have hv₂ : v ∈ LinearMap.ker q₂.toLinearMap := by
      change (q v).2 = 0
      rw [hv]
    have hv₁ : v ∈ LinearMap.ker q₁.toLinearMap := by
      rw [hker]
      exact hv₂
    apply hw
    change (q v).1 = 0 at hv₁
    simpa only [hv] using hv₁
  · rintro ⟨⟨W, _, _, π, hπ, q, hq⟩, hno⟩
    refine ⟨W, inferInstance, inferInstance, π, hπ, q, hq, ?_⟩
    intro W' _ _ π' hπ' q' hq'
    by_contra hne
    exact hno W' W π' π hπ' hπ (q'.prod q)
      (unequalIrreducibleQuotientKernels G V W' W ρ π' π hπ' hπ q' q hq' hq hne)

/-- The exact published aggregate, at independent group and carrier universes. -/
theorem headQuotientCriterion : HeadQuotientCriterionStatement.{uG, uV} :=
  ⟨unequalIrreducibleQuotientKernels, irreducibleHeadProductCriterion⟩

end Langlands.Classification
