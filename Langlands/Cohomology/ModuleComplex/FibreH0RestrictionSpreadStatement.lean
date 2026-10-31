import Langlands.Cohomology.PerfectModuleComplex

/-! # Spreading out a degree-zero restriction isomorphism from a fibre -/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

/-- Two chain maps out of a bounded finite projective complex, whose targets
have universal degree-zero cohomology equal to the base ring. If, after scalar
extension to a field, the first map is bijective on degree-zero cohomology and
the two maps jointly detect degree-one cohomology, then after inverting an
element that is nonzero in the field the first map is bijective on degree-zero
cohomology after every scalar extension. -/
def FibreH0RestrictionSpreadStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (K K₁ K₂ : CochainComplex (ModuleCat.{u} R) ℤ),
    IsStrictlyPerfect K → IsStrictlyPerfect K₁ → IsStrictlyPerfect K₂ →
    ∀ (ψ₁ : K ⟶ K₁) (ψ₂ : K ⟶ K₂) (k : Type u) [Field k] (φ₀ : R →+* k),
      (∀ i : ℤ, i < 0 → IsZero (((baseChange φ₀).obj K).homology i)) →
      (∀ i : ℤ, i < 0 → IsZero (((baseChange φ₀).obj K₁).homology i)) →
      (∀ i : ℤ, i < 0 → IsZero (((baseChange φ₀).obj K₂).homology i)) →
      (∀ (T : Type u) [CommRing T] (φ : R →+* T),
        Nonempty ((((baseChange φ).obj K₁).homology 0) ≃ₗ[T] T)) →
      (∀ (T : Type u) [CommRing T] (φ : R →+* T),
        Nonempty ((((baseChange φ).obj K₂).homology 0) ≃ₗ[T] T)) →
      Function.Bijective
        (HomologicalComplex.homologyMap ((baseChange φ₀).map ψ₁) 0).hom →
      (∀ c : ((baseChange φ₀).obj K).homology 1,
        (HomologicalComplex.homologyMap ((baseChange φ₀).map ψ₁) 1).hom c = 0 →
        (HomologicalComplex.homologyMap ((baseChange φ₀).map ψ₂) 1).hom c = 0 →
        c = 0) →
      ∃ r : R, φ₀ r ≠ 0 ∧
        ∀ (T : Type u) [CommRing T] (φ : R →+* T), IsUnit (φ r) →
          Function.Bijective
            (HomologicalComplex.homologyMap ((baseChange φ).map ψ₁) 0).hom

end Langlands.Cohomology.ModuleComplex
