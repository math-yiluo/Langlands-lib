import Langlands.ClassFieldTheory.Local.FiniteComparison

/-! # Relative invariants obtained by composing with actual closure inflation -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K]
  (E : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K E] [Normal K E]
  (invK : absoluteCohomology K 2 ≃+ RationalModIntegers)

/-- Restrict a supplied absolute invariant along the actual closure inflation. -/
def relativeInvariantFromAbsolute :
    relativeCohomology K E 2 →+ RationalModIntegers :=
  invK.toAddMonoidHom.comp (closureInflation K E 2)

@[simp]
theorem relativeInvariantFromAbsolute_apply (x : relativeCohomology K E 2) :
    relativeInvariantFromAbsolute K E invK x = invK (closureInflation K E 2 x) := rfl

/-- Injectivity follows from that of the actual inflation. -/
theorem relativeInvariantFromAbsolute_injective
    (hInflation : Function.Injective (closureInflation K E 2)) :
    Function.Injective (relativeInvariantFromAbsolute K E invK) :=
  invK.injective.comp hInflation

variable [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

/-- Inflation exactness and the degree law identify the actual relative image. -/
theorem relativeInvariantFromAbsolute_range
    (invE : absoluteCohomology E 2 ≃+ RationalModIntegers)
    (hExact : (closureInflation K E 2).range =
      (absoluteRestriction K E 2).hom.toAddMonoidHom.ker)
    (hDegree : ∀ x : absoluteCohomology K 2,
      invE (absoluteRestriction K E 2 x) = Module.finrank K E • invK x) :
    (relativeInvariantFromAbsolute K E invK).range =
      denominatorSubgroup (Module.finrank K E) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change Module.finrank K E • invK (closureInflation K E 2 x) = 0
    rw [← hDegree]
    have hx : closureInflation K E 2 x ∈ (closureInflation K E 2).range := ⟨x, rfl⟩
    rw [hExact] at hx
    change absoluteRestriction K E 2 (closureInflation K E 2 x) = 0 at hx
    rw [hx, map_zero]
  · intro hq
    change Module.finrank K E • q = 0 at hq
    have hx : invK.symm q ∈ (closureInflation K E 2).range := by
      rw [hExact]
      change absoluteRestriction K E 2 (invK.symm q) = 0
      apply invE.injective
      rw [map_zero, hDegree, invK.apply_symm_apply, hq]
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, ?_⟩
    change invK (closureInflation K E 2 x) = q
    rw [hx, invK.apply_symm_apply]

end Langlands.ClassFieldTheory.Local
