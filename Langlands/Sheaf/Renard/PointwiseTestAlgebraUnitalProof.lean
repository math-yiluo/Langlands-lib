import Langlands.Sheaf.Renard.CompactOpenSheafCharacterizationStatements

/-! # The pointwise test algebra is unital exactly on compact t.d. spaces -/

set_option autoImplicit false

noncomputable section

open TopologicalSpace

namespace Langlands.Sheaf.Renard

universe u

open HarmonicAnalysis.PointwiseTestAlgebra

/-- Renard II.2.4, Example: a unit is forced to be the constant function one. -/
theorem pointwiseTestAlgebraUnitalIffCompact :
    PointwiseTestAlgebraUnitalIffCompactStatement.{u} := by
  intro X _ hX
  let : T2Space X := hX.1
  constructor
  · rintro ⟨e, he⟩
    have heone : ∀ x : X, e x = 1 := by
      intro x
      obtain ⟨U, hx, ho, hc, _⟩ := hX.2 x Set.univ (Filter.univ_mem)
      let hcl : IsClopen U := ⟨hc.isClosed, ho⟩
      have hxone := congrArg (fun f : Carrier X => f x) (he (characteristic hcl hc)).1
      change e x * characteristic hcl hc x = characteristic hcl hc x at hxone
      simpa only [mul_apply, characteristic_apply, Set.indicator_of_mem hx,
        mul_one] using hxone
    have hs : Function.support (e : X → ℂ) = Set.univ := by
      ext x
      simp [Function.mem_support, heone x]
    exact ⟨by simpa only [hs] using isCompact_support e⟩
  · intro hcompact
    let := hcompact
    refine ⟨characteristic isClopen_univ isCompact_univ, ?_⟩
    intro f
    constructor <;> apply ext <;> intro x <;>
      simp only [mul_apply, characteristic_apply, Set.indicator_of_mem (Set.mem_univ x),
        one_mul, mul_one]

end Langlands.Sheaf.Renard
