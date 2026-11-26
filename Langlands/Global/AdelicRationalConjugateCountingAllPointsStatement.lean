import Langlands.Global.AdelicRationalConjugateCounting

/-! # Counting rational points in adelic conjugates of compact sets, at every adelic point

`AdelicRationalConjugateCountingAllPointsStatement` is Mœglin–Waldspurger I.2.4, Lemma (a)(i),
for `y = x`: the number of rational points in `x C x⁻¹` is bounded by a fixed power of the height
of `x`, for every `x ∈ G(𝔸)`. The Library's `AdelicRationalConjugateCountingStatement` is the
same bound for the points `x` whose finite component lies in a given compact set. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

/-- Counting rational points in adelic conjugates of compact sets at every adelic point
(Mœglin–Waldspurger I.2.4, Lemma (a)(i), with `y = x`). Fix an affine group `G` over a number
field `F` and a closed matrix embedding `rho` of positive size. There is `d` such that for every
compact `C ⊆ G(𝔸)` there is `B ≥ 0` with the following property: for every `x ∈ G(𝔸)`, the set
`G(F) ∩ x C x⁻¹` is finite and has at most `B ‖x‖^d` elements, where `‖x‖` is the height
`RepresentationGrowth.adelicHeight F G rho x`. The finite component of `x` is not restricted. -/
def AdelicRationalConjugateCountingAllPointsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (n : ℕ) (rho : GroupScheme.MatrixRepresentation G (Fin n)),
    0 < n → GroupScheme.IsClosedSubgroup rho →
    ∃ d : ℕ, ∀ (C : Set (AdelicGroupPoints F G)), IsCompact C →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : AdelicGroupPoints F G,
        let P := (AdelicGroupPoints.rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
          ((fun y => x * y * x⁻¹) '' C)
        P.Finite ∧ (P.ncard : ℝ) ≤ B * RepresentationGrowth.adelicHeight F G rho x ^ d

/-- The bound at every point implies the Library's bound for points with finite component in a
compact set. -/
theorem adelicRationalConjugateCounting_of_allPoints
    (h : AdelicRationalConjugateCountingAllPointsStatement.{u}) :
    AdelicRationalConjugateCountingStatement.{u} := by
  intro F _ _ G _ n rho hn hrho
  obtain ⟨d, hd⟩ := h F G n rho hn hrho
  exact ⟨d, fun _ _ C hC => by
    obtain ⟨B, hB, hx⟩ := hd C hC
    exact ⟨B, hB, fun x _ => hx x⟩⟩

end Langlands.Global
