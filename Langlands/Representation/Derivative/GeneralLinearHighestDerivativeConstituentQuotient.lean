import Langlands.Representation.Derivative.HighestDerivativeConstituentQuotient
import Langlands.Representation.Classification.MirabolicDerivativeContragredient

/-! # Actual general-linear highest-derivative constituents and dual quotients -/

noncomputable section

namespace Langlands.Derivative

open CategoryTheory GeneralLinear
open Classification.MirabolicDerivativeContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Choose an actual simple subrepresentation of a finite-length highest
general-linear derivative and an actual quotient of the same-order derivative
of a supplied modulus-twisted dual onto its smooth contragredient. -/
def chooseGeneralLinearHighestDerivativeConstituentQuotient
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (N + 1)
    letI := T.generalLinearTopologicalGroup (N + 1 - k)
    ∀ (A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier)),
      B.representation.Equiv
        (twist (T.determinantPowerCharacter (N + 1) 1)
          (smoothContragredient A.representation)) →
      Nontrivial ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A) →
      ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A).HasFiniteLength →
      (∀ (j : ℕ) (hj : j ≤ N + 1), k < j →
        Subsingleton ((generalLinearDerivative T ψ (N + 1) j hj).obj A)) →
      InvariantBilinear.ConstituentDualQuotientData
        ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A)
        ((generalLinearDerivative T ψ (N + 1) k hk.2).obj B) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (N + 1)
  letI := T.generalLinearTopologicalGroup (N + 1 - k)
  intro A B e hA hfinite hhigh
  let RA := (generalLinearRestriction T N).obj A
  let RB := (generalLinearRestriction T N).obj B
  let pairing := exists_determinant_pairing A B e RA (𝟙 RA)
    (by intro x y h; exact h)
  let β := Classical.choose pairing
  have hβ := Classical.choose_spec pairing
  have hA' : Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj RA) := by
    rwa [mirabolicDerivativeOfOrder_restriction ψ N k hk A]
  have hfinite' :
      ((mirabolicDerivativeOfOrder T ψ N k hk).obj RA).HasFiniteLength := by
    rwa [mirabolicDerivativeOfOrder_restriction ψ N k hk A]
  have hhigh' : ∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
      Subsingleton ((mirabolicDerivativeOfOrder T ψ N j hj).obj RA) := by
    intro j hj hkj
    rw [mirabolicDerivativeOfOrder_restriction ψ N j hj A]
    exact hhigh j hj.2 hkj
  have q := Mirabolic.chooseHighestDerivativeConstituentQuotient T ψ N k hk
    RA RB hA' hfinite' hhigh' β hβ
  rwa [mirabolicDerivativeOfOrder_restriction ψ N k hk A,
    mirabolicDerivativeOfOrder_restriction ψ N k hk B] at q

end Langlands.Derivative
