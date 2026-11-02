import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.SetTheory.Cardinal.Finite

/-! # A Bezout count for a section against a linear system with finite base locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- On an integral proper scheme of dimension at most `e` over an infinite field,
let `s` be a section of `L ^ p` that is not identically zero and let `S` be a set of
sections of `L ^ q` whose actual base locus (the points where every member of `S`
vanishes) is finite. If every base-locus point on the zero locus of `s` has a
local ring of dimension `e`, then the number of such points is at most
`e! * p * q ^ (e - 1)` times the degree-`e` coefficient of the actual Euler
polynomial of `L`. -/
def LinearSystemBaseLocusBezoutStatement : Prop :=
  ∀ (K : Type u) [Field K] [Infinite K] (X : Scheme.{u}) [IsIntegral X]
    [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (e : ℕ), 0 < e → topologicalKrullDim X ≤ e →
    ∀ (L : LineBundle X) (p q : ℕ) (s : L.powSections p) (S : Set (L.powSections q)),
      (L.sectionOpen s : Set X).Nonempty →
      {x : X | ∀ t ∈ S, x ∉ L.sectionOpen t}.Finite →
      (∀ x : X, (∀ t ∈ S, x ∉ L.sectionOpen t) → x ∉ L.sectionOpen s →
        ringKrullDim (X.presheaf.stalk x) = e) →
      (Nat.card {x : X // (∀ t ∈ S, x ∉ L.sectionOpen t) ∧ x ∉ L.sectionOpen s} : ℚ) ≤
        (e.factorial : ℚ) * (p : ℚ) * (q : ℚ) ^ (e - 1) *
          (lineBundleEulerPolynomial f L e).coeff e

end Langlands.AlgebraicGeometry.Picard
