import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescent
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover

/-! # Standard rational refinement transfer

The analytic standard-cover descent input is explicit in this formal adapter.
-/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Universal descent for standard rational covers supplies the local
separation needed to transfer gluing along any standard rational refinement. -/
theorem existsUnique_whole_gluing_of_standard_refinement
    (hstd : ∀ (Q : PresentedStrictAffinoidAlgebra K) (n : ℕ)
      (f : Fin n → Q) (hf : ∀ x : BanachSpectrum Q, ∃ j, x (f j) ≠ 0)
      (t : ∀ j, (standardRational f hf j).algebra),
      (∀ j l, (interLeft (standardRational f hf j) (standardRational f hf l)).restriction
        (t j) =
        (interRight (standardRational f hf j) (standardRational f hf l)).restriction
          (t l)) →
      ∃! a : Q, ∀ j, (standardRational f hf j).baseMap a = t j)
    {I : Type v} (D : I → RationalData K P) {n : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0)
    (k : Fin n → I) (inc : ∀ j, standardRational f hf j ⟶ D (k j))
    (s : ∀ i, (D i).algebra)
    (hs : ∀ i l, (interLeft (D i) (D l)).restriction (s i) =
      (interRight (D i) (D l)).restriction (s l)) :
    ∃! a : P, ∀ i, (D i).baseMap a = s i := by
  apply ScalarCoverDescent.of_refinement D (standardRational f hf) k inc
    (hstd P n f hf) ?_ s hs
  intro i
  exact ScalarCoverDescent.separated
    (hstd (D i).algebra n (fun j => (D i).baseMap (f j))
      (tuple_no_common_zero_pullback f hf (D i).baseMap))

end Langlands.Analytic.StrictTestDomain
