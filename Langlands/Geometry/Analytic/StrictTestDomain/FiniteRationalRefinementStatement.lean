import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover

/-! # Standard rational refinement of finite rational point covers -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- If finitely many rational loci cover the Banach spectrum, then one finite
standard rational cover refines them: each standard locus lies in some given
rational locus. This is a proposition to be proved separately. -/
def FiniteRationalRefinementStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K)
    (I : Type u) [Finite I] (D : I → RationalData K P),
    (∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) →
    ∃ (n : ℕ) (f : Fin n → P) (h : ∀ x : BanachSpectrum P, ∃ k, x (f k) ≠ 0),
      ∀ j : Fin n, ∃ i : I, (standardRational f h j).locus ⊆ (D i).locus

end Langlands.Analytic.StrictTestDomain
