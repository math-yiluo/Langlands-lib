import Langlands.GroupScheme.Rational.FundamentalRepresentations

/-! # Freudenthal's multiplicity formula for a split reductive group in characteristic zero -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Freudenthal's multiplicity formula (Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §22.3; Jantzen, *Representations of Algebraic Groups*, II.5.11 for
the Weyl-module consequence), for a split pinning of a group scheme over a field of
characteristic zero. For every representation `r` with `p.IsHighestWeight r lam` there is a
symmetric, Weyl-invariant, positive definite `ℚ`-valued bilinear form `F` on the character
lattice `X` such that, for every `μ : X`, writing `m ν = dim r_ν`,
`(F(lam, lam) + Σ_{α > 0} F(lam, α) - F(μ, μ)) * m μ
  = Σ_{α root} Σ_{j ≥ 1} F(μ + j α, α) * m(μ + j α)`.
Since `Σ_{α > 0} α = 2ρ`, the left coefficient is `‖lam + ρ‖² - ‖μ + ρ‖² + 2 F(μ, ρ)`, and the
right side, after pairing the terms of `α` and `-α`, is Freudenthal's
`2 Σ_{α > 0} Σ_{j ≥ 1} F(μ + j α, α) m(μ + j α)` plus `2 F(μ, ρ) m(μ)` (see the Markdown). -/
def FreudenthalMultiplicityStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (n : ℕ) (r : MatrixRepresentation G (Fin n))
    (lam : characterLattice p.torus),
    p.IsHighestWeight r lam →
    ∃ F : characterLattice p.torus →ₗ[ℤ] characterLattice p.torus →ₗ[ℤ] ℚ,
      (∀ x y : characterLattice p.torus, F x y = F y x) ∧
      (∀ (i : p.rootIndex) (x y : characterLattice p.torus),
        F (p.rootDatum.reflection i x) (p.rootDatum.reflection i y) = F x y) ∧
      (∀ x : characterLattice p.torus, x ≠ 0 → 0 < F x x) ∧
      ∀ μ : characterLattice p.torus,
        (F lam lam + (∑ᶠ (i : p.rootIndex) (_ : p.rootDatum.root i ∈ p.positiveRootMonoid),
            F lam (p.rootDatum.root i)) - F μ μ) *
            (Module.finrank k (p.representationWeightSpace r μ) : ℚ) =
          ∑ᶠ (i : p.rootIndex) (j : ℕ),
            F (μ + (j + 1) • p.rootDatum.root i) (p.rootDatum.root i) *
              (Module.finrank k
                (p.representationWeightSpace r (μ + (j + 1) • p.rootDatum.root i)) : ℚ)

end Langlands.GroupScheme
