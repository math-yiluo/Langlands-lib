import Langlands.LinearAlgebra.WeightGradedEndomorphisms
import Langlands.LinearAlgebra.GramDualForm

/-! # Freudenthal's recursion for a weight-graded Lie algebra of endomorphisms

This module states an abstract, purely linear-algebraic form of Freudenthal's multiplicity
formula. The data are a finite-dimensional space `U` over a field of characteristic zero,
graded by a lattice `X` of characters, a pairing of `X` with a lattice `Y` of cocharacters
having a basis, and a Lie algebra `g` of endomorphisms of `U` graded by the weight shift, with
a torus part given by the cocharacters and one-dimensional root parts. The conclusion is
Freudenthal's identity for a `g`-irreducible subspace `V` with a highest weight `lam`, for the
form `GramDual.form` attached to the weight multiplicities of `U`. -/

universe u₁ u₂ u₃ u₄ u₅ u₆

open Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.LinearAlgebra

/-- Abstract Freudenthal recursion. Hypotheses, for `W μ` the weight-`μ` space of `U`:
* the `W μ` are independent and span `U`; `X` is torsion free;
* `g` is spanned by its homogeneous parts `g ⊓ shift W χ`;
* every cocharacter `y` gives an element of `g` acting by `⟨μ, y⟩` on `W μ`;
* the degree-zero part of `g` is spanned by such elements;
* a nonzero degree outside the roots has zero part, and every root part is a line;
* every nonzero cocharacter pairs nontrivially with some weight of `U`;
* the roots are nonzero, pairwise distinct and closed under negation;
* `g` has no nonzero ideal consisting of nilpotent endomorphisms;
* `V` is `g`-stable and `g`-irreducible, `V ⊓ W lam` is a line, and `V ⊓ W (lam + α) = 0`
  for the roots `α` selected by `pos`, `V ⊓ W (lam - α) = 0` for the others.
Conclusion: writing `F = GramDual.form P yb m` with `m ν = dim W ν`, and `n μ = dim (V ⊓ W μ)`,
`(F(lam, lam) + Σ_{pos α} F(lam, α) - F(μ, μ)) n(μ) = Σ_α Σ_{j ≥ 0} F(μ + (j+1) α, α) n(μ + (j+1) α)`
for every `μ`. -/
def FreudenthalCasimirCoreStatement : Prop :=
  ∀ (k : Type u₁) [Field k] [CharZero k]
    (U : Type u₂) [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (X : Type u₃) [AddCommGroup X] [IsAddTorsionFree X]
    (Y : Type u₄) [AddCommGroup Y]
    (ι : Type u₅) [Fintype ι] [DecidableEq ι]
    (J : Type u₆) [Finite J]
    (P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (yb : Basis ι ℤ Y)
    (W : X → Submodule k U) (g : LieSubalgebra k (Module.End k U))
    (root : J → X) (V : Submodule k U) (lam : X) (pos : J → Prop),
    iSupIndep W →
    (⨆ μ, W μ) = ⊤ →
    g.toSubmodule ≤ ⨆ χ, g.toSubmodule ⊓ WeightGraded.shift W χ →
    (∀ y : Y, ∃ x ∈ g, WeightGraded.IsScalarOn W (fun μ => ((P μ y : ℤ) : k)) x) →
    g.toSubmodule ⊓ WeightGraded.shift W 0 ≤
      Submodule.span k {x | ∃ y : Y, WeightGraded.IsScalarOn W (fun μ => ((P μ y : ℤ) : k)) x} →
    (∀ χ : X, χ ≠ 0 → χ ∉ Set.range root → g.toSubmodule ⊓ WeightGraded.shift W χ = ⊥) →
    (∀ j : J, finrank k ↥(g.toSubmodule ⊓ WeightGraded.shift W (root j)) = 1) →
    (∀ y : Y, y ≠ 0 → ∃ μ : X, W μ ≠ ⊥ ∧ P μ y ≠ 0) →
    (∀ j : J, root j ≠ 0) →
    Function.Injective root →
    (∀ j : J, ∃ j' : J, root j' = -root j) →
    (∀ I : LieIdeal k g, (∀ x ∈ I, IsNilpotent ((x : g) : Module.End k U)) → I = ⊥) →
    (∀ x ∈ g, ∀ v ∈ V, x v ∈ V) →
    (∀ K : Submodule k U, K ≤ V → (∀ x ∈ g, ∀ v ∈ K, x v ∈ K) → K ≠ ⊥ → K = V) →
    finrank k ↥(V ⊓ W lam) = 1 →
    (∀ j : J, pos j → V ⊓ W (lam + root j) = ⊥) →
    (∀ j : J, ¬pos j → V ⊓ W (lam - root j) = ⊥) →
    ∀ μ : X,
      (GramDual.form P yb (fun ν => finrank k ↥(W ν)) lam lam +
          (∑ᶠ (j : J) (_ : pos j), GramDual.form P yb (fun ν => finrank k ↥(W ν)) lam (root j)) -
          GramDual.form P yb (fun ν => finrank k ↥(W ν)) μ μ) *
          (finrank k ↥(V ⊓ W μ) : ℚ) =
        ∑ᶠ (j : J) (i : ℕ),
          GramDual.form P yb (fun ν => finrank k ↥(W ν)) (μ + (i + 1) • root j) (root j) *
            (finrank k ↥(V ⊓ W (μ + (i + 1) • root j)) : ℚ)

end Langlands.LinearAlgebra
