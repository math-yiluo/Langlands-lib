/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Constructibility of all reductions from the first

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-thm-sfb-proper-base-change/sk-prop-integral-criterion-reductions.md,
  statement, conditions (1) and (2), and final integral-criterion assertion
  (blueprint: lemma-bounds-finite-reductions).

The integral category `D(X_proet, O_E)` is `AdicCompletion.Modules l E X`, internal
modules over the pulled-back condensed integer ring `DerivedNakayama.integerRing l E`;
`AdicCompletion.derivedReduction l E X n` is the derived reduction `K_{n+1}` modulo
`pi_E^(n+1)`. Bounded constructibility over `O_E` and over `O_E/pi_E^n` is the single
finite-constant-model predicate `constantModelBoundedConstructible` of
definition-constructible-sheaves, applied to the respective condensed rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a derived-complete integral pro-étale complex `K` on a Noetherian scheme, the
first reduction `K_1` is bounded constructible if and only if every reduction `K_n`
is bounded constructible with cohomology in one interval `[r,s]` independent of `n`
(first conjunct); and `K` itself lies in `D_bc(X, O_E)` if and only if this second
condition holds (second conjunct, the final assertion of the source).
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-thm-sfb-proper-base-change/sk-prop-integral-criterion-reductions.md,
  conditions (1), (2), and final sentence
  (blueprint: lemma-bounds-finite-reductions).

Proof (node steps 1-4).
1. (2) ⇒ (1): the case `n = 1` of (2).
2. Put `Λ_j = O_E/pi_E^j`, a finite ring (def-weil-l-adic-coefficient-extension (4)).
   By lem-pe-finite-coefficient-model-comparison, constructibility in the sense of
   definition-constructible-sheaves agrees with def-weil-proetale-constructible-sheaf, with the
   same cohomological intervals. For `n > 1`,
   lem-pe-derived-reduction-coefficient-triangle gives the distinguished triangle
   `Res K_{n-1} → K_n → Res K_1 → Res K_{n-1}[1]` in `D((Λ_n)_X)`.
3. (1) ⇒ (2): choose `[r,s]` containing the cohomology of `K_1` and induct on `n`.
   By lem-pe-finite-scalar-restriction-constructible, `Res K_{n-1}` and `Res K_1` lie
   in `D_bc(X, Λ_n)` with `H^q(Res L) = Res H^q(L)`, vanishing outside `[r,s]`;
   lem-weil-proetale-dbc-triangulated gives `K_n ∈ D_bc(X, Λ_n)`, and the long exact
   sequence (lem-sf-derived-homology-long-exact) gives `H^q(K_n) = 0` off `[r,s]`.
4. Final assertion. definition-derived-adic-completeness--1 and definition-derived-adic-completeness
use the
   same completion map. If (2) holds, then (1) holds by step 1 and
   lem-sfb-internal-integral-criterion-reverse gives `K ∈ D_bc(X, O_E)`. Conversely,
   for `K ∈ D_bc(X, O_E)` apply lem-sfb-degreewise-bounded-devissage with the property
   `Q(L)`: `L ⊗^L Λ_1 ∈ D_bc(X, Λ_1)`, which is extension-closed since derived
   extension of scalars is exact (lem-pur-derived-change-of-rings) and `D_bc(X, Λ_1)`
   is triangulated (lem-weil-proetale-dbc-triangulated); for constructible `M`,
   lem-sfb-finite-model-sheaf-quotient-constructible with `n = 1` gives `Q(M[-q])`.
   Hence (1), and (2) by steps 2-3. -/
theorem integralCriterionReductions (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : IsDerivedComplete l E X K) :
    (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ↔
      (∀ n : ℕ, constantModelBoundedConstructible
        (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧
        ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K))) ∧
    (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
      (∀ n : ℕ, constantModelBoundedConstructible
        (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧
        ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale
