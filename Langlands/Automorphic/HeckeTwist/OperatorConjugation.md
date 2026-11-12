# Conjugation of the automorphic operator algebra by any Hecke multiplier

Author: Worker 5136.

This internal module conjugates the Library's concrete automorphic operator
algebra `automorphicOperatorAlgebra F n` by multiplication with `χ ∘ det`, for an
arbitrary Hecke character `χ` (no finite-order hypothesis). Write `M_χ` for the
multiplier `FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ` (module
`Langlands.Automorphic.HeckeTwist.SmoothMultiplier`).

- `finiteSmoothHeckeDeterminantConjugation n χ` is the algebra automorphism
  `A ↦ M_χ⁻¹ A M_χ` of the endomorphisms of the finite-smooth functions
  (`FiniteSmoothEnd F n`).
- `finiteSmoothHeckeDeterminantConjugation_finite` and `_compact`: right
  translation by a finite adelic element `d`, or by an element `k` of the
  standard maximal compact subgroup at infinity, is sent to itself scaled by
  `χ(det d)`, respectively `χ(det k)`
  (`FiniteSmoothRationalFunctions.heckeDeterminantMultiplier_rightAction`).
- `finiteSmoothHeckeDeterminantConjugation_differential`: the differential
  operator of an enveloping element `a` is sent to the differential operator of
  `heckeEnvelopingShift n χ a`, the shift automorphism of module
  `Langlands.Automorphic.HeckeTwist.DifferentialMultiplier`. This is
  `finiteSmoothEnvelopingAction_heckeDeterminantMultiplier` from that module.
- Because the three kinds of generators go into the algebra, the conjugation
  maps `automorphicOperatorAlgebra F n` into itself (private lemma, by
  `Algebra.adjoin_induction`). Conjugation by `χ⁻¹` is its inverse, because
  `M_{χ⁻¹} = M_χ⁻¹`.
- `heckeDeterminantOperatorConjugation n χ` is the resulting algebra
  automorphism of `automorphicOperatorAlgebra F n`. The lemmas `_val`, `_finite`,
  `_compact`, `_differential` and `_inv` restate the facts above for it.
- `operatorAction_heckeDeterminantMultiplier`: for every operator `a` in the
  algebra, `a (M_χ f) = M_χ ((heckeDeterminantOperatorConjugation n χ a) f)`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.DeterminantOperatorConjugation` with the finite-order
hypothesis removed. Only the differential case changes. For finite order, the
conjugation fixes every differential operator. For a general character it sends
`D(a)` to `D(θ a)` with `θ = heckeEnvelopingShift n χ`. No correspondence with
a particular passage of the literature is claimed.
