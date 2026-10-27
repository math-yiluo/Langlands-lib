# Product-Levi dual-opposite tempered sufficiency

Author: Worker 253.

This module proves

```text
theorem Langlands.glProductLeviDualOppositeTemperedSufficiency :
    GLProductLeviDualOppositeTemperedSufficiencyStatement.{uF, uV}
```

The proposition is published in
[`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md).
The field universe `uF` and representation universe `uV` stay independent.
The theorem has no hypotheses. It says the following. Let `S` be an irreducible
admissible representation of an actual positive-rank GL block Levi
`M_C = C.Levi F.Carrier`. Suppose its block scalars act by a unitary character
`ω`, through the explicit `HasScalarCharacter` hypothesis. Suppose also that
every nonzero element of the full algebraic dual of every normalized refined
opposite Jacquet quotient, which is an eigenfunctional with an open-kernel
character `ψ` and real part `s`, has nonpositive prefix sums of `s` inside
each outer block. Then `S` is tempered modulo the full centre of `M_C`, for
every Borel Haar measure on the actual central quotient.

## Implemented proof

The proof is one application of two published theorems:

1. `glProductLeviTemperedExponentSufficiency` (module
   [`ProductLeviTemperedSufficiencyProof`](ProductLeviTemperedSufficiencyProof.md))
   proves the upper core proposition
   `GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV}`.
2. `glProductLeviDualOppositeTemperedSufficiency_of_core` (module
   [`ProductLeviDualOppositeAdapter`](ProductLeviDualOppositeAdapter.md))
   proves that the core proposition implies the dual-opposite proposition, at
   the same universes.

Applying the second theorem to the first gives the target. The final theorem
type therefore contains neither the core proposition nor any other added
hypothesis.

## Signs

All sign conventions are those of the two imported proofs; this module adds no
new sign. In the adapter the steps are as follows.

- Conjugation by the blockwise block-reversal matrix sends the upper Jacquet
  quotient of a refinement `D` to the opposite Jacquet quotient of the reversed
  refinement `D'`. The opposite normalization uses the positive upper half
  modulus. After reversal this equals the inverse half modulus that normalizes
  the upper quotient of `D`.
- The algebraic dual adds no inversion and no complex conjugation of the
  character. A generalized eigencharacter `ψ` of the upper quotient of `D`
  becomes the eigencharacter `ψ ∘ (relabelling)` of a nonzero dual
  eigenfunctional on the opposite quotient of `D'`.
- The hypothesis gives nonpositive within-block prefixes of the real part
  `s`. Unitarity of `ω` gives zero block totals. On the chamber where the
  absolute values increase inside each block of `D`, the reversed logarithms
  are antitone. Summation by parts then bounds `∑ s_b log|a_b|` by `0`, so
  `‖ψ(a)‖ ≤ 1`. That is the core hypothesis.

For `C = (2)` and `D = (1,1)`, the Steinberg representation has opposite real
part `(-1/2, 1/2)`, with prefixes `-1/2, 0`, and satisfies the hypothesis. The
trivial representation has opposite real part `(1/2, -1/2)`, with first prefix
`1/2 > 0`, and fails it. The identity refinement `(2)` has real exponent zero.
These are explanatory checks from the statement Markdown, not Lean theorems.

## Provenance

This module is an internal composition and formalizes no literature result
itself. The statement module lists the sources of the proposition and its
product-Levi translation: Waldspurger 2003 (`waldspurger-2003-plancherel`),
Proposition III.2.2, pp.265–266, and Silberger 1979
(`silberger-1979-harmonic-analysis`), §4.5 and Lemma 4.5.3, pp.184–186.
The analytic content is in the core proof. It does not apply Waldspurger's
criterion literally. Instead it works directly on Cartan cells of the central
quotient, combining the published chamber coefficient bound
`glProductLeviChamberCoefficientBound`, the published Cartan cell count
`GeneralLinear.CartanQuotient.cartanCellCount` and lattice summability; see
its Markdown for the route. The dual-opposite form is the project's derived
adapter. It is not a literal theorem about algebraic duals in those sources.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
