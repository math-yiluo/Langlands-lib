# Elementary reductions for Waldspurger VIII.4.1

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, Proposition VIII.4.1 and the first paragraph of its proof,
printed pp. 327–328 (registered source `waldspurger-2003-plancherel`).

This module proves the elementary parts of VIII.4.1 for the published closed
target `RationalCuspidalCentralProjectionFiniteStatement`. It does not prove
that target. The analytic case is named as a proposition.

## Generic translation lemma

Let `Γ` be a group, `A` a subgroup with a measurable structure for which
left multiplication is measurable, `μA` a left-invariant measure on `A`,
and `χ : A →* ℂˣ`.

- `centralProjection_eq_inv_mul_of_isLeftInvariant`: if `f` is left
  `H`-invariant and `b ∈ A` with `(b : Γ) ∈ H`, then for every `g`,
  `centralProjection μA χ f g = χ(b)⁻¹ * centralProjection μA χ f g`.
  The proof replaces the integration variable `a` by `b a`
  (`integral_mul_left_eq_self`). It then uses `χ(b a)⁻¹ = χ(b)⁻¹ χ(a)⁻¹` and
  `f(b (a g)) = f(a g)`. Finally it pulls out the constant
  (`integral_const_mul`). Both Mathlib lemmas hold for every function, with
  no integrability premise. The Bochner integral of a non-integrable function
  is `0`, and the identity is still true then.
- `centralProjection_eq_zero_of_isLeftInvariant`: if moreover `χ b ≠ 1`,
  then `centralProjection μA χ f = 0`. This holds because `χ(b)⁻¹ ≠ 1`.
- `schwartzCentralIntegralImage_eq_zero_of_isLeftInvariant` and
  `schwartzCentralIntegralSpan_eq_bot_of_isLeftInvariant`: suppose every
  element of a submodule `E` of a Schwartz space is left `H`-invariant, and
  `χ` is nontrivial at some point of `A ∩ H`. Then the raw image is `{0}`
  (it contains `centralProjection 0 = 0`) and the span is `⊥`.
- `CentralIntegralConvergesOn.mono_of_le`: convergence on `E` restricts to every
  `E' ≤ E`.

## Actual rational points

On the literal point-image `(rationalPoints.map s).range` with the subspace
Borel structure, the instance `MeasurableMul` is found automatically, and a
Haar measure is left invariant. Let `H` be a subgroup of the rational points,
`b` a point of the split-component image with `(b : G(F)) ∈ H`, and
`χ b ≠ 1`. Every element of `rationalCuspidalLevel hKc hPK ρ H` is
bi-invariant, hence left invariant (`IsBiInvariant.isLeftInvariant`).

- `rationalCuspidalCentralLevelImage_eq_zero`: the raw level image is `{0}`.
- `rationalCuspidalCentralLevelSpan_eq_bot`: the level span is `⊥`.
- `rationalCuspidalCentralLevel_finite_of_ne_one`: both conclusions of the
  closed VIII.4.1 target hold for this `H` and `χ`, with no hypothesis on
  convergence, compactness of `H` or unitarity.

These lemmas formalize the source's first step: "if `χ` is nontrivial on
`A_G ∩ H` then `p_χ(f) = 0` for every `f ∈ °C_H`". The source's
translation argument uses the integral's convergence. The Lean argument does
not need it, because both sides are Bochner integrals related by a
measure-preserving change of variables.

## The remaining case and the assembly

`RationalCuspidalCentralTrivialLevelFiniteStatement` is a derived proposition.
Its parameters are exactly those of
`RationalCuspidalCentralProjectionFiniteStatement`. It has one extra premise,
`∀ b, (b : G(F)) ∈ H → χ b = 1` (that is, `χ` is trivial on `A_G ∩ H`). Its
conclusion is only the finite dimensionality of the actual level span
`rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H`. This is the case of
VIII.4.1 that the source handles by the VIII.2 projection, VIII.2.3
reproduction and VIII.3.2. The proposition is a statement and is not proved
here.

`RationalCuspidalCentralTrivialLevelFiniteStatement.centralProjectionFinite`
proves `RationalCuspidalCentralProjectionFiniteStatement` from two inputs: the
published closed convergence target `RationalSchwartzCentralConvergenceStatement`
and `RationalCuspidalCentralTrivialLevelFiniteStatement`. The proof
splits on whether some `b` of the split-component image lies in `H` with
`χ b ≠ 1`.

- If so, `rationalCuspidalCentralLevel_finite_of_ne_one` gives both conclusions.
- Otherwise, convergence on the whole Schwartz space restricts to the level
  (`CentralIntegralConvergesOn.mono_of_le`). The published
  `coe_schwartzCentralIntegralSpan_eq_image` then gives equality of the
  span's carrier with the raw image. The trivial-character proposition gives
  finite dimensionality.

Both inputs are explicit premises of this implication. It is a reduction, not
a proof of the closed target.

## Open hypotheses

This module leaves two propositions open, both premises of
`RationalCuspidalCentralTrivialLevelFiniteStatement.centralProjectionFinite`:

- `RationalSchwartzCentralConvergenceStatement` (closed central
  convergence on the whole rational Schwartz space) is proved in the Library as
  `rationalSchwartzCentralConvergence` (module `RationalSchwartzCentralConvergenceProof`).
- `RationalCuspidalCentralTrivialLevelFiniteStatement` is not proved in the Library. Its
  route is the local kernel step (`RationalCuspidalCentralKernelStep`), fed by the rank
  adapter (`RationalCuspidalUnit`) from the VIII.2 projection targets, inside a mutual
  well-founded assembly over rank. The kernel step also needs the split-central height
  estimates (`RationalSplitCenterHeightStatement`) and the VIII.3.2 integrability
  (`RationalCuspidalConjugationIntegrabilityStatement`).

All other results in this module are proved unconditionally. Nothing here
assumes same-rank finiteness, same-rank reconstruction, the closed target
itself or a dimension bound.
