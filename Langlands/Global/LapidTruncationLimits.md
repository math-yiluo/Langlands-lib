# Passing from truncated pairings to full pairings

The theorems in `Langlands.Global.LapidTruncationLimits` implement the
measure-theoretic implication used in the proof of Lapid's Proposition 2.
They work on an arbitrary measure space `(X, μ)`, with complex-valued functions
and a nontrivial countably generated filter of truncation parameters. In
particular, one can use `atTop` along a strictly regular ray. Write
`B(f, k) = ∫ x, f(x) conj(k(x)) dμ(x)` for the pairing in the Lean code.

## Provenance and scope

Derived from E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`. See the proof of
Lemma 9, p. 327 (PDF p. 336), and the opening paragraph of §8, p. 328
(PDF p. 337). Lapid uses equality with the original function on an exhausting
Siegel region and contraction of the orthogonal projection. The implementation
uses Fatou's lemma and allows almost-everywhere convergence instead of eventual
pointwise equality. The test uses `B(Λᵀf, Λᵀf)` rather than `B(Λᵀf, f)`, so it
does not require the pairing against a not-yet-square-integrable `f`.

This module does **not** construct or analyze Arthur truncation, prove the
Siegel-region identity, show that truncated wave packets are in `L²`, or
compute any asymptotic pairing limit. Those are separate adelic inputs.

## Statement

`Langlands.Global.TruncationPairingLimitStatement` packages the full conditional
implication. The two original functions are assumed almost everywhere strongly
measurable and their approximants square integrable for every index. Assume
almost-everywhere convergence for each family and eventual bounds on the real
diagonal pairings. The operators on `L²` are eventually orthogonal projections;
for each original function, *if* it is in `L²`, the approximants' classes
must eventually agree with its projected classes. If the mixed truncated
pairings tend to `z`, both originals are in `L²` and their pairing is `z`.
`truncationPairingLimit` implements this statement via the following lemmas.

## Implemented proofs

- `memLp_two_of_ae_tendsto_of_bounded_selfPairings`: if the square-integrable
  approximants `g i` tend almost everywhere to the almost-everywhere strongly
  measurable function `f` and `Re B(g i, g i) ≤ C` eventually, then `f` is
  square integrable. `B(g i, g i)` is the Hilbert self-pairing of the `L²`
  class. The bound gives `eLpNorm (g i) 2 μ ≤ ofReal (√C)` eventually; Fatou
  (`Lp.eLpNorm_le_of_ae_tendsto`) gives the same finite bound on `f`.
- `tendsto_toLp_of_ae_tendsto_of_starProjection`: if `f` is in `L²` and the
  `L²` classes `b i` of `g i` are eventually orthogonal projections of the
  class `a` of `f`, Pythagoras gives `‖a‖² = ‖b i‖² + ‖b i − a‖²`. In
  particular `‖b i‖ ≤ ‖a‖` eventually. If a strictly smaller extended norm
  bound held frequently, restricting to that subfilter and applying Fatou
  would bound the extended norm of `f` by the same smaller number. The
  norms therefore converge to `‖a‖`; Pythagoras and continuity of the square
  root now give `b i → a` in `L²`.
- `pairing_eq_of_truncation_limits`: use the diagonal bounds on both families
  for square integrability, then the strong convergence of both `L²` classes.
  Continuity of the Hilbert inner product shows that the mixed pairings tend
  to `B(f, f')`; uniqueness identifies this with the given limit `z`. For this
  comparison the two entries are reversed in Mathlib's inner product, since
  it conjugates the first entry and Lapid's pairing conjugates the second.
