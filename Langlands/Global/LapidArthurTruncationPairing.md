# The truncation pairing limit on the full rational quotient

`Langlands.Global.ArthurTruncation.FullQuotientTruncationPairingStatement`
applies the measure-theoretic `TruncationPairingLimitStatement` and the
pointwise `TruncationRayStatement` to the actual full-adelic Arthur
truncation. The measure is the rational quotient Haar measure
`rationalQuotientHaarMeasure F G` on `G(F)\G(𝔸_F)`.

The setting is the truncation data of `ArthurTruncation.lean`. That is a
number field, a connected reductive group, a maximal split torus, a generic
cocharacter, reflection data, a compact subgroup `K` that is Iwasawa for the
minimal parabolic, and a bijective character restriction. Truncating a
function `f` on the quotient means the following. Pull `f` back to
`G(𝔸_F)` along `LeftCosetSpace.mk`, apply `truncation` with parameter `T`,
and evaluate at the chosen representative `q.out`. This is the same
operator as the full-quotient conjunct of
`TruncationOrthogonalProjectionStatement`, and here it is called
`fullQuotientTruncation`.

The statement assumes `TruncationFinitenessStatement` and makes the
following hypotheses:

- `v` is a direction on which every simple relative root is strictly
  positive.
- There is a constant `C` such that, for every truncation parameter whose
  simple-root evaluations all exceed `C`, the full-quotient truncation
  satisfies `IsOrthogonalL2Extension` for the rational quotient Haar
  measure.
- `f` and `f'` are measurable complex functions on the quotient, and each is
  bounded on every compact set.
- For all sufficiently large natural `n`, the truncations of `f` and `f'`
  at parameter `n • v` are in `L²`.
- For each of `f` and `f'`, there is a uniform upper bound on the real part of
  the diagonal pairing `∫ Λ f · conj(Λ f)` of its truncation, for all
  sufficiently large `n`.
- The mixed pairing `∫ Λ f · conj(Λ f')` of the truncations tends to `z`.

Under these hypotheses, `f` and `f'` are in `L²` and
`∫ f · conj f' = z`. The pairing is conjugate-linear in the second argument.

## Provenance and scope

This is the measure-theoretic reduction in the proof of Lemma 9, printed
p. 327 (PDF p. 336), and in the opening paragraph of §8, printed p. 328 (PDF
p. 337), of E. Lapid, *On Arthur's asymptotic inner product formula of
truncated Eisenstein series*, Clay Math. Proc. 13 (2011), pp. 309–331. The
source is registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`. The orthogonal
projection hypothesis has the form of the full-quotient conjunct of the
Library's `TruncationOrthogonalProjectionStatement` (Arthur 2005, after
Proposition 13.1). If that statement supplies a constant `C` and a function
`h` for the same `K`, then `fun T hT => (h T hT).2` is the projection
hypothesis here. That statement only produces some suitable `K`, so the
compact subgroup has to be matched separately when this result is applied.

Lapid's proof uses the identity of Lapid 2006, Lemma 6.2, uniformly on
exhausting Siegel regions. The proof here uses eventual pointwise equality
together with Fatou's lemma instead, and makes no claim of the uniform
identity. Lapid's estimates are hypotheses here and are not proved. These are
square integrability of the truncations, the bounds on the diagonal pairings,
and the value of the mixed limit, which comes from Lapid's Proposition 1 and
Lemma 8. Cutoff finiteness and the projection extension are also hypotheses.
This is a supporting result for Lapid's Proposition 2, not that proposition.

## Implemented proof

- `fullQuotientTruncationRay` applies `truncationRay` to the pullback of a
  quotient function, which is left `G(F)`-invariant by
  `LeftCosetSpace.mk_subgroup_mul`. Since `mk (q.out) = q`, the evaluated
  truncation at `n • v` eventually equals `f q` for each fixed `q`.
- `eventually_regular_ray` shows that, for each simple root `β`, `n • v`
  eventually satisfies `C < β(n • v)`, because `β(v) > 0`. The relative roots
  are finite (`ArthurRelative.finite_relativeRoots`), so the simple roots are
  finite and the finitely many eventual conditions combine. So the projection
  extension holds for all large `n`.
- `pairing_eq_of_fullQuotientTruncationRay` chooses `N` beyond which the two
  square-integrability hypotheses and the projection extension hold. Then it
  shifts the index to `n + N`, which is still a sequence along `atTop`. For
  each shifted index it chooses a star projection `Q n` with the agreement
  property. The pointwise ray limit gives everywhere convergence to `f` and
  `f'`, so in particular almost everywhere convergence. Agreement of the
  projection with truncation, almost everywhere for measurable functions that
  are bounded on compact sets, identifies the `Lp` classes via `Lp.ext`. Then
  `pairing_eq_of_truncation_limits` gives square integrability and the
  pairing. The diagonal bounds and the mixed limit transfer to the shifted
  sequence by composition with the shift.
- `fullQuotientTruncationPairing` proves the named statement from the
  theorem above.
