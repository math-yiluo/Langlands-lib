# Weak automorphic induction of a Hecke character to a cuspidal class

This module defines Harris's weak automorphic induction from a Hecke
character for actual cuspidal classes. A class is a weak automorphic
induction of `χ` when some spectral presentation of the class carries an
unramified spectrum that matches `χ`. The matching condition is the
published numerical relation `SpectralSystem.IsWeakInductionOf`
(`Automorphic/Unramified/WeakInduction`). The attached spectra are those of
the published `CuspidalSpectralPresentation`. The module asserts no
existence and no uniqueness.

## Setting

`E` and `E'` are number fields in independent universes `uE` and `uE'`,
with an algebra map `E → E'`. Compactness of `AdeleQuotient E` is an
explicit hypothesis, as in the cuspidal modules on which this one is built.
For `r : ℕ`, `CuspidalOperatorRealization.IsoClass E r` is the type of
classes of actual irreducible cuspidal realizations of `GL(r + 1)` over
`E`, up to full-operator equivalence. `PositiveRankCuspidalClass E` is the
dependent sum of these classes over all `r`. Its `rank` is `r + 1`.

`IsoClass.HasSpectralSystem c s` says that some actual representative of `c`
has a `CuspidalSpectralPresentation` whose numerical spectral system is `s`.
The presentation's local factors live in a universe `uV`. This universe is
an explicit parameter of every declaration below.

## Definitions

- `CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf c χ`,
  for a class `c` of rank `r + 1` and a Hecke character `χ` of `E'`, holds
  when there is a spectral system `s : SpectralSystem (FinitePlace E) (r + 1)`
  that satisfies both of the following:
  - `HasSpectralSystem c s` holds, so `s` is attached to `c`;
  - `s.IsWeakInductionOf χ` holds.
- `PositiveRankCuspidalClass.IsWeakAutomorphicInductionOf c χ` is the same
  relation for the fixed-rank class carried by a mixed-rank class `c`.

## Results

- `SpectralSystem.IsWeakInductionOf.of_sameEulerPolynomials`: if `s` is
  weakly induced from `χ` and `s.SameEulerPolynomials t` holds, then `t` is
  weakly induced from `χ`. The hypothesis says that, at all but finitely
  many places outside both exceptional sets, the Euler polynomials of `s`
  and `t` agree. The proof keeps the rank conjunct. It intersects three cofinite
  sets: the places where the relation for `s` holds, the places where the
  Euler polynomials agree, and the places outside `s.exceptional`. The
  equality of Euler polynomials then transfers the matching identity.
- `SpectralSystem.isWeakInductionOf_restrict_iff`: enlarging the finite
  exceptional set by `SpectralSystem.restrict` does not change the
  relation. Both directions apply the previous theorem to the published
  `sameEulerPolynomials_restrict`.
- `IsoClass.IsWeakAutomorphicInductionOf.rank_eq`: the rank `r + 1` of a
  weak automorphic induction of `χ` equals `[E' : E]`. This is the rank
  conjunct of `IsWeakInductionOf`.
- `IsoClass.isWeakAutomorphicInductionOf_iff`: for any actual
  representative `S`, the relation holds for the class of `S` exactly when
  some `CuspidalSpectralPresentation` of `S` itself has a weakly induced
  spectral system. The proof is the published `hasSpectralSystem_iff`,
  which transports presentations along full-operator equivalences.
- `IsoClass.isWeakAutomorphicInductionOf_of_hasSpectralSystem`: an attached
  system `t` witnesses the relation as soon as `s.SameEulerPolynomials t`
  holds for some weakly induced system `s`. The system `s` need not be
  attached to any class.
- `PositiveRankCuspidalClass.isWeakAutomorphicInductionOf_ofFixedRank`
  (simp): on a fixed-rank class, the mixed-rank relation is the fixed-rank
  relation, by definition.
- `PositiveRankCuspidalClass.IsWeakAutomorphicInductionOf.rank_eq`: the
  rank of a mixed-rank weak automorphic induction of `χ` is `[E' : E]`.

## Source

Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), Definition 1.3(b), printed p. 186 (PDF
p. 10), is the source. Its retained TeX is `math_9611226v1.tex`, lines
570–597. Let `π ∈ Isob(n, E)` and `π' ∈ Isob(m, E')` with `n = m[E' : E]`.
Let `S` be a finite set of finite places of `E` that contains the
ramification of `π`, and let `S'` be the set of places above `S`; it
contains the ramification of `π'`. Then `π` is a weak automorphic induction
of `π'` relative to `S` if the unramified local identity holds at every
finite `v ∉ S`. Harris remarks that this is equivalent to the equality of
partial Euler products `L^S(s, π) = L^{S'}(s, π')`. He calls `π` a weak
automorphic induction of `π'` if this holds relative to some `S`.

The published `IsWeakInductionOf` formalizes the local identity in the case
`m = 1`, `π' = χ`. It corrects the identity to a direct sum over all places
above `v`, following Harris's Euler-product formulation and Tate 1979
(2.3.5). Its Markdown records this correction and the normalization of the
Euler polynomials.

Harris's Proposition 4.8 (printed p. 201, PDF p. 25, TeX lines 1554–1561)
uses the definition in this form: it produces a *cuspidal* automorphic
representation `Π` that is a weak automorphic induction of a Hecke
character. That is why the module works with cuspidal classes.

## Design choices

These choices are derived; they are not in Harris's text.

- **Cuspidal instead of isobaric.** Harris states the definition on
  `Isob(n, E)`. No isobaric automorphic objects exist in the Library. The
  module specializes to actual irreducible cuspidal classes, which is the
  case used in Proposition 4.8.
- **Existence over presentations.** The unramified components of `π` are
  intrinsic to `π` in Harris's setting. Here a class carries spectra only
  through supplied presentations. The Library does not prove that two
  presentations of one class give the same spectrum, nor that a class has a
  presentation. The relation therefore asks for *some* attached weakly
  induced spectrum. Two consequences follow:
  - a class with no presentation is never a weak automorphic induction;
  - a "for every attached spectrum" formulation would instead hold
    vacuously for such classes, so it is not used.
  Once uniqueness of attached spectra away from a finite set is available,
  `of_sameEulerPolynomials` shows that one witness is equivalent to all.
- **The set `S`.** "Relative to some `S`" is the cofinite quantifier inside
  `IsWeakInductionOf`. Places in the presentation's exceptional set play
  the role of Harris's `S` for `π`. The unramifiedness of `χ` and of `E'/E`
  above `v` is part of `IsWeakInductionOf`.
- **Ranks.** The fixed-rank index `r` stands for `GL(r + 1)`, as in
  `CuspidalOperatorRealization`. The rank equality `r + 1 = [E' : E]` is
  part of the relation, not a hypothesis.
- **Mixed rank.** The `PositiveRankCuspidalClass` form reads the retained
  fixed-rank class. It adds no new condition.

## Not asserted

This module does not assert or prove any of the following:

- the existence of a weak automorphic induction, or of a presentation;
- uniqueness of the inducing class, of `χ`, or of attached spectra;
- the isobaric form of Harris's definition, or the case `m > 1`;
- any compatibility at ramified or archimedean places;
- Harris's conditions `U(n, E)` and the hypotheses of Proposition 4.8.

These belong to separate predicates and statements. The relation uses no
Weil group, global or local.
