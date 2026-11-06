# Supercuspidal Langlands quotients of tempered standard modules have one block (statement)

Author: Worker 1722. The exact form was requested by Worker 1719 for the
reduction of Henniart (2002), Theorem 1.6(b), task
`99282d49-8140-483c-8dfc-8411be315345`.

`Langlands.Classification.SupercuspidalTemperedQuotientSingleBlockStatement`
is a proposition definition with universe parameters `uF` and `uV`. It
states a theorem and does not prove it. The proof is a separate module.

## Exact statement and universes

Fix a prime `p` with `Fact p.Prime`, an arbitrary `F : PadicField.{uF} p`,
an arbitrary topological realization `T : F.TopologicalData`, and a natural
number `n`. The group is the actual `GL_(n+1)(F)`,
`GeneralLinear (n + 1) F.Carrier`, with the topology `T.topology`. The rank
is `n + 1`, so it is always positive.

Quantify over:

- every tempered Langlands datum
  `d : T.TemperedLanglandsDatum.{uV, uF} (n + 1)`, the published structure of
  `Classification/LanglandsData`. It consists of an ordered block shape
  `d.shape = (n_1, …, n_r)` of `n + 1`, irreducible tempered smooth blocks
  `π_i` of `GL_(n_i)(F)` on carriers in `Type uV`, and real exponents
  `u_1 > ⋯ > u_r`;
- every smooth complex representation
  `π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)`.
  Its carrier universe `max uF uV` is the universe of the standard module.

The assertion is

```text
d.IsLanglandsQuotient π →
  IsSupercuspidal π.representation →
  d.shape.length = 1.
```

`d.IsLanglandsQuotient π` is the published relation: `π` is irreducible and
there is a surjective intertwiner from the standard module
`d.standardModule = i(ν^(u_1) π_1, …, ν^(u_r) π_r)` onto `π`. Irreducibility
is Mathlib's `Representation.IsIrreducible`, which includes nontriviality.
The standard module is the published normalized parabolic induction from the
standard upper block parabolic of `d.shape`, with `ν = |det|`. The relation
asks for some irreducible quotient. It does not ask that `π` be the unique
irreducible quotient.

`GeneralLinear.IsSupercuspidal` is the published predicate of
`Classification/Supercuspidal`. It means admissibility, and vanishing of the
actual Jacquet coinvariants for every proper ordered block parabolic and for
every conjugate of its unipotent radical.

The conclusion `d.shape.length = 1` says that the datum has exactly one
block. So `d.shape` is the one-block shape `(n + 1)`, the datum consists of
one irreducible tempered `π_1` of `GL_(n+1)(F)` and one real exponent `u_1`,
and the standard module is `ν^(u_1) π_1` induced from the full group. The
statement does not assert that `π` is equivalent to `ν^(u_1) π_1`. No
existence or uniqueness of Langlands data is asserted, and no hypothesis on
the datum is added beyond the published structure.

The universes `uF` and `uV` are independent. The statement is stated over an
arbitrary `T`. A user who works with the canonical realization instantiates
`T := F.canonicalTopologicalData`.

## Source provenance

The provenance is derived. The proposition is a focused special case of the
uniqueness half of the Langlands classification for `GL_n(F)`, applied to a
supercuspidal representation.

| Original | Passage | Role |
| --- | --- | --- |
| S. S. Kudla, *The local Langlands correspondence: the non-archimedean case* (1994), `kudla-1994-local-langlands-nonarchimedean`, SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Theorem 2.2.2(a)–(b), printed pp. 373–374 (PDF pp. 383–384 of the volume) | Tempered form of the Langlands classification, with uniqueness. |
| G. Henniart, *Une caractérisation de la correspondance de Langlands locale pour GL(n)* (2002), `henniart-2002-characterization`, SHA256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306` | §2.8, printed p. 596 (PDF p. 10); §3.2–3.3, printed pp. 597–598 (PDF pp. 11–12) | Essentially square-integrable form of the classification, and the use in Theorem 1.6(b). |

Kudla's Theorem 2.2.2 says: "(a) Every irreducible admissible representation
π can be written as a quotient of an induced representation of the form
ξ = I_P^G(π_1(x_1) ⊗ ⋯ ⊗ π_m(x_m)) where the π_i's are tempered
representations and x_1 > x_2 > ⋯ > x_m are real numbers. (b) For a given π,
the standard parabolic P, the tempered representations π_1, …, π_m (up to
isomorphism) and the real numbers x_1 > x_2 > ⋯ > x_m are unique." Here
`π(x) = π ⊗ |det|^x` and `I_P^G` is normalized induction from the standard
upper parabolic. This matches `TemperedLanglandsDatum`, `standardModule` and
`IsLanglandsQuotient`, as recorded in
[LanglandsData](LanglandsData.md).

An irreducible supercuspidal `π` of `GL_(n+1)(F)` has the form `ν^x π_u`
with `π_u` unitary supercuspidal, hence tempered. So `π` is the quotient of
the one-block induced representation `π_u(x)`. By the uniqueness in
Theorem 2.2.2(b), every tempered datum with `π` as an irreducible quotient
has the same standard parabolic, here the whole group, so it has one block.
That is this proposition. Henniart's §2.8 states the same classification in
essentially square-integrable form: `i(π_1, …, π_r)` with
`α(π_1) ≥ ⋯ ≥ α(π_r)` has a unique irreducible quotient
`J(π_1, …, π_r)`, and `∑ π_i ↦ J(π_1, …, π_r)` is a bijection from
`N[A_2] − {0}` onto `A`. A supercuspidal `π` lies in `A_2`, so it corresponds
to the one-term sum.

The statement keeps only part of the source's uniqueness. It uses the
uniqueness of the parabolic, not that of the blocks or exponents. It concludes
`length = 1` for every tempered datum that has `π` as an irreducible
quotient. This is the form used for Henniart's Theorem 1.6(b),
(i) ⇒ (ii). In the Library, `IsLanglandsPairLPolynomial` defines the pair
L-factor of irreducible representations through the standard modules of
every pair of tempered Langlands data having them as irreducible quotients.
This is Henniart's convention of §2.8, `L(s, π × π') = ∏ L(s, π_i × π'_j)`.
Henniart's supercuspidal computation in §3.3 (printed p. 598, from Jacquet,
Piatetski-Shapiro and Shalika, Theorem 8.1) is about a supercuspidal `π`
itself. To use it, one needs that every such datum of a supercuspidal `π`
has one block. The proposition does not cite or assume Theorem 2.2.2 as a
hypothesis.

## Proof status

This pair proves nothing. The proof is a separate module,
`Langlands.Representation.Classification.SupercuspidalTemperedQuotientSingleBlockProof`,
whose theorem is
`Langlands.Classification.supercuspidalTemperedQuotientSingleBlock`. Its
route differs from the source: it uses second adjointness instead of the
uniqueness theorem. Its own Markdown describes the proof.
