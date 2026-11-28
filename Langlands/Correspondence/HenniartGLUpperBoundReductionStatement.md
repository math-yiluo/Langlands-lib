# The supercuspidal stratum upper bound from maximal simple types

This module declares the **statement**
`Langlands.Henniart.SupercuspidalStratumUpperBoundReductionStatement`, with
universe parameters `uK uV uT`. It is a proposition definition, and the file
contains no proof of it. It says that four statements on maximal simple types
in `GL_N` together imply input (I1) of Option II of the numerical local
Langlands route note, the Library statement
`Langlands.Henniart.SupercuspidalStratumUpperBoundStatement`
(`Langlands/Correspondence/HenniartGLUpperBoundStatement.lean`). Its provenance
is *derived*. It is a reduction internal to the Library's formalization of the
route note, not a numbered result of a source. It records the argument of
Remark `rem:upper` of the route note, which deduces the upper bound from
Bushnell–Kutzko (1993) and (1994). See §3.

## 1. The statement

The proposition is an implication with four hypotheses. Each one is a Library
statement in `Langlands/BushnellKutzko/`. In them `p` is a prime, `K` a p-adic
field (`PadicField p`, with its canonical topology, valuation and local-field
structure), `N = k + 1`, and `π` a supercuspidal class of `GL_{k+1}(K)`
(`Correspondence.SupercuspidalAutomorphicClass K k.succPNat`). The sets of
maximal simple type pairs `glMaximalSimpleTypesAt N K t m` (positive depth,
principal order of period `t`, level `m`) and `glMaximalLevelZeroSimpleTypes N K`
(level zero) are those of `Langlands/BushnellKutzko/GLMaximalSimpleTypeSets.lean`.
Containment of a type in a class is `SupercuspidalClassContainsType`
(`Langlands/BushnellKutzko/SupercuspidalClassContainment.lean`).

1. **A1**, `BushnellKutzko.SupercuspidalClassMaximalTypeStatement.{uK, uV, uT}`
   (`SupercuspidalClassMaximalTypeStatement.lean`, BK93 (8.4.1) with (6.2.1)).
   Every `π` contains a pair of `glMaximalSimpleTypesAt N K t m` for some
   `t ≥ 1` dividing `N` and some `m ≥ 1`, or a pair of
   `glMaximalLevelZeroSimpleTypes N K`.
2. **A2**, `BushnellKutzko.SupercuspidalClassTypeInvariantsStatement.{uK, uV, uT}`
   (`SupercuspidalClassTypeInvariantsStatement.lean`, BK93 (6.2.5) for the
   torsion number, BK94 (3.10)(i) for the Swan exponent).
   (a) If `π` contains a pair of `glMaximalSimpleTypesAt N K t m` with
   `t, m ≥ 1`, then `t ∣ N`, the torsion number of `π` is `N / t` and its Swan
   exponent is `m * (N / t)`.
   (b) If `π` contains a level-zero pair, its torsion number is `N` and its Swan
   exponent is `0`.
3. **A3**, `BushnellKutzko.SupercuspidalClassConjugateTypeTwistStatement.{uK, uV, uT}`
   (`SupercuspidalClassConjugateTypeTwistStatement.lean`, BK93 (6.2.3)). If `π`
   contains a maximal simple type pair `x` (of either kind), and `π'` contains
   a pair `x'` that is `GL_N(K)`-conjugate to `x`, then
   `π' = supercuspidalUnramifiedTwist K k z π` for some `z : ℂˣ`.
4. **Q3**, `BushnellKutzko.GLMaximalSimpleTypeLabelBoundStatement.{uK, uT}`
   (`GLMaximalSimpleTypeLabelBoundStatement.lean`, BK94 (3.7)–(3.8)). For every
   nonarchimedean local field `F` and `N ≥ 1`, with `q_F = Nat.card 𝓀[F]`:
   for `t ≥ 1` dividing `N` and `m ≥ 1` there is a labelling
   `glMaximalSimpleTypesAt N F t m → extendedLabelSet m t (N / t) q_F` whose
   values all have `e = 1` and whose fibres lie in single `GL_N(F)`-conjugacy
   classes; and there is a labelling
   `glMaximalLevelZeroSimpleTypes N F → degenerateLabelSet N q_F` whose fibres
   lie in single conjugacy classes.

The conclusion is `SupercuspidalStratumUpperBoundStatement.{uK, uV}`,
unchanged: for every prime `p`, every `K : PadicField.{uK} p` and all
`k s f : ℕ`, the refined supercuspidal orbit stratum
`Numerical.supercuspidalRefinedStratum.{uK, uV} K k s f` has `encard` at most
`Numerical.polarPartCount q (k + 1) f s`, where
`q = K.canonicalTopologicalData.residueCardinality`.

The statement has no other hypotheses. The label count it relies on,
`Langlands.Henniart.bushnellKutzkoLabelCount : BushnellKutzkoLabelCountStatement`
(`Langlands/Correspondence/BushnellKutzkoLabelCountProof.lean`), is a theorem of
the Library and is used in the proof, not assumed.

## 2. Universe levels

- `uK` is the universe of the p-adic field `K`. It is shared by A1–A3, Q3 and
  the conclusion.
- `uV` is the universe of the carriers of the supercuspidal classes. It
  appears in A1–A3 and in the conclusion.
- `uT` is the universe of the carriers of the type pairs (`GLRepresentationPair`).
  It appears in A1–A3 and in Q3, and not in the conclusion.

Q3 has its own universe parameters `uF` (the local field `F`) and `uρ` (the
type carriers). They are set to `uF := uK`, so that Q3 applies to
`F = K.Carrier`, and `uρ := uT`, so that Q3 labels the same type sets that A1–A3
speak about. Because `uT` does not occur in the conclusion, (I1) follows from
proofs of A1–A3 and Q3 at any single universe, for example `uT = 0`.

## 3. Provenance

The source of the argument is the operator route note *Numerical local
Langlands for GL_n, counts on the two sides and the recommended route*
(16 November 2026, `operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`):

- **Remark `rem:upper`** (lines 584–593). When only the upper bound
  `|S_K(n, s, f)| ≤ ν(n, f, s; q)` is needed, it suffices to have exhaustion
  and maximality (Theorem `thm:BK` (v) and the first half of (iv)), part (ii)
  (two representations containing the same maximal simple type are unramified
  twists of each other), Proposition `prop:T2`, and the statement that the
  maximal simple types with given `(t, m)` fall into at most
  `|{(p, φ) : e(p) = 1}|` conjugacy classes.
- **Theorem `thm:BK94`** (line 532), BK94 (3.7)–(3.8): the labels of
  conjugacy classes of simple types, with `e(p) = 1` for maximal types.
- **Lemma `lem:BKlabels`** with its proof (lines 538–549): with `t = n/f` and
  `m = s/f`, the labels with `e(p) = 1` are counted by `ν(n, f, s; q)`, and at
  level zero by `ν(n, n, 0; q)`. In the Library this count is the proved
  `bushnellKutzkoLabelCount`.
- The sentence after Proposition `prop:T2` (line 514): a class containing a
  maximal simple type attached to `[𝔄, m, 0, β]` has torsion number
  `f = n / e(𝔄)` and Swan exponent `m f`.

The underlying results of the sources:

- C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact
  open subgroups* (1993) (`bushnell-kutzko-1993-admissible-dual-gln`; PDF page
  = printed page + 12): (8.4.1), printed p. 297 (exhaustion; hypothesis A1);
  (6.2.3), printed p. 204 (hypothesis A3); (6.2.5), printed pp. 204–205 (the
  torsion number; hypothesis A2).
- C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing conjugacy
  classes* (1994) (`bushnell-kutzko-1994-simple-types-conjugacy-classes`; PDF
  page = printed page + 13): (3.7)–(3.8), printed pp. 125–126 (the labels;
  hypothesis Q3).

The route note's remark is an argument about representations up to
isomorphism and their unramified-twist orbits. The present statement is the
same argument for the Library's objects: the stratum is a set of
unramified-twist orbits of supercuspidal classes
(`PadicSupercuspidal.unramifiedOrbitClass`), and the labels are the Library's
`extendedLabelSet` and `degenerateLabelSet`.

## 4. The route of the proof

This module does not prove the statement. The following route proves it from
the four hypotheses as stated here. Fix `p`, `K`, `k`, `s`, `f`, and put
`N = k + 1` and `q = K.canonicalTopologicalData.residueCardinality`.

1. For each orbit `c` in the stratum choose a class `π_c` in it with Swan
   exponent `s` and torsion number `f`. If `π_c'` is an unramified twist of
   `π_c`, then `c = c'`, by `PadicSupercuspidal.unramifiedOrbitClass_twist`.
   Here `Numerical.supercuspidalUnramifiedTwist K k z π` and
   `PadicSupercuspidal.unramifiedTwistBasisEquiv K z` agree on the summand of
   rank `k + 1` by definition (`rfl`).
2. A class has at most one Swan exponent (`HasSupercuspidalSwan` fixes the
   conductor). By A1 and A2, if `s = 0` every `π_c` contains a level-zero pair,
   and `f = N`. If `s ≥ 1`, every `π_c` contains a pair of
   `glMaximalSimpleTypesAt N K (N / f) (s / f)`, with `1 ≤ f`, `f ∣ N` and
   `f ∣ s`. (A positive-depth type gives Swan exponent `m * (N / t) ≥ 1`, a
   level-zero type gives `0`.) If the stratum is empty, the bound is trivial.
3. Q3 at `F = K.Carrier`. Its `q_F = Nat.card 𝓀[K.Carrier]`, formed with the
   canonical instances of `K`, is `K.canonicalTopologicalData.residueCardinality`
   by definition (`rfl`). With `t = N / f` one has `N / t = f`
   (`Nat.div_div_self`), so the labels lie in
   `{y ∈ extendedLabelSet (s / f) (N / f) f q | y.1.e = 1}`, or in
   `degenerateLabelSet N q` at level zero. No additive character is needed:
   none of A1–A3 and Q3 takes one as a parameter.
4. The map `c ↦ label of the type in π_c` is injective. Equal labels give
   conjugate pairs by Q3, the classes are unramified twists of each other by
   A3, and so the orbits agree by step 1.
5. `q` is a prime power (`residueCardinality_eq_pow`, `residueDegree_pos`).
   By `bushnellKutzkoLabelCount` with `n = N`, the label set has
   `polarPartCount q N f (f * (s / f)) = polarPartCount q N f s` elements, or
   `polarPartCount q N N 0` elements at level zero. The injection bounds the
   `encard` of the stratum (`ENat.card_le_card_of_injective`).

## 5. Scope

- Only the upper bound is concerned (route note, Remark `rem:upper`). The
  lower bound, the uniqueness of the type contained in a class (BK93 (6.2.4),
  (5.7.1)) and the non-conjugacy of types with different labels are not
  hypotheses and are not asserted.
- Each of A1–A3 and Q3 is a separate premise of the reduction, and the
  conclusion is the Library statement of input (I1) without change.
