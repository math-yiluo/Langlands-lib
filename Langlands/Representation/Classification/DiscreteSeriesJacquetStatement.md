# Discrete-series temperedness and opposite Jacquet quotients

This pair states two prerequisites for the discrete-series support and summand
results used in the tempered part of the Langlands quotient argument.
`Langlands.GLDiscreteSeriesJacquetPrerequisitesStatement` is their conjunction.
All three declarations are proposition definitions; this file proves none of the
representation-theoretic implications.

## Exact statements and actual objects

Both components quantify over every prime `p`, every finite extension
`F : PadicField p` of `Q_p`, its actual topological data `T`, a positive rank `n`,
and a standard positive block shape `B` of `n`. Put
`M = B.Levi F.Carrier = ∏ i, GL_(B.size i)(F)` and `Q = M / Z(M)`.
The topology is the one supplied by `T`; the proved instance
`T.leviTopologicalGroup B` makes the product Levi a topological group.
The measure variables range over every Borel measurable structure on `Q` and
every Haar measure `μ` on it. This range is nonempty by
`T.exists_isHaarMeasure_leviCentralQuotient B` in
[TemperedInductionStatement](TemperedInductionStatement.md).

`GLLeviDiscreteSeriesTemperedStatement` states, for every actual complex
representation `σ` of `M` on a carrier `W`,

```text
IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
  IsTemperedModCenter σ μ.
```

The square-integrability predicate includes admissibility and an actual smooth
unitary scalar central character. It requires all coefficient norms from the
smooth contragredient and all vectors to lie in `L²(Q, μ)`. The tempered
predicate retains admissibility and a smooth unitary scalar central character,
and requires those norms to lie in `L^(2+ε)(Q, μ)` for every real `ε > 0`.
Neither predicate is defined by the other or by a Jacquet exponent criterion.
There is no assumed tensor factorization of `σ`.

`GLTemperedDiscreteSeriesJacquetQuotientStatement` also quantifies over a complex
representation `π` of `GL_n(F)` on `V`. Its hypotheses are

```text
IsIrreducible π, T.IsTempered π,
IsIrreducible σ, IsSquareIntegrableModCenter σ μ.
```

Admissibility is included in the analytic predicates, and irreducibility
includes nontriviality. There is no omitted finite-length hypothesis or
assumed quotient map. Let `J` be the actual opposite normalized Jacquet
representation specified below. The conclusion is

```text
(∃ S : Subrepresentation J,
   ∃ q : S.toRepresentation.IntertwiningMap σ, Surjective q)
  ↔ (∃ q : J.IntertwiningMap σ, Surjective q).
```

The left side is exactly an irreducible subquotient, with its invariant
subspace and surjective intertwiner supplied as witnesses. The right side is
an actual quotient of the whole Jacquet representation. The witnesses are
conclusions, not fields of a representation datum. The field universe `uF`,
ambient carrier universe `uV`, and Levi carrier universe `uW` are independent.
Actual intertwiners allow their source and target carriers to have different
universes. The first component uses only `uF` and `uW`.

## Opposite Jacquet normalization

Let `P` be the standard upper block parabolic, with common product Levi `M`,
and let `δ = T.leviModulus B` be its positive full modulus. In block matrices,

```text
δ(m) = ∏_(i<j) |det m_i|^(B.size j) / |det m_j|^(B.size i),
```

with normalized absolute value `q^(-ord_F)`. The opposite parabolic has
modulus `δ⁻¹`. The carrier of `J` is the quotient
`Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)`.
The action uses the published generic construction
`Jacquet.normalizedActionOfModulus` on this actual opposite unipotent subgroup
and the embedded Levi. The inclusion of the embedded Levi in its normalizer
is the proved `B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup`.
The full modulus supplied to that construction is the inverse of the upper
modulus transported to the embedded Levi. Finally the action is pulled back
to the product Levi along `B.leviEquiv F.Carrier`.

Thus the multiplier on the opposite Jacquet quotient is
`δ_opposite^(-1/2) = δ_upper^(1/2)`. This uses the actual opposite quotient,
not the upper quotient with a changed scalar. The generic construction already
proves the representation laws and its formula on quotient classes. The local
`let J` merely specializes and transports this action; it introduces no new
axioms, group data, or unproved representation obligations.

## Original-source correspondence

The source is Allan J. Silberger, *Introduction to Harmonic Analysis on
Reductive p-adic Groups* (1979), registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Its one-based PDF page is the printed page plus six. The decisive formulas
on pp.121–123,187–189,193 were checked in rendered page images.
No errata note for this source was present in the current Library.

| Source location | Correspondence |
| --- | --- |
| Theorem 4.5.10(1)–(2), pp.188–189 | A smooth admissible matrix coefficient with unitary scalar central character that is square integrable on the central quotient is a tempered coefficient. Applied to every coefficient of the actual product Levi, this gives the first component after the analytic convention translation below. |
| Lemma 3.2.2(2), p.121, and Theorem 3.2.4, pp.122–123 | Class-exponent membership is equivalent to an irreducible subquotient of the opposite unnormalized Jacquet quotient of class `δ_opposite^(1/2) σ`. Twisting by `δ_opposite^(-1/2)` translates this to the left side of the second component. |
| Definition of weak class exponents and Lemma 4.5.6, p.187 | Weak class exponents are the tempered class exponents. The discrete-series input is tempered by Theorem 4.5.10 and the first component, so the occurrence condition needs no additional temperedness hypothesis on `σ`. |
| Theorem 4.5.18(1)–(2), p.193 | Weak class-exponent membership is equivalent to `δ_opposite^(1/2) σ` being a quotient of the opposite unnormalized Jacquet module. The same inverse-half twist gives the right side. |

In Theorem 4.5.18 the Levi representation belongs to the discrete series.
The Lean assertion preserves that assumption; it does not replace it by an
arbitrary tempered representation. The theorem is specialized from reductive
groups to positive-rank `GL_n` over finite extensions of `Q_p`, and from
semistandard parabolics to the standard block parabolics with their actual
opposites. Its first component also uses the source with the split reductive
group `M = ∏ GL_(B.size i)` and its full center. This is an explicit
specialization, not a general reductive assertion.

## Analytic convention translation

Silberger's tempered coefficient convention is the weak inequality of
Theorem 4.5.1 and the following definition, pp.183–184. The Library uses
`L^(2+ε)` on the actual central quotient. The correspondence is the derived
argument documented in
[TemperedInductionStatement](TemperedInductionStatement.md), under
“Analytic convention correspondence,” and applies to both `GL_n` and its
actual product Levi without factoring the representation.

For the first component, Theorem 4.5.10 sends each square-integrable
coefficient to the weak inequality. On a Cartan chamber modulo the full
split center, write `d(a) = δ_0(a) ≤ 1`. Double-coset volume is comparable to
`d(a)^(-1)`, and the spherical function is bounded by `d(a)^(1/2)` times a
polynomial in the length. Hence the `L^(2+ε)` integral is bounded by a
chamber lattice sum of `d(a)^(ε/2)` times a polynomial. This sum converges
because the positive root sum is strictly positive in every noncentral
chamber direction. The group, modulus, center, and estimates are products
for `M`; this does not assume a tensor decomposition of `σ`. Directions
of rank zero modulo the center are compact and cause no divergence.
Smooth coefficients are locally constant and measurable.

For the second component, the given analytic temperedness of `π` implies
the source weak inequality by the converse argument in the same published
Markdown: a normalized Jacquet exponent violating a weak chamber bound,
together with the Jacquet coefficient asymptotic and Cartan volume estimate,
would give disjoint chamber double cosets whose `L^(2+ε)` contributions grow
for some sufficiently small `ε > 0`. The weak exponent criterion then gives
the source's tempered coefficient inequality. The scalar unitary central
character needed to pass to the central quotient is already in the analytic
hypothesis. These are documented mathematical derivations, not formal proofs
or assertions that one of the imported statement targets has been proved.

The analytic inputs are J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques d’après Harish-Chandra* (2003), registered as
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`:
I.1(5), p.241 (Cartan double-coset measure), Theorem I.4.1, p.245 (Jacquet
coefficient asymptotic), Lemma II.1.1, p.251 (spherical-function bound), and
§III.2 / Proposition III.2.2, pp.265–266 (weak inequality and exponent
criterion). Its one-based PDF page is printed page minus 234. No errata note
for this source was present in the current Library. Borel Haar measures on
these locally compact second-countable quotients differ by a positive finite
scalar, which does not change membership in any of the finite `L^r` spaces
used here. This justifies the stated quantification over every such measure.

## Remaining boundaries

The analytic bridge, square-integrable-to-tempered implication, and Jacquet
quotient criterion still require Lean proofs. Theorem 4.5.18(3), involving
both normalized induced representations and their direct summands, and
Corollary 4.5.11, giving discrete-series support, are stated separately in
[TemperedSupportStatement](TemperedSupportStatement.md), with proofs still
open. In particular this pair does not claim the whole of Theorem
4.5.18, induction irreducibility, support uniqueness, or Langlands quotient
classification. Corollary 4.5.11's weakly critical-exponent refinement remains
open as well.
