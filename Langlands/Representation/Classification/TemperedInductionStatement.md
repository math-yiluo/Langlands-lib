# Tempered unitarity and normalized induction for GL_n

## Contribution and scope

`Langlands.GLTemperedInductionPrerequisitesStatement` is the conjunction of
`Langlands.GLTemperedUnitarityStatement` and
`Langlands.GLTemperedInductionStatement`. All three are proposition definitions.
They specialize Silberger (1979), Corollary 4.5.13 and Lemma 4.5.15, to general
linear groups over finite extensions of `Q_p`, using the independently defined
analytic tempered predicate and actual normalized parabolic induction.

The first component states that every irreducible tempered representation of
`GL_n(F)` is unitarizable. The second states that an irreducible tempered
representation of any standard block Levi is unitarizable and that its normalized
induction to `GL_n(F)` is completely reducible and tempered. The second component
retains an arbitrary representation of the actual Levi. It neither assumes a
tensor-product factorization nor needs such a factorization to state the result.

These definitions do not prove these assertions. The accompanying Haar-existence
helper is proved. The proof status of each component is recorded under
[Implemented helper, proof status and retained obligations](#implemented-helper-proof-status-and-retained-obligations).
This contribution does not assert irreducibility of induction,
existence or uniqueness of a Langlands quotient, or exhaustion by such quotients.
Silberger's discrete-series support and summand assertions (Corollary 4.5.11 and
Theorem 4.5.18) are stated separately in
[TemperedSupportStatement](TemperedSupportStatement.md). Both are proved, by
`Langlands.glTemperedDiscreteSeriesSupport` and
`Langlands.glTemperedDiscreteSeriesSummand`. The weakly critical-exponent
refinement of Corollary 4.5.11 is the separate conjunction
`GLWeaklyCriticalTemperedRefinementStatement`. Its pair-minimality component
has no proof in the Library, so the refinement as a whole is unproved.

## Exact mathematical statement

The field and representation carrier have independent universes `uF` and `uV`.
Quantify over a prime `p`, a `PadicField.{uF} p`, its topological data `T`, and
`n > 0`. The field object is a finite extension of `Q_p`; no chosen splitting or
embedding into the complex numbers is required. The coefficient field of every
representation is `ℂ`.

For the unitarity component, quantify over every `V : Type uV` with its additive
commutative group and complex module structures, and every actual representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`. The assertion is

```text
IsIrreducible ρ → T.IsTempered ρ → IsUnitarizable ρ.
```

For the induction component, also quantify over every ordered positive block
shape `B`, whose block sizes sum to `n`. Put

```text
M = B.Levi F.Carrier = ∏ i, GL_(B.size i)(F),
Q = M / Z(M).
```

Use the topology induced by `T`. Quantify over a measurable space on `Q` equipped
with `BorelSpace`, every Haar measure `μ` on it, every complex carrier `V : Type uV`,
and every actual representation `σ : Representation ℂ M V`. The assertion is

```text
IsIrreducible σ → IsTemperedModCenter σ μ →
  IsUnitarizable σ ∧
  IsSemisimpleRepresentation (T.normalizedParabolicInduced B σ) ∧
  T.IsTempered (T.normalizedParabolicInduced B σ).
```

Thus the input can be tested with any one of the quantified Borel Haar measures
on the Levi's quotient. The output `T.IsTempered` quantifies over every Borel Haar
measure of the ambient group's central quotient. Both quantifications have
actual measures available. No measure, admissibility, or coefficient-growth
conclusion is assumed in the induction construction.

Irreducibility is algebraic irreducibility of the actual action; it includes
nontriviality of the carrier. Admissibility is already part of the analytic
hypotheses, including smoothness and finite-dimensional fixed vectors for each
compact open subgroup. Consequently the source's separate admissibility
hypothesis has not been dropped. No finite-dimensionality of the full carrier
is imposed.

## Meanings of the imported predicates

`IsTemperedModCenter σ μ`, from `Classification/Tempered`, means that `σ` is
admissible and there exists a smooth unitary central character acting by scalars,
such that every absolute smooth matrix coefficient on the actual quotient `Q`
belongs to `L^(2+ε)(Q, μ)` for every real `ε > 0`. The coefficients range over all
vectors and all elements of the smooth contragredient. The descent to `Q` is
constructed in `MatrixCoefficient/ModuloCenter`, with well-definedness proved
from the scalar action and unitarity. This is an analytic condition, independent
of Jacquet exponents and parabolic induction.

`T.IsTempered ρ` uses this predicate for every Borel Haar measure on the central
quotient of `GL_n(F)`. The published theorem
`T.exists_isHaarMeasure_centralQuotient` supplies a measure, and
`T.IsTempered.isAdmissible` extracts the admissibility condition.

`IsUnitarizable`, from `Unitary/Basic`, means the existence of a positive definite
Hermitian form invariant under the actual action. It does not equip `V` with a
previously chosen norm or require a Hilbert completion. This is the algebraic
unitarizability assertion corresponding to Silberger's term "unitary": an
invariant unitary realization restricts to such a form on its smooth vectors.

Mathlib's `Representation.IsSemisimpleRepresentation` is
`ComplementedLattice (Subrepresentation ρ)`: every invariant subspace has an
invariant complement. This is algebraic complete reducibility. The source result
is complete reducibility of the admissible induced representation, so it implies
this precise conclusion. A particular decomposition, a list of summands, their
multiplicities, and finite length are not additional conclusions of this file.

## Normalization and specialization

For `G = GL_n(F)`, take `P_B` to be the standard upper block parabolic and `M` its
actual block diagonal Levi. The imported function representation
`T.normalizedParabolicInduced B σ` satisfies

```text
f(m u g) = δ_(P_B)(m)^(1/2) σ(m) f(g),
(i_(P_B)^G σ)(g₀) f(g) = f(g g₀).
```

The positive square root comes from the actual block modulus. In terms of block
matrices `m_i`, that modulus is

```text
δ_(P_B)(m) = ∏_(i<j) |det m_i|^(n_j) / |det m_j|^(n_i),
```

where `n_i = B.size i` and the normalized absolute value is `q^(-ord_F)`.
This agrees with the `Ind_P^G(δ_P^(1/2) σ)` displayed in Silberger's Lemma 4.5.15.
The action is right translation. No real exponent twist, sign reversal, or
opposite-parabolic replacement occurs in this statement.

Silberger's assertions apply to reductive groups. Here they are used for the
split reductive group `GL_n` and, for the input unitarity assertion in the second
component, the split reductive group `M = ∏ GL_(n_i)`. Standard block parabolics
are a documented restriction of that source scope. All block sizes are positive;
for positive total rank there is at least one block. The one-block case is
included. No assertion is made about all reductive groups or positive
characteristic local fields.

A scalar central element of `G` maps in `M` to the tuple `(z I_(n_i))_i`, on which
`δ_(P_B)` is one. Right translation by it in the induced representation therefore
acts by the restriction of the scalar central character of `σ`. In particular
the induced representation has a smooth unitary scalar central character. This
explains why the analytic output predicate, which requires one such character,
is appropriate even when induction is reducible.

## Analytic convention correspondence

Silberger defines admissible tempered representations through their tempered
matrix-coefficient functions (§4.5, p.184). Theorem 4.5.1 (pp.183–184) identifies
this, for the smooth coefficients in question, with a bound of the form
`|c(g)| ≤ C Ξ(g) (1 + length(g))^r`. Waldspurger's §III.2 and Proposition III.2.2
(pp.265–266) use this same weak inequality and characterize it by weak bounds on
normalized Jacquet exponents. Neither source is being quoted as a Lean theorem
about the Library's `IsTemperedModCenter`.

The needed analytic translation is a derived specialization for `H = GL_n(F)`
or a finite product of such groups, with a scalar unitary central character.
It is the same coefficient argument described in
[TemperedExponentStatement](TemperedExponentStatement.md), now also applied to
the actual block Levi. Here are the details relevant to that extension.

* The full center of each factor is split; the full center of the product is
  the product of those centers. Thus the quotient used in the Library is the
  quotient by the split center used in the estimates. Cartan double cosets,
  the minimal-parabolic modulus and `Ξ` are products of those for the factors;
  one can take the sum of the factor length functions. This is a statement about
  the group and its measures, and does not factor the representation `σ`.
* On the closed chamber modulo the center, write `d(a) = δ_0(a) ≤ 1`.
  Waldspurger I.1(5), p.241, gives double-coset volume comparable to `d(a)^(-1)`,
  and Lemma II.1.1, p.251, bounds `Ξ(a)` above by `d(a)^(1/2)` times a polynomial
  in the length. The same estimates hold for the product by multiplying them.
  Unitarity of the scalar central character allows the coefficient norm and
  these estimates to be used modulo the full center. For each `ε > 0`, the
  `L^(2+ε)` integral of a weakly bounded coefficient is then bounded by a lattice
  sum of `d(a)^(ε/2)` times a polynomial. The root sum is strictly positive on
  every nonzero chamber direction modulo the center, so this exponential decay
  makes the sum converge. Rank-zero factors modulo the center contribute only
  compact directions. Coefficients are locally constant, giving measurability.
* Conversely, use the Jacquet coefficient asymptotic of Waldspurger Theorem
  I.4.1, p.245, in precisely the form used in the proof of III.2.2 on p.266:
  for each normalized exponent `χ`, suitable vectors and a sufficiently deep
  chamber give `c(a) = δ_P(a)^(1/2) χ(a)`. If `|χ|` grows on any chamber
  direction modulo the center, perturb to a rational interior direction and
  take an integral multiple. Along its powers, disjoint compact-open double
  cosets have volumes comparable to `δ_P(a)^(-1)`. Their contributions to the
  coefficient's `L^(2+ε)` integral are proportional to
  `δ_P(a)^(ε/2) |χ(a)|^(2+ε)`. For sufficiently small positive `ε` this grows
  exponentially, contradicting integrability. Thus every exponent has the
  required weak bound; the central direction already has unit modulus.
  Waldspurger III.2.2 then gives the weak coefficient inequality. The same
  argument works in the product chamber; it uses the general reductive
  asymptotic theorem on the product group, not tensor decomposition of `σ`.
* Any Borel Haar measure on either quotient differs from a fixed quotient Haar
  measure by a positive finite scalar. The groups in question are locally
  compact and second countable. Multiplying the measure by that scalar does
  not change membership in any of the finite `L^(2+ε)` spaces. Hence the bridge
  applies to each input `μ` and yields the output for every ambient Haar measure.

In the unitarity component the analytic hypothesis supplies the scalar unitary
central character required by this argument. In the induction component it
supplies that character on `M`, and the covariance calculation above supplies
it on `G`. Accordingly Silberger's two conclusions translate into exactly the
analytic conclusions stated here. This paragraph and the preceding argument
document a mathematical derivation; they are not formal proofs of the bridge.
The separately published exponent-criterion proposition is not assumed as an
already proved implication.

## Original sources and declaration correspondence

The source copies are the registered retained originals. No errata file for
either source was present in the current Library when this contribution was
prepared.

| Source | Exact location | Use |
| --- | --- | --- |
| A. J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic Groups* (1979), `silberger-1979-harmonic-analysis`, SHA256 `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc` | Theorem 4.5.1 and following definition, pp.183–184 | Tempered functions and representations; equivalence with the weak coefficient inequality. |
| Same original | Corollary 4.5.13, p.190 | `GLTemperedUnitarityStatement`, and the `IsUnitarizable σ` conjunct of `GLTemperedInductionStatement`, applied respectively to `GL_n` and the block Levi. |
| Same original | Lemma 4.5.15, p.191 | Complete reducibility and temperedness of the actual positive-half-modulus normalized induction from an irreducible admissible tempered Levi representation. |
| J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra* (2003), `waldspurger-2003-plancherel`, SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7` | I.1(5), p.241; Theorem I.4.1, p.245; Lemma II.1.1, p.251; §III.2 and Proposition III.2.2, pp.265–266 | Cartan measure estimate, Jacquet coefficient asymptotic, `Ξ` estimate, and weak exponent criterion used in the explicitly derived analytic translation. |

For Silberger the one-based PDF page is the printed page plus six. For
Waldspurger it is the printed page minus 234. The formulas in Silberger's
pp.190–191 were checked visually because the text layer omits symbols.

## Implemented helper, proof status and retained obligations

`PadicField.TopologicalData.exists_isHaarMeasure_leviCentralQuotient` supplies a
Borel Haar measure on the actual quotient of `B.Levi F.Carrier` by its center.
The proof installs the published Levi topology, topological-group and local
compactness instances, installs the Borel measurable space and its reflexive
`BorelSpace` witness, and uses Mathlib's `Measure.haarMeasure`. The quotient
instances are inferred from the actual topological group. This is an internal
measure-existence construction following the existing ambient-group helper;
it proves that the analytic measure quantification is nonvacuous.

This pair proves none of the representation-theoretic implications. Their
status in the Library is as follows.

- `Langlands.glTemperedUnitarity`, in
  `Langlands.Representation.Classification.TemperedUnitarityProof`, proves
  `GLTemperedUnitarityStatement.{uF, uV}` exactly.
- The first conclusion of `GLTemperedInductionStatement`, unitarizability of
  `σ`, is isolated with exactly the same inputs and hypotheses as
  `GLLeviTemperedUnitarityStatement`. `Langlands.glLeviTemperedUnitarity`
  proves it.
- The second conclusion, semisimplicity of the normalized induction, follows
  from that theorem, the admissibility contained in `IsTemperedModCenter`, and
  `isSemisimple_normalizedParabolicInduced_of_admissible_unitarizable`. The
  Library has no separately named theorem for this conclusion.
- The final conclusion, temperedness of the normalized induction, is isolated
  as `GLTemperedInductionPreservationStatement`. It has no proof in the
  Library.

Hence `GLTemperedInductionStatement` and the conjunction
`GLTemperedInductionPrerequisitesStatement` are unproved. Silberger's p.190
proof invokes Corollaries 1.7.9 and 4.5.11; his p.191 proof invokes the
character criterion and continuity of constant terms. Their transitive proofs
are not reimplemented or certified by this contribution.
No Langlands-classification conclusion is an input field or an assumed axiom.

Worker 1058 updated the proof status in this file for the 2026-10-29
documentation audit; the Lean file is unchanged.
