# Nonlinkage of segments with square-integrable special heads

Author: Worker 389. The focused interface and source locations were supplied by
Worker 346.

`Langlands.Classification.SquareIntegrableSegmentNonlinkage.{uF,uV} F T`
states that two segments whose actual special heads are analytically
square-integrable are not linked. This is a source-derived proposition
definition. It supplies a target for a later proof and proves no nonlinkage
or classification theorem.

## Exact statement and existing objects

Fix arbitrary `p : ℕ` with `[Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, and a supplied `T : F.TopologicalData`.
Put `v = max uF uV` and use `T.topology`. The definition quantifies over
`Δ Δ' : T.Segment.{v,uF}` and actual smooth complex representations

```text
π  : SmoothRep.{0,uF,v} ℂ (GeneralLinear Δ.degree F.Carrier)
π' : SmoothRep.{0,uF,v} ℂ (GeneralLinear Δ'.degree F.Carrier).
```

Its four hypotheses, in order, are
`T.IsSegmentHead Δ π`, `T.IsSegmentHead Δ' π'`,
`T.IsSquareIntegrable π.representation`, and
`T.IsSquareIntegrable π'.representation`. Its conclusion is
`¬ Δ.IsLinked Δ'`.

The degrees need not agree. Segment rank and length are positive by their
existing structure fields, so both degrees are positive without additional
hypotheses. The segments may be equal; the existing
`Segment.not_isLinked_self` already handles that case. The field universe
`uF` and carrier parameter `uV` are independent. Both segment representatives
and heads have carriers in `Type (max uF uV)`, which is preserved under the
existing induction construction. No finite-dimensional carrier is required.

In `Classification.Segments`, a segment with base `ρ` and length `m` has
support `{ρ, νρ, …, ν^(m-1)ρ}`, where `ν = |det|_F` and the absolute value is
residue-normalized. `Segment.IsLinked` means that neither support contains
the other and their union is the support of a segment. The definition uses
this relation directly.

`T.IsSegmentHead Δ π` asserts that for an actual supercuspidal representative
of `Δ.base`, `π` is an irreducible quotient of the increasing product
`i(ρ, νρ, …, ν^(m-1)ρ)` and every irreducible quotient map has the same
kernel. It contains a surjective intertwining map and irreducibility; no
separate irreducibility hypothesis is needed here. This is the special
quotient, denoted `Q(Δ)` by Kudla and `L(Δ)` by Rodier. It is distinct from
the irreducible subrepresentation of the increasing product.

The product is the existing normalized induction of actual block factors
from the standard upper block parabolic. Its covariance is
`f(pg) = δ_P(p)^(1/2) σ(p) f(g)`, and the action is right translation.
Kudla §1.1, printed pp.367–368, especially equation (1.1.3), uses these
conventions.

`T.IsSquareIntegrable` is the analytic predicate in `Classification.Tempered`.
For every Borel Haar measure on the actual central quotient, it requires
admissibility, a unitary scalar central character, and `L²` membership of
all descended absolute matrix coefficients of vectors and smooth-dual
functionals. The Library proves existence of a Haar measure on this
quotient, so that quantification is not vacuous. Square-integrability is
not defined by a segment parameter or by the existence of a centered
cuspidal presentation.

## Original sources and derivation

Kudla, Proposition 1.2.3, printed p.369, describes square-integrable
representations as special quotients of segments whose middle
supercuspidal twist is unitary. Printed p.370 discusses the scalar central
characters and unitary normalization of supercuspidals and gives the
support-based linkage definition in Definition 1.2.4. Immediately after
Proposition 2.2.1 on printed p.373, Kudla writes such segments as

```text
[σ ν^(-(m-1)/2), σ ν^((m-1)/2)]
```

with `σ` supercuspidal and unitary central character, and explicitly
observes that two such segments cannot be linked. The present statement
isolates that observation for the existing head relation and analytic
predicate. It does not use tempered exhaustion or irreducibility of an
induced product as a hypothesis.

Rodier §4.1, printed p.210, distinguishes the quotient `L(Δ)` from the
subrepresentation `Z(Δ)` of the increasing product. Proposition 11,
printed p.212, gives the centered square-integrable description, using
endpoint index `r` and length `r+1`. Theorem 3(b), printed pp.211–212,
states uniqueness of ordered quotient segment parameters up to
permutation. Propositions 12–13 on p.212 give the surrounding tempered
exhaustion and irreducibility statements. These are parallel source
context; they are not proved inputs to this module. Rodier attributes
Proposition 11 to an unpublished result of Bernstein.

There is a necessary distinction between finding some centered segment
for a square-integrable representation and centering the particular
segment in a supplied `IsSegmentHead` witness. Applying only an exhaustion
statement does not identify that witness's segment. A centered-presentation
proof would also have to establish the relevant parameter identification
independently of the downstream results excluded below.

An alternative derivation uses only central actions and support
combinatorics. Suppose a common segment support contains the two supports.
Write the two starting positions in its integer twist string as `a,b`,
and their lengths as `m,m'`. For a scalar central character `ω` of a
representative of the common base, the scalar action on the first
increasing product, hence on its nonzero quotient, is

```text
ω(z)^m |z|_F^(r*m*(a+(m-1)/2)).
```

Here `r` is the common positive cuspidal rank. The positive half modulus
is trivial on scalar matrices. The other quotient has the analogous
formula with `b,m'`. Their unitary central actions imply that the two
exponent means `a+(m-1)/2` and `b+(m'-1)/2` agree, by evaluating at a
uniformizer with absolute value strictly between zero and one. Two
finite integer intervals with the same midpoint are nested, so their
supports cannot satisfy the two noncontainment clauses in `IsLinked`.
If the segments were linked, their union segment would supply the common
support needed for this argument.

This central-action argument explains a possible independent proof route;
it is not implemented by the proposition definition. In particular, it
does not assume that a unitary representative of each middle cuspidal
class has already been selected.

## Remaining proof obligations and independence

A proof must justify the scalar-character existence and compatibility
used above, transport along actual supercuspidal isomorphism classes,
compute the scalar action on normalized tensor-product induction and its
quotient, and derive the unitary scalar action from the analytic
hypotheses. The uniformizer and real-power calculation, comparison of
integer twist positions, and interval/support argument must then be
formalized. The published proposition
`SegmentConstituentCentralCharacter` describes a relevant compatibility
target; its definition is not a proof of that target.

A proof following the source's centered description instead must prove
that description for the supplied segment, with all analytic and
parameter-identification comparisons. The sources use a fixed Haar
measure; comparison with the Library's all-Haar-measures predicate
requires the usual positive-scalar invariance of integrability if that
source-based analytic route is used.

This result is intended upstream of tempered block uniqueness and the
shared special-head exhaustion route. Its proof must not use tempered
block uniqueness, `SquareIntegrableLanglandsClassification`,
square-integrable exhaustion, regular exhaustion, multisegment exhaustion,
ordered strong-head existence, or quotient coverage, nor obtain those
conclusions through transitive proof dependencies. Independent lower-level
results can be reused only after checking that independence. Nothing in
this statement asserts that any such result has already been proved.

## Imports, source editions, and reading record

The only direct imports are the published
`Langlands.Representation.Classification.Segments` and
`Langlands.Representation.Classification.Tempered`, inspected against
Library commit `e9ecbfeda9579d84259f3a6c2f76fe0354602b13`.
No existing published pair is changed.

- Stephen S. Kudla, *The local Langlands correspondence: the
  non-archimedean case*, in *Motives*, Part 2, Proc. Sympos. Pure Math. 55,
  Part 2, AMS, 1994, pp.365–391.
  Literature ID `kudla-1994-local-langlands-nonarchimedean`;
  SHA-256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
  Read printed pp.367–373, one-based PDF pp.377–383 of the retained volume;
  visually checked pp.368–369 and 373, including the half modulus and
  centered exponents.
- F. Rodier, *Représentations de GL(n,k) où k est un corps p-adique*,
  Séminaire Bourbaki, exposé 587, *Astérisque* 92–93 (1982), pp.201–218.
  Literature ID `rodier-1982-gln`;
  SHA-256 `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
  Read printed pp.210–212, one-based PDF pp.11–13; visually checked
  Proposition 11 and the adjacent propositions on p.212.

Both retained files were rehashed. No source-specific errata note was
present in the inspected project and current Library notes; this records
the local search scope, not an assertion that no errata exist elsewhere.
The existing `notes/henniart/gln-classification-sources.md` was read for
the retained classification and analytic source boundaries.
