# Cuspidal support of automorphic representations of `GL_n`, at the finite places

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** The module `Langlands.Global.Factors.CuspidalSupportStatement`
defines one predicate and states two propositions. It proves nothing.

- `Langlands.Global.IsFiniteInducedConstituent`: an irreducible automorphic
  operator subquotient `Q` of `GL_(r+1)` is a constituent, at the finite
  places, of the representation induced from given cuspidal data.
- `Langlands.Global.CuspidalSupportExistenceStatement`: every irreducible
  automorphic operator subquotient is such a constituent for some cuspidal
  data. This is the second half of Getz–Hahn (2024), Theorem 10.7.1, the
  "only if" direction of Langlands (1979), Proposition 2, for `GL_n`, read at
  the finite places.
- `Langlands.Global.CuspidalSupportUniquenessStatement`: those cuspidal data
  are unique up to a permutation and equivalence. This is Getz–Hahn (2024),
  Corollary 10.7.3, read at the finite places.

The module also defines one `local instance`: the canonical topology on
`GL_n(F_v)`, as in `CuspidalInducingDataRigidityStatement` and
`CuspidalInducedConstituentAutomorphyStatement`. Without it, Lean picks the
`Units` topology of the matrix ring, and the `representation` field of a
canonical object does not elaborate. Everything else is Library vocabulary:

- `CuspidalOperatorRealization`, `PositiveRankCuspidalClass`
  (`Langlands/Automorphic/CuspidalOperatorRealization.lean`) and
  `CuspidalSpectralPresentation`
  (`Langlands/Automorphic/CuspidalSpectralPresentation.lean`);
- `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`);
- `LocalRealization.padicObject` (`Langlands/Automorphic/PadicLocalCategory.lean`);
- `PadicField.canonicalNormalizedProductInduced`
  (`Langlands/Representation/Induction/BlockFactors.lean`);
- `Correspondence.AutomorphicObject`, `Correspondence.sphericalSubgroup` and
  `Correspondence.IsSubquotientOf`
  (`Langlands/Correspondence/AutomorphicRelations.lean`,
  `Langlands/Correspondence/UnramifiedNormalization.lean`);
- `Langlands.fixedVectors` (`Langlands/Representation/Smooth/Definitions.lean`);
- `Automorphic.IrreducibleOperatorSubquotient`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`) and
  `OperatorSubquotient.localRepresentation`
  (`Langlands/Automorphic/OperatorSubquotient.lean`).

**Why it is here.** L4 of this task's contract asks for the isobaric theory of
Getz–Hahn §10.7, and its context names GH 10.2.3–10.7.6 as the roadmap range.
The program ledger `notes/automorphic/global-program-coverage.md` (section "14
November 2026 admissibility of automorphic representations", list of remaining
L4 targets) lists "the converse half of GH Theorem 10.7.1" and "GH Corollary
10.7.3, p.287" as missing statements. The Library has the first half of
10.7.1 (`CuspidalInducedConstituentAutomorphyStatement`) and Theorem 10.7.2
(`CuspidalInducingDataRigidityStatement`), but no statement that every
automorphic representation of `GL_n` has cuspidal inducing data, and none
that those data are unique.

**Proof targets.** Later proof tasks should prove the Library statements
`Langlands.Global.CuspidalSupportExistenceStatement` (universe parameter `u`)
and `Langlands.Global.CuspidalSupportUniquenessStatement` (universe parameters
`u` and `uQ`). `u` is the universe of the number field and of every local
carrier; `uQ` is the factor universe of the spectral presentations.

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | `I(σ, λ)` and its local factors, p.271 (PDF 283); (10.34), Thm 10.7.1 and the remark on Lemma 1, pp.286–287 (PDF 298–299); Thm 10.7.2, Cor 10.7.3 and the sentence after it, p.287 (PDF 299); `π_i = \|det\|^(λ_i) π_i^1`, p.288 (PDF 300) |
| `langlands-1979-notion-automorphic-representation` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | `Ind σ`, constituents, `π°_v`, Lemma 1 and its proof, p.203 (PDF 198); Prop 2, Lemmas 3–5 and the start of the proof that automorphic representations are constituents, p.204 (PDF 199); end of that proof, Lemma 6, p.205 (PDF 200) |
| `jacquet-shalika-1981-euler-ii` | `4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8` | Thm (4.4), p.809 (PDF 34), as quoted in `CuspidalInducingDataRigidityStatement.md` §1 |
| `borel-jacquet-1979-automorphic` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | automorphic forms, §4.2, pp.194–195 (PDF 189–190); automorphic representations, §4.6, p.196 (PDF 191) |

Langlands' paper and Borel–Jacquet are consecutive papers in the same
registered file, the Corvallis volume, Part I. Its printed page is the PDF page
plus 5. GH cite Langlands' paper as "the appendix to [BJ79]". JS II was not
re-read for this module; its Theorem (4.4) enters only through the Library
statement `CuspidalInducingDataRigidityStatement`, whose Markdown quotes it.

**What the sources state.** GH p.286: "Given a cuspidal automorphic
representation `σ` of `M(𝔸_F)`, we form the induced representation `I(σ, λ)`
(10.34) as in (10.1). For the proof of the following theorem, see the appendix
to [BJ79]:

> **Theorem 10.7.1 (Langlands)** Any irreducible subquotient of `I(σ, λ)` is
> an automorphic representation, and every automorphic representation is of
> this form."

GH pp.286–287: "in [BJ79, Appendix, Lemma 1] Langlands observes that the
subquotients of `I(σ, λ)` can be described as follows. For all but finitely
many `v` the representation `σ_v` is unramified and `I(σ_v, λ)` has a unique
irreducible unramified subquotient `π°_v`. The irreducible subquotients of
`I(σ, λ)` are the representations of the form `⊗_v π_v`, where `π_v` is an
irreducible subquotient of `I(σ_v, λ)` for all `v` and `π_v ≅ π°_v` for almost
every `v`."

GH p.287 then restricts to `G = GL_n`. With `∑_(i=1)^k n_i = ∑_(j=1)^(k') n'_j = n`
and cuspidal automorphic representations `σ_i` (resp. `σ'_j`) of
`A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` (resp. `A_(GL_(n'_j)) \ GL_(n'_j)(𝔸_F)`), it
forms `σ = ⊗_i σ_i`, `σ' = ⊗_j σ'_j` and `I(σ, λ)`, `I(σ', λ')` for the standard
parabolics of types `(n_1, …, n_k)` and `(n'_1, …, n'_(k'))`, and states
Theorem 10.7.2 ([JS81a, Theorem 4.4]): if the irreducible unramified
subquotients of `I(σ_v, λ)` and `I(σ'_v, λ')` are isomorphic for `v ∉ S`, then
`k = k'` and there is a permutation `τ` of the set of `k` elements such that
`σ_i ≅ σ'_(τ(i))` and `λ_i = λ'_(τ(i))`. Then:

> "This immediately implies the following corollary:
>
> **Corollary 10.7.3** If `π` is an irreducible subquotient of `I(σ, λ)` and
> `I(σ', λ')` then the conclusion of Theorem 10.7.2 holds.
>
> Thus every automorphic representation of `GL_n(𝔸_F)` is a subquotient of
> `I(σ, λ)`, where `σ` and `λ` are unique up to a permutation in the sense made
> precise in Theorem 10.7.2."

GH p.288: for each cuspidal `π_i` of `GL_(n_i)(𝔸_F)` there is a unique
cuspidal `π_i^1` of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` with
`π_i(g) = |det g|^(λ_i) π_i^1(g)` for some `λ_i ∈ ℂ`. On p.271 the action of
`I(σ, λ)` has the factor `e^⟨H_P(xg), λ + ρ_P⟩`, so the induction is
normalized, and `I(σ, λ) ≅ ⊗'_v I(σ_v, λ)`.

Langlands p.203: for a parabolic `P` with Levi factor `M` and a cuspidal
representation `σ = ⊗σ_v` of `M(𝔸)`, `Ind σ = ⊗_v Ind σ_v`, and "an
irreducible subquotient of this representation is said to be a constituent of
it". "For almost all `v`, `Ind σ_v` has exactly one constituent `π°_v`
containing the trivial representation of `G(O_v)`."

> LEMMA 1. The constituents of `Ind σ` are the representations `π = ⊗π_v`
> where `π_v` is a constituent of `Ind σ_v` and `π_v = π°_v` for almost all `v`.

P.204:

> PROPOSITION 2. A representation `π` of `G(𝔸)` is an automorphic
> representation if and only if `π` is a constituent of `Ind σ` for some `P`
> and some `σ`.

Langlands adds that "the proof that every automorphic representation is a
constituent of some `Ind σ` does not involve the theory of Eisenstein series
in any serious way", and gives it on pp.204–205 (§5 below).

BJ79 §4.6, p.196: "An irreducible representation of `ℋ` is automorphic … if it
is isomorphic to a subquotient of a representation of `ℋ` in the space of
automorphic forms on `G(𝔸)`." Here `ℋ` is the global Hecke algebra, built from
`G(𝔸_f)` and the pair `(𝔤, K_∞)`.

## 2. The declarations

Throughout, `F` is a number field with `[CompactSpace (AdeleQuotient F)]`, the
instance needed by `CuspidalOperatorRealization`. Cuspidal data consist of

- `k : ℕ`, `m : Fin k → ℕ` and `hm : ∑ i, (m i + 1) = r + 1`;
- `T i : CuspidalOperatorRealization F (m i)`, actual cuspidal realizations of
  `GL_(m i + 1)` over `F`;
- `P i : CuspidalSpectralPresentation (T i)`, spectral presentations, and
  `h i : HasIrreducibleAdmissibleComponents (P i)`: every finite local
  component of `P i` is irreducible and admissible.

Write `σ_(i,v)` for the canonical object
`((P i).localComponent v).padicObject (h i v).1 (h i v).2` of
`AutomorphicObject (padicField v)` and `B` for the block shape
`⟨k, fun i => m i + 1, _, hm⟩`.

**`IsFiniteInducedConstituent hm P h Q`**, for
`Q : IrreducibleOperatorSubquotient F r`, holds when there are
`A v : AutomorphicObject.{u, u} (padicField v) r.succPNat` for every finite
place `v` (an irreducible admissible smooth representation of `GL_(r+1)(F_v)`
with carrier in universe `u`) and a finite set `S` of finite places such that

1. for every finite place `v`, `A v` is a subquotient (`IsSubquotientOf`) of
   `(padicField v).canonicalNormalizedProductInduced B (fun i => σ_(i,v).obj.representation)`;
2. for every finite place `v ∉ S`, `A v` has a nonzero vector fixed by
   `sphericalSubgroup (padicField v) r`, that is by `GL_(r+1)(O_v)`;
3. for every finite place `v` there is an injective intertwining map from
   `A v` to `Q.subquotient.localRepresentation v`, the restriction of `Q` to
   `GL_(r+1)(F_v)`.

Conditions 1–2 are the hypotheses of `CuspidalInducedConstituentAutomorphyStatement`
and condition 3 is its conclusion, for the same `A` and `S`.

**`CuspidalSupportExistenceStatement`**: for every `F`, every `r` and every
`Q : IrreducibleOperatorSubquotient F r` there are `k`, `m`, `hm`, `T`, spectral
presentations `P i : CuspidalSpectralPresentation.{u, u} (T i)` (factors in the
universe `u` of the form space) and `h` with
`IsFiniteInducedConstituent hm P h Q`.

**`CuspidalSupportUniquenessStatement`**: let `F`, `r`, and two families of
cuspidal data `(k, m, hm, T, P, h)` and `(k', m', hm', T', P', h')` of total
rank `r + 1`, with all presentations in factor universe `uQ`, be given, and
let `Q : IrreducibleOperatorSubquotient F r`. If
`IsFiniteInducedConstituent hm P h Q` and `IsFiniteInducedConstituent hm' P' h' Q`,
then there is `e : Fin k ≃ Fin k'` such that for every `i`,
`⟨m i, (T i).isoClass⟩ = ⟨m' (e i), (T' (e i)).isoClass⟩` in
`PositiveRankCuspidalClass F`.

## 3. Matching with the sources

- **Automorphic representations.** As in
  `CuspidalInducedConstituentAutomorphyStatement.md` §3: by BJ79 §4.6 an
  automorphic representation `π` is isomorphic to a quotient `V / U` of
  `ℋ`-invariant subspaces `U ⊆ V` of the space of automorphic forms (Library
  automorphic forms are those of BJ79 §4.2, `Langlands/Automorphic/Forms.md`).
  `ℋ`-invariance is invariance under `GL_(r+1)(𝔸_f)`, `K_∞` and the enveloping
  algebra, so `(V, U)` is an `OperatorSubquotient`, irreducible under the whole
  operator algebra: an `IrreducibleOperatorSubquotient F r`. Conversely every
  `IrreducibleOperatorSubquotient F r` is an irreducible `ℋ`-subquotient of
  the automorphic forms, that is, an automorphic representation of
  `GL_(r+1)(𝔸_F)`. Admissibility is not part of the Library notion; by BJ79
  §4.6 it is automatic, and the Library states this as
  `IrreducibleSubquotientAdmissibilityStatement` (not proved).
- **Cuspidal data and `λ`.** As in `CuspidalInducingDataRigidityStatement.md`
  §3: `T i` is a cuspidal `π_i` of `GL_(n_i)(𝔸_F)`, `n_i = m i + 1`, with no
  condition on the split centre. By GH p.288, `π_i = |det|^(λ_i) π_i^1` with
  `π_i^1` cuspidal on `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)`, so GH's `(σ, λ)` with
  `σ = ⊗_i π_i^1` and the Lean `T` determine each other, and the local factor
  at `v` of the normalized `I(σ, λ)` is the normalized induction of the
  `π_(i,v)`. Langlands' `σ` is any cuspidal representation of `M(𝔸)`. For
  `G = GL_(r+1)` and the standard parabolic of type `(n_1, …, n_k)`,
  `M = ∏_i GL_(n_i)`, and an irreducible cuspidal representation of `M(𝔸)` is
  `⊗_i π_i` with `π_i` cuspidal on `GL_(n_i)(𝔸_F)` (background, not asserted).
  Every parabolic of `GL_n` is conjugate to a standard block parabolic, and
  conjugate parabolics give equivalent induced representations, so only
  standard block parabolics occur. Langlands does not say whether his `Ind`
  is normalized; the two inductions differ by the twist `δ_P^(1/2)`, which is
  `∏_i |det_i|^(c_i)` for real `c_i`, and such twists of cuspidal
  realizations are cuspidal realizations. So "constituent of some `Ind σ`"
  means the same for both normalizations.
- **Local components.** `(P i).localComponent v` is the actual embedded factor
  at `v` of a spectral presentation, the `σ_(i,v)` of GH (after `λ` is
  absorbed) and of Langlands. `LocalRealization.padicObject` views it in the
  correspondence category with its original action. The data are never
  vacuous: for factor universe `u` every cuspidal realization has a
  presentation satisfying `h`, by the proved
  `cuspidalIrreducibleAdmissibleFiniteSliceExistence`
  (`Langlands/Automorphic/CuspidalAdmissible/Existence.lean`) and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
  (`Langlands/Automorphic/CuspidalSlicePresentation.lean`), the facts cited
  in `CuspidalInducingDataRigidityStatement.md` §3.
- **`IsFiniteInducedConstituent` is "`Q` is a constituent of `Ind σ`", read
  at the finite places.** Suppose `π ≅ Q` is a constituent of `I(σ, λ)`. By
  Langlands' Lemma 1, `π ≅ ⊗_v π_v` with `π_v` a constituent of `I(σ_v, λ)` and
  `π_v ≅ π°_v` for almost all `v`. Take `A v := π_v` for finite `v`. It has a
  representative with carrier in universe `u`, as a quotient of a subspace of
  the induced carrier. Condition 1 holds. Condition 2: `π°_v` contains the
  trivial representation of `GL_(r+1)(O_v)`, so `A v` is spherical for almost
  all `v`. Condition 3: restricted to `GL_(r+1)(F_v)`, `π` is
  `π_v ⊗ (⊗'_(w ≠ v) π_w)` with the group acting on the first factor; for a
  nonzero vector `y` of the second factor, `x ↦ x ⊗ y` embeds `A v`. Conversely
  the predicate says nothing at the infinite places, so it is weaker than
  "`Q` is a constituent of `I(σ, λ)`". This comparison is background and is
  not asserted; the Library has no global induced representation.
- **Condition 2 is automatic.** By background facts (an irreducible
  automorphic `Q` is admissible and is a restricted tensor product, Flath; so
  its restriction to `GL_(r+1)(F_v)` is isotypic, and `Q` has a nonzero vector
  fixed by `GL_(r+1)(O_v)` for almost all `v`), every irreducible `A v`
  embedding into the restriction of `Q` is spherical for almost all `v`. So the
  predicate is equivalent to conditions 1 and 3 alone. Condition 2 is kept so
  that the predicate matches the hypotheses of
  `CuspidalInducedConstituentAutomorphyStatement` and of
  `CuspidalInducingDataRigidityStatement`. This equivalence is not asserted.
- **Existence.** `CuspidalSupportExistenceStatement` is GH Theorem 10.7.1,
  "every automorphic representation is of this form", and Langlands'
  Proposition 2, "only if", for `G = GL_(r+1)`, with the conclusion read through
  the previous bullets. The presentations are asked for in factor universe
  `u`, where the existence results of the bullet "Local components" apply.
  `k ≥ 1` is forced by `hm`, since `r + 1 ≥ 1`; `k = 1` is the case `P = G`,
  `Q` cuspidal.
- **Uniqueness.** `CuspidalSupportUniquenessStatement` is GH Corollary 10.7.3
  with "`π` is an irreducible subquotient of `I(σ, λ)` and `I(σ', λ')`" read as
  the two predicates. The hypotheses are weaker than GH's, since nothing is
  assumed at the infinite places, so the statement is at least as strong as
  GH's at the finite places. The conclusion is the conclusion of Theorem
  10.7.2 in the form of `CuspidalInducingDataRigidityStatement.md` §4:
  `m' (e i) = m i` and `T i`, `T' (e i)` have the same full operator class,
  that is `π_i ≅ π'_(e(i))`, which is GH's `σ_i ≅ σ'_(τ(i))`, `λ_i = λ'_(τ(i))`
  with `τ = e` by the bullet "Cuspidal data and `λ`". `k = k'` is part of
  `e : Fin k ≃ Fin k'`.
- **Universes.** In the existence statement the presentations are in factor
  universe `u`. In the uniqueness statement both families of presentations are
  in the same arbitrary factor universe `uQ`, as in
  `CuspidalInducingDataRigidityStatement`. `A v` has its carrier in universe
  `u`; by the bullet on `IsFiniteInducedConstituent` this loses nothing.

## 4. Relation to other statements

- **`CuspidalInducedConstituentAutomorphyStatement`** (first half of GH
  10.7.1). For given cuspidal data, `A` and `S` satisfying conditions 1–2, it
  asserts some `Q` satisfying condition 3, that is
  `IsFiniteInducedConstituent hm P h Q` with these `A` and `S`.
  `CuspidalSupportExistenceStatement` is its converse: every `Q` arises in
  this way from some cuspidal data. Together they are GH Theorem 10.7.1 at the
  finite places.
- **`CuspidalInducingDataRigidityStatement`** (GH 10.7.2). GH derive 10.7.3
  from 10.7.2 "immediately"; §5 spells out the steps, which use the isotypy
  of local restrictions.
- **Local components at every place.** Candidate `08944adf` (accepted by
  machine validation, peer review pending when this module was written; not
  in Library commit `c40a0134`) states, for irreducible jointly admissible
  operator subquotients, that the restriction to `GL_(r+1)(F_v)` is isotypic
  (`LocalComponentExistenceStatement`) and that an irreducible representation
  with a nonzero intertwiner into it is its isotypic type
  (`LocalComponentEmbeddingStatement`). This module does not import it.
- **Cuspidal support as an isobaric datum.** Together, the two statements of
  this module give every irreducible automorphic `Q` of `GL_(r+1)` a well
  defined multiset `{⟨m i, (T i).isoClass⟩}` of positive-rank cuspidal classes,
  an element of the Library type `Langlands.Automorphic.IsobaricData F`
  (`Langlands/Automorphic/IsobaricData.lean`). That map is not defined here.
- **Isobaric representations.** `Automorphic.IrreducibleOperatorSubquotient.IsIsobaric`
  (`Langlands/Global/Factors/IsobaricAutomorphicRepresentation.lean`, GH
  Definition 10.7.6) singles out, among the constituents with a given cuspidal
  support, the one whose local components are the local isobaric sums. Not
  every constituent is isobaric, and this module does not say which `Q` are.

## 5. Proof routes (for the proof tasks; not part of the statements)

**Existence** (Langlands pp.204–205). Realize `π` on `V / U` with `V`
generated by one automorphic form `φ`. Lemma 3 (BJ79): automorphic forms are
`Z(𝔸)`-finite. Lemma 4: the constant term `φ_P(m; g) = ∫_(N(F)\N(𝔸)) φ(nmg) dn`
is an automorphic form on `M(𝔸)`. Lemma 5 (Langlands 1976): if `φ` is
orthogonal to cusp forms along every `P` (`φ ⊥ P` for all `P`), then `φ = 0`.
Totally order the conjugacy classes of parabolics compatibly with rank, let
`{P_φ}` be the least `{P}` such that `{P} < {P'}` implies `φ ⊥ P'`, and choose
the generator `φ` with `{P_φ}` minimal. Then `φ ↦ φ_P` does not identify the
images of `U` and `V`, so `π` is realized on `V_P / U_P` inside the space
`𝒜_P^0` of smooth `K`-finite functions on `N(𝔸)P(F) \ G(𝔸)` that are
cuspidal automorphic along `M`. Lemma 6 makes `A(𝔸)` (the centre of `M`) act
by a character `χ` on the generator. Langlands then lets `ν` be the positive
character of `M(𝔸)` with `ν(a) = |χ(a)|` on `A(𝔸)`. It enters only the weight
`ν^(-2)` in the norm defining the Hilbert space
`L^2_0 = L^2_0(M(F) \ M(𝔸), χ)` (his condition (ii)). It is not an inducing
twist. Projecting `m ↦ φ(m, g)` onto an irreducible summand `H` of `L^2_0`
realizes `π` as a quotient of a space `V'`. In Langlands' words (p.205, last
sentence before the converse): "if `δ²` is the modular function for `M(𝔸)` on
`N(𝔸)` and `σ` the representation of `M(𝔸)` on `H` then `V'` is contained in
the space of `Ind δ^(-1) σ`." So the inducing representation is `δ^(-1) σ`,
where `δ` is the square root of the modular function of `M(𝔸)` acting on
`N(𝔸)`; it is not `σ ν^(-1)`. For `GL_(r+1)` and a block Levi
`M = ∏ GL_(n_i)`, `σ = ⊗ π_i` with `π_i` cuspidal. Also `δ` is a product
`∏_i |det_i|^(c_i)` with real `c_i`. As §3 (**Cuspidal data**) notes, Langlands
does not say whether his `Ind` is normalized; write `δ_P = δ²` for the modular
function. If `Ind` is normalized, `V'` lies in the normalized induction of
`δ^(-1) σ`. If it is unnormalized, `V'` lies in the normalized induction of
`δ_P^(-1/2) δ^(-1) σ = δ^(-2) σ`. Either way, the representation induced in
the normalized sense is `⊗_i |det_i|^(e_i) π_i` for real `e_i`, whose blocks
`|det_i|^(e_i) π_i` are cuspidal again. The proof task takes these blocks, not
the `π_i` themselves, as the cuspidal data `T`. The finite-place form then
follows from Lemma 1 as in §3. The Library has constant terms along maximal
block parabolics (`constantTerm`, used in `CuspidalOperatorRealization.lean`)
and the cuspidal finite-slice and presentation existence results cited in
§3.

**Uniqueness** (GH's "immediately"). Let `(A, S)` and `(A', S')` witness the
two predicates. Let `E` be the finite set of places where some `P i` or
`P' j` has a non-spherical local component (outside the presentations'
tensor-exceptional sets the reference vectors are fixed by `GL(O_v)`).
For `v ∉ S ∪ S' ∪ E`:

1. `A v` and `A' v` are irreducible and both embed into the restriction of
   `Q` to `GL_(r+1)(F_v)`. That restriction is isotypic (`Q` is admissible by
   `IrreducibleSubquotientAdmissibilityStatement`, Task 6611, and isotypic by
   Flath; candidate `08944adf`'s `LocalComponentEmbeddingStatement`), so
   `A v ≅ A' v`.
2. So `A v` is a spherical irreducible subquotient of both normalized
   inductions, and every `localClass (P i) (h i) v`, `localClass (P' j) (h' j) v`
   is spherical (`LocalRealization.padicClass_isSpherical_iff`).
3. `CuspidalInducingDataRigidityStatement` (proof Task 6447) with the finite set
   `S ∪ S' ∪ E` gives the permutation.

## 6. Not asserted

- anything at the infinite places: the archimedean components of `Q` are not
  related to the archimedean inducing data, and GH Theorem 10.7.1 at every
  place is not stated;
- that `Q` is a constituent of a global induced representation, which is not
  in the Library;
- Langlands' Lemma 1 (either direction), the admissibility of `Q`, or the
  isotypy of its local restrictions;
- that condition 2 of `IsFiniteInducedConstituent` follows from conditions 1
  and 3 (§3);
- that the cuspidal data of the existence statement are of the special form
  `π_i = |det|^(λ_i) π_i^1` with `λ` in a chosen chamber, or any ordering of the
  blocks;
- a cuspidal-support map to `IsobaricData F` (§4);
- groups other than `GL_n`.

## 7. Provenance

The two statements are source statements: the "every automorphic
representation is a constituent" half of GH Theorem 10.7.1 (Langlands'
Proposition 2, "only if") and GH Corollary 10.7.3, for `GL_n`. The predicate
`IsFiniteInducedConstituent` is this formalization's reading of "irreducible
subquotient (constituent) of `I(σ, λ)`" at the finite places, built from
Langlands' Lemma 1 as explained in §3. The following choices belong to this
formalization:

- the cuspidal data are arbitrary cuspidal realizations, with `λ` absorbed
  (§3, as in `CuspidalInducingDataRigidityStatement`);
- "`π_v ≅ π°_v` for almost all `v`" is replaced by "`A v` spherical for almost
  all `v`", as in `CuspidalInducedConstituentAutomorphyStatement`;
- "`π_v` is the local component of `Q`" is replaced by "`A v` embeds into the
  restriction of `Q` to `GL_(r+1)(F_v)`";
- only the finite places are covered;
- the existence statement fixes the factor universe of the presentations to
  `u`; the uniqueness statement uses one factor universe `uQ` for both
  families.

The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. Both
statements are `def`s returning `Prop`, with axioms `propext`,
`Classical.choice`, `Quot.sound`;
`CuspidalSupportExistenceStatement` has universe parameter `u`, and
`CuspidalSupportUniquenessStatement` has universe parameters `u` and `uQ`.
