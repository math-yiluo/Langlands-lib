# Cuspidal support of automorphic representations of `GL_n`, at every place

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** The module `Langlands.Global.Factors.CuspidalSupportEveryPlaceStatement`
defines four predicates and states four propositions. It proves nothing.

- `Langlands.Automorphic.OperatorSubquotient.HasRealPlaceStandardConstituent`
  and `HasComplexPlaceStandardConstituent`: at one real or complex place, an
  automorphic operator subquotient contains an irreducible subquotient of the
  standard module of a given list of archimedean blocks.
- `Langlands.Global.IsInducedConstituent`: an irreducible automorphic operator
  subquotient `Q` of `GL_(r+1)` is a constituent, at every place, of the
  representation induced from given cuspidal data. At the finite places this
  is the published `IsFiniteInducedConstituent`.
- `Langlands.Automorphic.IrreducibleOperatorSubquotient.HasCuspidalSupport`:
  `Q` has a given multiset of cuspidal classes, an element of
  `IsobaricData F`, as cuspidal support.
- `Langlands.Global.CuspidalSupportEveryPlaceStatement`: every irreducible
  automorphic operator subquotient is an induced constituent, at every place,
  of some cuspidal data. This is the second half of Getz–Hahn (2024),
  Theorem 10.7.1, with Langlands' description of the constituents (the remark
  after it), at every place.
- `Langlands.Global.CuspidalSupportDataStatement`: every irreducible
  automorphic operator subquotient has exactly one cuspidal support in
  `IsobaricData F`. This is Getz–Hahn (2024), Theorem 10.7.1 with Corollary
  10.7.3 and the sentence after it.
- `Langlands.Global.CuspidalSupportDataReductionStatement`: the previous
  statement follows from the existence statement and the published
  finite-place uniqueness `CuspidalSupportUniquenessStatement`.
- `Langlands.Global.CuspidalIsobaricSupportStatement`: an isobaric sum of
  cuspidal realizations is an induced constituent, at every place, of the same
  cuspidal data. This is the first assertion of Getz–Hahn (2024), Theorem
  10.7.5.

The module also defines six `local instance`s. They give the form spaces and
the realization carriers (`RationalInvariantFunctions`,
`ContinuousRationalFunctions`, `FiniteSmoothRationalFunctions`,
`AutomorphicForms`, `StableAutomorphicFunctions`, `OperatorRealization.Space`)
their additive group structures as submodules (`Submodule.addCommGroup`), as
in `Langlands/Automorphic/ArchimedeanPlaceParameter.lean`. Everything else is
Library vocabulary:

- `OperatorSubquotient.realPlaceCompactRepresentation` and
  `complexPlaceCompactRepresentation`
  (`Langlands/Automorphic/OperatorSubquotientPlaceAction.lean`),
  `OperatorSubquotient.realPlaceLieAction` and `complexPlaceLieAction`
  (`Langlands/Automorphic/OperatorSubquotientLieAction.lean`);
- `realStandardKFinite`, `complexStandardKFinite`,
  `OperatorRealization.HasRealPlaceParameter` and `HasComplexPlaceParameter`
  (`Langlands/Automorphic/ArchimedeanPlaceParameter.lean`);
- `LocalFactor.Archimedean.RealBlock` and `realRank`
  (`Langlands/LocalFactor/ArchimedeanPresentation.lean`),
  `ComplexCharacterData` (`Langlands/LocalFactor/ArchimedeanAttachment.lean`);
- `Archimedean.unitaryCompact` and `Archimedean.matrixModel`
  (`Langlands/Representation/Archimedean/GeneralLinear.lean`),
  `Archimedean.rightDerivative`
  (`Langlands/Representation/Archimedean/StandardModule.lean`),
  `Whittaker.rightTranslation`
  (`Langlands/Representation/Whittaker/Algebraic.lean`);
- `IsFiniteInducedConstituent` and `CuspidalSupportUniquenessStatement`
  (`Langlands/Global/Factors/CuspidalSupportStatement.lean`);
- `IrreducibleOperatorSubquotient.IsCuspidalIsobaricSum`
  (`Langlands/Global/Factors/IsobaricAutomorphicRepresentation.lean`);
- `IsobaricData` (`Langlands/Automorphic/IsobaricData.lean`),
  `PositiveRankCuspidalClass` and `CuspidalOperatorRealization.isoClass`
  (`Langlands/Automorphic/CuspidalOperatorRealization.lean`);
- `CuspidalSpectralPresentation`
  (`Langlands/Automorphic/CuspidalSpectralPresentation.lean`) and
  `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`);
- `Automorphic.IrreducibleOperatorSubquotient`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`).

**Why it is here.** L4 of this task's contract asks for the isobaric theory of
Getz–Hahn §10.7. The program ledger `notes/automorphic/global-program-coverage.md`
(section "14 November 2026 local components, absolute convergence, archimedean
Theorem 11.5.2, cuspidal support", list of remaining L4 targets) lists as
missing statements "GH Theorem 10.7.1 at every place" and "the cuspidal-support
map from irreducible automorphic subquotients to `IsobaricData F`".
`CuspidalSupportStatement.md` §6 records that the published
`CuspidalSupportExistenceStatement` says nothing at the infinite places and
that it defines no cuspidal-support map. The Library states GH Theorem 10.7.5
at every place as the existence of an isobaric sum
(`CuspidalIsobaricAutomorphyStatement`), but not that the isobaric sum is a
constituent of the induced representation.

**Proof targets.** Later proof tasks should prove the Library statements
`Langlands.Global.CuspidalSupportEveryPlaceStatement`,
`Langlands.Global.CuspidalSupportDataStatement` and
`Langlands.Global.CuspidalSupportDataReductionStatement` (universe parameter
`u`), and `Langlands.Global.CuspidalIsobaricSupportStatement` (universe
parameters `u` and `uQ`). `u` is the universe of the number field and of every
local carrier; `uQ` is the factor universe of the spectral presentations.

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | essentially unitary representations, Thm 10.6.4 and its proof, p.286 (PDF 298); (10.34), Thm 10.7.1 and the remark on Lemma 1, pp.286–287 (PDF 298–299); Thm 10.7.2, Cor 10.7.3 and the sentence after it, p.287 (PDF 299); `π_i = \|det\|^(λ_i) π_i^1`, Thm 10.7.5, (10.35) and its proof, p.288 (PDF 300) |
| `getz-hahn-2024-errata-2026-10` | `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2` | pp.2–3 (PDF 2–3): the entries pass from Chapter 9 to Chapter 11; none concerns Chapter 10 |
| `langlands-1979-notion-automorphic-representation` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | `Ind σ`, constituents, `π°_v`, Lemma 1, p.203 (PDF 198); Prop 2, p.204 (PDF 199) |
| `badulescu-renard-2010-unitary-dual` | `ceb97805d7a6270ddb5dc11255d84fcad9e11f1a06705ddf69c1c3a0a8da416f` (registered folder) | `M(G)`, `R(G)`, standard parabolics, normalized induction `i_(n_1,…,n_s)`, Def 2.2 and Remark 2.3, p.1123 (PDF 10); Prop 2.4, p.1124 (PDF 11) |
| `zelevinsky-1980-induced-ii` | `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` | Thm 1.9, p.174 (PDF 11) |
| `knapp-1994-archimedean-llc` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Thm 1, p.400 (PDF 410); Thm 4, p.405 (PDF 415); as summarized in `IsobaricAutomorphicRepresentation.md` §1 |

The Langlands paper is in the Corvallis volume, Part I, whose printed page is
the PDF page plus 5. Badulescu–Renard is registered as a folder; the pages
are those of its journal PDF (SHA-256
`a20178a93ca053f71ecbcd16ad779b74f597169b71208621c6173da2af808c8b`), whose
printed page is the PDF page plus 1113. Mœglin–
Waldspurger 1989, §1.2(3), and Jacquet 2009, Lemma 2.5, enter only through GH's
proof of Theorem 10.6.4 and were not read for this module. Flath's
factorization theorem is used only as background, as in
`IsobaricAutomorphicRepresentation.md` §§1, 4 and
`OperatorSubquotientLocalComponentStatement.md`.

**What the sources state.** GH p.286 (§10.6, local): with `λ_i` as in (10.29)
and ordered as in (10.30), an irreducible admissible `π_i` is *essentially
unitary* if `π_i^1` is unitary, and

> **Theorem 10.6.4** If `π_i` is an essentially unitary generic representation
> for `1 ≤ i ≤ k` then `⊞_(i=1)^k π_i` is a subquotient of
> `I(⊗_(i=1)^k π_i^1, λ)`.

The proof shows that each unitary generic representation is an `I(σ, λ)` with
`σ` square integrable on a Levi subgroup and then cites [MW89, §1.2(3)].

GH pp.286–287 (§10.7, global): "Given a cuspidal automorphic representation
`σ` of `M(𝔸_F)`, we form the induced representation `I(σ, λ)` (10.34) as in
(10.1)."

> **Theorem 10.7.1 (Langlands)** Any irreducible subquotient of `I(σ, λ)` is
> an automorphic representation, and every automorphic representation is of
> this form.

GH continue: "in [BJ79, Appendix, Lemma 1] Langlands observes that the
subquotients of `I(σ, λ)` can be described as follows. For all but finitely
many `v` the representation `σ_v` is unramified and `I(σ_v, λ)` has a unique
irreducible unramified subquotient `π°_v`. The irreducible subquotients of
`I(σ, λ)` are the representations of the form `⊗'_v π_v`, where `π_v` is an
irreducible subquotient of `I(σ_v, λ)` for all `v` and `π_v ≅ π°_v` for almost
every `v`." In this remark, as in Langlands' Lemma 1 below, the tensor
product runs over all places, the infinite ones included.

GH p.287 states Theorem 10.7.2 ([JS81a, Theorem 4.4]) and then:

> "This immediately implies the following corollary:
>
> **Corollary 10.7.3** If `π` is an irreducible subquotient of `I(σ, λ)` and
> `I(σ', λ')` then the conclusion of Theorem 10.7.2 holds.
>
> Thus every automorphic representation of `GL_n(𝔸_F)` is a subquotient of
> `I(σ, λ)`, where `σ` and `λ` are unique up to a permutation in the sense made
> precise in Theorem 10.7.2."

The conclusion of Theorem 10.7.2 is: `k = k'` and there is a permutation `τ`
of the set of `k` elements with `σ_i ≅ σ'_(τ(i))` and `λ_i = λ'_(τ(i))`.

GH p.288: for cuspidal `π_i` of `GL_(n_i)(𝔸_F)`, `π_i^1` is the unique cuspidal
representation of `A_(GL_(n_i)) \ GL_(n_i)(𝔸_F)` with
`π_i(g) = |det g|^(λ_i) π_i^1(g)`; "After rearranging the `π_i` we can assume
(10.30) holds." With `P` of type `(n_1, …, n_k)` and `λ = (λ_1, …, λ_k)`:

> **Theorem 10.7.5** The representation `⊞_(i=1)^k π_i := ⊗'_v (⊞_(i=1)^k π_(iv))`
> (10.35) is an irreducible subquotient of `I(⊗_(i=1)^k π_i^1, λ)`, hence
> automorphic.

Proof (GH p.288): the `π_(iv)` are generic and essentially unitary, so for all
`v` the representation `⊞_i π_(iv)` is an irreducible subquotient of
`I(⊗_i π_(iv)^1, λ)` by Theorem 10.6.4, "and it is unramified for all but
finitely many `v` by Theorem 10.6.3"; the discussion after Theorem 10.7.1
finishes the proof.

Langlands p.203: for a parabolic `P` with Levi factor `M` and a cuspidal
`σ = ⊗σ_v` of `M(𝔸)`, `Ind σ = ⊗_v Ind σ_v`; "an irreducible subquotient of
this representation is said to be a constituent of it".

> LEMMA 1. The constituents of `Ind σ` are the representations `π = ⊗π_v`
> where `π_v` is a constituent of `Ind σ_v` and `π_v = π°_v` for almost all `v`.

P.204:

> PROPOSITION 2. A representation `π` of `G(𝔸)` is an automorphic
> representation if and only if `π` is a constituent of `Ind σ` for some `P`
> and some `σ`.

Badulescu–Renard p.1123: `M(G)` is the category of smooth representations
(non-archimedean `F`) or of Harish-Chandra modules with respect to `O(n)`,
`U(n)` (archimedean `F`); `R(G)` is the Grothendieck group of its finite-length
objects, "the free `ℤ`-module with basis `Irr(G)`". `i_(n_1,…,n_s)` is
normalized parabolic induction from the standard parabolic generated by the
block-diagonal subgroup and the upper triangular Borel subgroup.
Definition 2.2: `π_1 × π_2 := i_(n_1,n_2)(π_1 ⊗ π_2)`, extended to a product on
`R = ⊕_n R(G_n)`. Remark 2.3: "`π_1 × π_2 = π_2 × π_1` in `R` (see below), but
`i_(n_1,n_2)(π_1 ⊗ π_2)` is not isomorphic to `i_(n_1,n_2)(π_2 ⊗ π_1)` in
general." P.1124, Proposition 2.4: "The ring `(R, ×)` is graded commutative."

Zelevinsky p.174, Theorem 1.9: the ring `R` of `p`-adic `GL_n` is commutative;
for representations `π_1`, `π_2` of finite length, `π_1 × π_2` and `π_2 × π_1`
have the same composition factors.

## 2. The declarations

Throughout, `F` is a number field. For the archimedean predicates,
`Q : OperatorSubquotient F n`; elsewhere `[CompactSpace (AdeleQuotient F)]` is
assumed, as needed by `CuspidalOperatorRealization`, and
`Q : IrreducibleOperatorSubquotient F r`.

**`HasRealPlaceStandardConstituent Q v ds`**, for a real place `v` and a list
`ds : List RealBlock`, says:

1. `realRank ds = n`;
2. there is a `ℂ`-subspace `W` of the functions `GL_n(ℝ) → ℂ` with
   `W ≤ realStandardKFinite n ds`, the `O(n)`-finite functions of the
   Library's standard module of `ds`;
3. there is a `ℂ`-linear map `A : W →ₗ[ℂ] Q.Space` such that
   - for `k ∈ O(n)` (as an element of `Archimedean.unitaryCompact ℝ n`) and
     `f ∈ W`, the right translate of `f` by `k` lies in `W` and `A` sends it to
     `Q.realPlaceCompactRepresentation v k (A f)`;
   - for `X ∈ 𝔤𝔩_n(ℝ)` and `f ∈ W`, the right derivative of `f` along `X` lies
     in `W` and `A` sends it to `Q.realPlaceLieAction v (1 ⊗ X) (A f)`;
4. the range of `A` is nonzero;
5. every `ℂ`-subspace `U` of the range of `A` that is stable under the compact
   action at `v` of all of `O(n)` and under the Lie action at `v` of all real
   `X` is `0` or the whole range.

This is `HasRealPlaceLanglandsQuotient` (`IsobaricAutomorphicRepresentation.lean`)
with two changes: the domain of `A` is a subspace `W` of the `O(n)`-finite
functions, stable under right translation by `O(n)` and right differentiation,
instead of all of them; and there is no order condition on `ds`.
`HasComplexPlaceStandardConstituent Q v ds`, for a complex place `v` and
`ds : List ComplexCharacterData`, is the same with `ds.length = n`,
`complexStandardKFinite n ds`, `U(n)` and real directions `X ∈ 𝔤𝔩_n(ℂ)`, with
`F_v` identified with `ℂ` as in the published place actions.

Cuspidal data are, as in `CuspidalSupportStatement.md` §2: `k : ℕ`,
`m : Fin k → ℕ`, `hm : ∑ i, (m i + 1) = r + 1`, actual cuspidal realizations
`T i : CuspidalOperatorRealization F (m i)`, spectral presentations
`P i : CuspidalSpectralPresentation (T i)`, and
`h i : HasIrreducibleAdmissibleComponents (P i)`.

**`IsInducedConstituent hm P h Q`** is the conjunction of

1. `IsFiniteInducedConstituent hm P h Q` (`CuspidalSupportStatement.md` §2);
2. for every real place `v` there are `ds : Fin k → List RealBlock` with
   `(T i).realization.HasRealPlaceParameter v (ds i)` for every `i` and
   `Q.subquotient.HasRealPlaceStandardConstituent v (List.ofFn ds).flatten`,
   where `(List.ofFn ds).flatten` is the concatenation
   `ds 0 ++ ds 1 ++ ⋯ ++ ds (k-1)`;
3. the same at every complex place `v`, with
   `ds : Fin k → List ComplexCharacterData`, `HasComplexPlaceParameter` and
   `HasComplexPlaceStandardConstituent`.

**`Q.HasCuspidalSupport D`**, for `D : IsobaricData F`, holds when there are
cuspidal data `(k, m, hm, T, P, h)`, with presentations in factor universe
`uQ`, such that `IsInducedConstituent hm P h Q` and
`Finset.univ.val.map (fun i => ⟨m i, (T i).isoClass⟩) = D`: the multiset of
the positive-rank cuspidal classes `⟨m i, [T i]⟩`, `i : Fin k`, counted with
multiplicity, is `D`. The definition has universe parameters `u` and `uQ`.

**`CuspidalSupportEveryPlaceStatement`**: for every `F`, every `r` and every
`Q : IrreducibleOperatorSubquotient F r` there are `k`, `m`, `hm`, `T`,
presentations `P i : CuspidalSpectralPresentation.{u, u} (T i)` and `h` with
`IsInducedConstituent hm P h Q`.

**`CuspidalSupportDataStatement`**: for every `F`, every `r` and every
`Q : IrreducibleOperatorSubquotient F r` there is exactly one
`D : IsobaricData F` with `Q.HasCuspidalSupport.{u, u} D`.

**`CuspidalSupportDataReductionStatement`**:
`CuspidalSupportEveryPlaceStatement.{u}` and
`CuspidalSupportUniquenessStatement.{u, u}` together imply
`CuspidalSupportDataStatement.{u}`.

**`CuspidalIsobaricSupportStatement`**: for every `F`, all cuspidal data
`(k, m, hm, T, P, h)` of total rank `r + 1` with presentations in factor
universe `uQ`, and every `Q : IrreducibleOperatorSubquotient F r`,
`Q.IsCuspidalIsobaricSum T P h` implies `IsInducedConstituent hm P h Q`.

## 3. Matching with the sources

- **Automorphic representations, cuspidal data, `λ` and the finite places.**
  As in `CuspidalSupportStatement.md` §3: an `IrreducibleOperatorSubquotient F r`
  is an automorphic representation of `GL_(r+1)(𝔸_F)` in the sense of
  Borel–Jacquet §4.6; GH's `(σ, λ)` with `σ = ⊗_i π_i^1` and the cuspidal
  realizations `T i` determine each other (GH p.288); and
  `IsFiniteInducedConstituent` is "`Q` is a constituent of `I(σ, λ)`" read at
  the finite places through Langlands' Lemma 1.
- **Standard constituents.** In `HasRealPlaceStandardConstituent`, the
  conditions on `W` say that `W` is a `(𝔤, K)`-submodule of the `(𝔤, K)`-module
  `I(ds)_K` of `K`-finite vectors of the standard module, `K = O(n)`.
  Since `A` is equivariant, `ker A` is a submodule of `W`, and the range of `A`
  is a `(𝔤_v, K_v)`-submodule of `Q`, isomorphic to `W / ker A`; conditions 4–5
  say that it is irreducible. So the predicate says: some irreducible
  subquotient of `I(ds)_K` is isomorphic to a `(𝔤_v, K_v)`-submodule of `Q`.
  Conversely, given `(𝔤, K)`-submodules `W' ⊆ W` of `I(ds)_K` with `W / W'`
  irreducible and an embedding `W / W' → Q`, the composition
  `A : W → W / W' → Q` satisfies the predicate. If `Q` is admissible, Flath's
  factorization makes the restriction of `Q` to `(𝔤_v, K_v)` isotypic of type
  `Q_v` (background, as in `IsobaricAutomorphicRepresentation.md` §4), and the
  predicate says that `Q_v` is a constituent of `I(ds)` in Langlands' sense.
  None of this is proved here.
- **The induced representation at an infinite place.** Fix a real place `v`.
  By GH p.288 and `CuspidalSupportStatement.md` §3, the factor at `v` of GH's
  normalized `I(σ, λ)` is the normalized induction of `⊗_i π_(iv)` from the
  standard parabolic of type `(m 0 + 1, …, m (k-1) + 1)`, where `π_(iv)` is the
  component of `T i` at `v`. Background facts, used only in this explanation:
  - For a parameter `ds i` of the cuspidal `T i` at `v`, the standard module
    `I(ds i)` is irreducible and isomorphic to `π_(iv)`
    (`IsobaricAutomorphicRepresentation.md` §4, first bullet; the Library
    states the irreducibility as `CuspidalArchimedeanStandardIrreducibleStatement`,
    not proved).
  - The Library's standard module of a list of blocks is realized inside the
    principal series from the upper triangular Borel subgroup by normalized
    induction in stages (`StandardModule.md`, Derived choices 1 and 7), with
    the blocks placed along the diagonal in list order. The same
    identification `Ind_Q^G(Ind_(B∩D)^D χ) ≅ Ind_B^G χ`, applied to the block
    parabolic of type `(m 0 + 1, …)` and the Levi factor
    `∏_i GL_(m i + 1)(ℝ)`, identifies the normalized induction of
    `⊗_i I(ds i)` with `I(ds 0 ++ ⋯ ++ ds (k-1))`.

  So `I(σ_v, λ)` is `I((List.ofFn ds).flatten)`, and condition 2 of
  `IsInducedConstituent` says that `Q` contains at `v` a constituent of
  `I(σ_v, λ)`. If `Q` is admissible, this is "`Q_v` is a constituent of
  `Ind σ_v`" of Langlands' Lemma 1. The complex places are the same with
  characters of `GL_1(ℂ)` as blocks (Knapp Theorem 4).
- **The order of the blocks.** The blocks are concatenated in the index order
  of `i : Fin k`, matching the standard upper block parabolic of
  `canonicalNormalizedProductInduced` at the finite places. GH's Theorem
  10.7.1 allows any cuspidal `σ` on the Levi factor of a standard parabolic,
  so any order. Theorem 10.7.5 uses the order (10.30). The constituents do not
  depend on the order: induced representations of the same blocks in
  different orders have the same image in the Grothendieck group, hence the
  same composition factors (Badulescu–Renard Remark 2.3 and Proposition 2.4
  at the archimedean places, Zelevinsky Theorem 1.9 at the finite places).
  This is background and is not asserted.
- **The parameters are existential.** Condition 2 asks for some parameters
  `ds i` of the `T i` at `v`. For cuspidal `T i` they exist
  (`CuspidalArchimedeanParameterExistenceStatement`, Task 5720, not proved)
  and are determined up to permutation, the sign of the weight of an
  induction block and the splitting of a weight-zero block
  (`IsobaricAutomorphicRepresentation.md` §4). These moves do not change the
  composition factors of `I((List.ofFn ds).flatten)`, by the previous bullet
  and `StandardModule.md` Derived choice 4. So the condition does not depend on
  the choice (background, not asserted).
- **Existence at every place.** `CuspidalSupportEveryPlaceStatement` is GH
  Theorem 10.7.1, "every automorphic representation is of this form", read
  through Langlands' description of the constituents at all places (GH's
  remark after 10.7.1, Langlands' Lemma 1), with the reading of the previous
  bullets; it is also Langlands' Proposition 2, "only if", for
  `G = GL_(r+1)`. As in `CuspidalSupportExistenceStatement`, the
  presentations are asked for in factor universe `u`.
- **Cuspidal support.** By `CuspidalSupportStatement.md` §3 (bullet
  "Uniqueness"), the class `⟨m i, (T i).isoClass⟩` of `PositiveRankCuspidalClass F`
  records GH's `(σ_i, λ_i)`, and two families of cuspidal data agree "up to a
  permutation in the sense made precise in Theorem 10.7.2" exactly when their
  multisets of classes are equal. So `Q.HasCuspidalSupport D` says that `Q` is
  a constituent, at every place, of `I(σ, λ)` for cuspidal data with multiset
  of classes `D`, and `CuspidalSupportDataStatement` is the sentence after GH
  Corollary 10.7.3: `σ` and `λ` exist and are unique up to permutation. The
  multiset `D` is an element of the Library type `IsobaricData F`, which
  consists of the finite multisets of positive-rank cuspidal classes.
- **Isobaric sums.** By `IsobaricAutomorphicRepresentation.md` §4,
  `Q.IsCuspidalIsobaricSum T P h` is the Library's reading of
  "`Q ≅ ⊞_i π_i` (10.35)" at every place, and `IsInducedConstituent hm P h Q`
  is "`Q` is a constituent, at every place, of `I(⊗_i π_i^1, λ)`" by the
  bullets above. So `CuspidalIsobaricSupportStatement` is the first assertion
  of GH Theorem 10.7.5. The hypothesis `hm` is GH's `∑ n_i = n`; GH's
  rearrangement into the order (10.30) is not needed, by the bullet on the
  order. The second condition of `IsFiniteInducedConstituent` (a spherical
  vector outside a finite set) is GH's "unramified for all but finitely many
  `v` by Theorem 10.6.3".
- **Universes.** `CuspidalSupportDataStatement` and the reduction use
  presentations in factor universe `u`, the universe of the existence
  statement and of the instance `CuspidalSupportUniquenessStatement.{u, u}`.
  `CuspidalIsobaricSupportStatement` allows any factor universe `uQ`, as
  `IsCuspidalIsobaricSum` does.

## 4. Relation to other statements

- **`CuspidalSupportExistenceStatement`** (`CuspidalSupportStatement.lean`).
  Condition 1 of `IsInducedConstituent` is `IsFiniteInducedConstituent`, so
  `CuspidalSupportEveryPlaceStatement.{u}` implies
  `CuspidalSupportExistenceStatement.{u}` by projection. This implication is
  not stated in Lean.
- **`CuspidalSupportUniquenessStatement`.** It is a hypothesis of
  `CuspidalSupportDataReductionStatement`. Since `IsInducedConstituent`
  contains `IsFiniteInducedConstituent`, uniqueness at the finite places
  already determines the cuspidal support; nothing at the infinite places is
  needed for it.
- **`CuspidalInducedConstituentAutomorphyStatement`** is the first half of GH
  Theorem 10.7.1 at the finite places. The first half at every place (every
  constituent of `I(σ, λ)` is automorphic) is not stated here.
- **`CuspidalIsobaricAutomorphyStatement`** (GH Theorem 10.7.5 at every place,
  existence) gives, for cuspidal data with `hm`, some `Q` with
  `Q.IsCuspidalIsobaricSum T P h`. With `CuspidalIsobaricSupportStatement`, such
  a `Q` is an induced constituent of the data, so
  `Q.HasCuspidalSupport D` holds for `D` the multiset of the classes of the
  `T i`, directly from the definition of `HasCuspidalSupport`.
- **`IrreducibleOperatorSubquotient.IsIsobaric`** (GH Definition 10.7.6). By
  `CuspidalIsobaricSupportStatement`, an isobaric `Q` has as cuspidal support
  the multiset of the classes of its summands. With
  `CuspidalSupportDataStatement` (factor universe `u`), these summands are
  determined up to permutation by `Q`. Neither consequence is stated in
  Lean.
- **`CuspidalArchimedeanComponentStatement`** states that the standard module
  of a given parameter of a cuspidal realization is irreducible, generic and,
  under a unitary central character, unitarizable. These are archimedean
  inputs for the proof routes in §5.
- **`OperatorSubquotientLocalComponentStatement`** states the isotypy of the
  local restrictions of jointly admissible `Q`, at every place. It is the
  background used in §3 to read the archimedean predicates as statements
  about `Q_v`. This module does not import it.

## 5. Proof routes (for the proof tasks; not part of the statements)

**Existence at every place** (deep). Langlands' proof (pp.204–205,
summarized in `CuspidalSupportStatement.md` §5) realizes `π ≅ Q` as a quotient
of a space `V'` of functions in the global induced representation
`Ind δ^(-1) σ`, through constant terms along the parabolic `P_φ` chosen there.
The constant-term map commutes with `GL_(r+1)(𝔸_f)`, `K_∞` and the Lie
algebra, so it relates `Q` and the induced representation at all places at
once. At a real place `v` the proof task has to supply:

1. parameters `ds i` of the cuspidal blocks at `v`
   (`CuspidalArchimedeanParameterExistenceStatement`), whose standard modules
   are their components at `v` (`CuspidalArchimedeanStandardIrreducibleStatement`
   and the isotypy of the restriction of `T i` to `(𝔤_v, K_v)`);
2. the identification, by normalized induction in stages, of the
   `(𝔤_v, K_v)`-module of the induced representation at `v` with
   `I((List.ofFn ds).flatten)_K` (`StandardModule.md`, Derived choice 1);
3. the passage from the global realization of `Q` to a `(𝔤_v, K_v)`-subquotient
   `W / ker A` of `I((List.ofFn ds).flatten)_K` inside `Q`, for instance by
   Langlands' Lemma 1 together with Flath's factorization and the isotypy of
   the restrictions of `Q` (`OperatorSubquotientLocalComponentStatement`).

The finite-place part is `CuspidalSupportExistenceStatement`, but the proof
must produce one family of cuspidal data that works at all places at once.

**Reduction** (short). Existence: `CuspidalSupportEveryPlaceStatement.{u}`
gives cuspidal data, which witness `HasCuspidalSupport.{u, u}` for their own
multiset of classes. Uniqueness: let `D` and `D'` be cuspidal supports of
`Q`, with witnesses `(k, m, hm, T, P, h)` and `(k', m', hm', T', P', h')`.
Condition 1 of both `IsInducedConstituent`s and
`CuspidalSupportUniquenessStatement.{u, u}` give `e : Fin k ≃ Fin k'` with
`⟨m i, (T i).isoClass⟩ = ⟨m' (e i), (T' (e i)).isoClass⟩`. Then
`D = univ.val.map (f' ∘ e) = (univ.val.map e).map f' = D'`, by
`Multiset.map_map` and Mathlib's `Multiset.map_univ_val_equiv`
(`Mathlib/Data/Fintype/Basic.lean`).

**Isobaric sums.** Finite places: the representation `A v` of
`IsCuspidalIsobaricSum` is `⊞_i σ_(i,v)` (`IsobaricSum.md` §3). It is a
subquotient of the normalized induction in GH's order (10.30) by GH Theorem
10.6.4, and so of the induction in index order by Zelevinsky Theorem 1.9.
Outside a finite set `S` containing the exceptional sets of the presentations,
every `σ_(i,v)` is unramified (as in `CuspidalSupportStatement.md` §5), and so is `⊞_i σ_(i,v)` (GH Theorem 10.6.3). Real
places: the hypothesis gives parameters `ds i` and a permutation `ds'` of the
concatenation with `HasRealPlaceLanglandsQuotient Q v ds'`. Use the same
`ds i`. The image `J` of the Langlands-quotient map is an irreducible quotient
of `I(ds')_K`. `I(ds')` and `I((List.ofFn ds).flatten)` are products of the
same block classes in `R(GL_n(ℝ))`, so by Badulescu–Renard Proposition 2.4 they
have the same composition factors, with multiplicities. Standard modules have
finite length. So `J` is isomorphic to a subquotient `W / W'` of
`I((List.ofFn ds).flatten)_K`, and `A : W → W / W' ≅ J ⊆ Q` satisfies
`HasRealPlaceStandardConstituent`. The complex places are the same.

## 6. Not asserted

- the first half of GH Theorem 10.7.1 at the infinite places, that every
  constituent of `I(σ, λ)` is automorphic (§4);
- Langlands' Lemma 1, Flath's factorization, the admissibility of `Q` or the
  isotypy of its local restrictions;
- that the standard module of a parameter of a cuspidal realization is
  irreducible or is its archimedean component, or that parameters exist;
- that the predicates do not depend on the order of the blocks or on the
  choice of the parameters (§3);
- that `Q` is a constituent of a global induced representation, which is not
  in the Library;
- that the rank `D.rank` of a cuspidal support equals `r + 1` (it follows from
  `hm`; not stated);
- that `Q` is determined by its cuspidal support, or which constituent with a
  given support is isobaric; the converse of `CuspidalIsobaricSupportStatement`;
- groups other than `GL_n`.

## 7. Provenance

`CuspidalSupportEveryPlaceStatement`, `CuspidalSupportDataStatement` and
`CuspidalIsobaricSupportStatement` are source statements: the "every
automorphic representation is of this form" half of GH Theorem 10.7.1 with
Langlands' Lemma 1 (Langlands' Proposition 2, "only if"), the sentence after GH
Corollary 10.7.3, and the first assertion of GH Theorem 10.7.5, all for
`GL_n` and at every place. `CuspidalSupportDataReductionStatement` is derived:
it splits the second statement into the published finite-place uniqueness
(GH Corollary 10.7.3) and the new existence statement. The four predicates
are this formalization's reading of "constituent at `v`", "constituent of
`I(σ, λ)`" and "cuspidal support", explained in §3. The following choices
belong to this formalization:

- at an infinite place, "`π_v` is a constituent of `I(σ_v, λ)`" is replaced by
  "`Q` contains at `v` an irreducible subquotient of the standard module of
  the concatenated parameters", without identifying a local component of `Q`;
- the inducing data at an infinite place are read through existential
  standard-module parameters of the cuspidal realizations;
- the blocks are concatenated in index order, matching the finite places;
- the cuspidal support is a multiset of positive-rank cuspidal classes, the
  Library's `IsobaricData F`, with `λ` absorbed into the classes as in
  `CuspidalSupportStatement.md`;
- `CuspidalSupportEveryPlaceStatement` and `CuspidalSupportDataStatement` fix
  the factor universe of the presentations to `u`;
  `CuspidalIsobaricSupportStatement` allows any `uQ`.

The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The four
statements are `def`s returning `Prop`, with axioms `propext`,
`Classical.choice`, `Quot.sound`. `CuspidalSupportEveryPlaceStatement`,
`CuspidalSupportDataStatement` and `CuspidalSupportDataReductionStatement`
have universe parameter `u`; `CuspidalIsobaricSupportStatement` has universe
parameters `u` and `uQ`.
