# Automorphy of isobaric sums of cuspidal representations, at every place

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition and proves nothing:

- `Langlands.Global.CuspidalIsobaricAutomorphyStatement`.

The module is `Langlands.Global.Factors.CuspidalIsobaricAutomorphyStatement`.
The proposition is Getz–Hahn (2024), Theorem 10.7.5, at every place. Take
cuspidal automorphic representations `π_1, …, π_k` of `GL_(n_i)(𝔸_F)` with
`∑ n_i = n`. Then there is an irreducible automorphic representation of
`GL_n(𝔸_F)` that is the isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` at every finite, real
and complex place. "Isobaric sum at every place" is the predicate
`IrreducibleOperatorSubquotient.IsCuspidalIsobaricSum` of the definition
module `Langlands.Global.Factors.IsobaricAutomorphicRepresentation`, which is
part of the same contribution (`IsobaricAutomorphicRepresentation.md` §4).
The statement module imports only that module and defines no instances.
Library vocabulary in the statement itself:

- `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`
  (`Langlands/Automorphic/CuspidalOperatorRealization.lean`);
- `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`);
- `Automorphic.IrreducibleOperatorSubquotient`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`).

**Why it is here.** Getz–Hahn 10.7.5 is in the L4 list of this task's
contract. The Library states it only at the finite places
(`CuspidalIsobaricRealizationStatement`, which says nothing at the infinite
places). This statement adds the real and complex places. It is the
existence half of the isobaric theory whose uniqueness half is
`IsobaricStrongMultiplicityOneStatement` (GH Corollary 11.7.3), in the same
contribution.

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalIsobaricAutomorphyStatement`. Its universe
parameters are `u` (the number field, every local carrier and the
multisegments) and `uQ` (the factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | (10.28)–(10.31), p.283 (PDF 295); Thm 10.6.1, `⊞`, Thm 10.6.2, (10.33), p.284 (PDF 296); Thm 10.6.3, p.285 (PDF 297); "essentially unitary", Thm 10.6.4 and its proof, (10.34), Thm 10.7.1, p.286 (PDF 298); `π_i = \|det\|^(λ_i) π_i^1`, Thm 10.7.5 (10.35) and its proof, Def 10.7.6, p.288 (PDF 300) |
| `knapp-1994-archimedean-llc` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Langlands quotients for `GL_n(ℝ)`, Thm 1, p.400 (PDF 410); for `GL_n(ℂ)`, Thm 4, p.405 (PDF 415); used through the definition module |
| `langlands-1979-notion-automorphic-representation` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | Lemma 1, p.203 (PDF 198); Proposition 2 (constituents of `Ind σ` are automorphic), p.204 (PDF 199); used only for the proof route (§5) |

**What GH state.** On p.288 GH fix cuspidal automorphic representations
`π_i` of `GL_(n_i)(𝔸_F)`, write `π_i(g) = |det g|^(λ_i) π_i^1(g)`, order the
`π_i` by (10.30) and form `I(⊗_(i=1)^k π_i^1, λ)`. "By Theorem 10.7.1 any
irreducible subquotient of this representation is automorphic." Then:

> **Theorem 10.7.5** The representation
> `⊞_(i=1)^k π_i := ⊗'_v (⊞_(i=1)^k π_(iv))` (10.35)
> is an irreducible subquotient of `I(⊗_(i=1)^k π_i^1, λ)`, hence automorphic.

GH's proof: the `π_(iv)` are generic (GH Theorem 11.3.6) and essentially
unitary, so "for all `v`" the local isobaric sum `⊞_i π_(iv)` is an
irreducible subquotient of `I(⊗_i π_(iv)^1, λ)` by Theorem 10.6.4; it is
unramified for almost all `v` by Theorem 10.6.3; the discussion after
Theorem 10.7.1 (Langlands, appendix to [BJ79], Lemma 1) then gives the
theorem. Theorem 10.6.4 (p.286) covers both kinds of local fields: its proof
uses Theorem 8.4.4 when `F` is non-archimedean and Theorem 10.6.2 with
[Jac09, Lemma 2.5] when `F` is archimedean.

## 2. The declaration

`CuspidalIsobaricAutomorphyStatement` says the following. Let:

- `F` be a number field with `[CompactSpace (AdeleQuotient F)]`, the instance
  needed by `CuspidalOperatorRealization`;
- `r, k : ℕ` and `m : Fin k → ℕ` with `∑ i, (m i + 1) = r + 1`;
- `T i : CuspidalOperatorRealization F (m i)`, actual cuspidal realizations of
  `GL_(m i + 1)` over `F`;
- `P i` be spectral presentations of `T i`, with factors in universe `uQ`;
- `h i` say that every finite local component of `P i` is irreducible and
  admissible (`HasIrreducibleAdmissibleComponents`).

Then there is `Q : IrreducibleOperatorSubquotient F r` with
`Q.IsCuspidalIsobaricSum T P h`. Unfolded (`IsobaricAutomorphicRepresentation.md`
§§3–4), with `σ_(i,v)` the canonical local component of `T i` at a finite
place `v`:

1. at every finite place `v` there is an irreducible admissible
   `A : AutomorphicObject.{u, u} (padicField v) r.succPNat` with
   `IsIsobaricSum (fun i => σ_(i,v).obj) A.obj` and an injective intertwining
   map from `A` into the restriction of `Q` to `GL_(r+1)(F_v)`;
2. at every real place `v` there are lists of real blocks `ds i` with
   `(T i).realization.HasRealPlaceParameter v (ds i)` for every `i`, and a
   permutation `ds'` of their concatenation with
   `Q.subquotient.HasRealPlaceLanglandsQuotient v ds'`: the blocks `ds'` are
   in Langlands order (GH (10.30)) and there is a `(𝔤_v, K_v)`-map from the
   `O(r+1)`-finite standard module of `ds'` into `Q` with nonzero irreducible
   image;
3. at every complex place `v`, the same with complex characters,
   `HasComplexPlaceParameter` and `HasComplexPlaceLanglandsQuotient`.

## 3. Hypotheses and conclusion, matched with GH

- **Cuspidal data.** As in `CuspidalIsobaricRealizationStatement` §3: `T i`
  is GH's cuspidal `π_i` of `GL_(n_i)(𝔸_F)` with `n_i = m i + 1` (GH's `π_i`,
  not `π_i^1`, with `λ_i` absorbed), and `σ_(i,v)` is its local component at
  the finite place `v`, read through the presentation `P i`. For `uQ = u` such
  presentations exist for every cuspidal realization
  (`cuspidalIrreducibleAdmissibleFiniteSliceExistence` and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`), so the
  statement is not vacuous.
- **The conclusion.** GH's `⊞_i π_i` is an irreducible automorphic
  representation (Theorem 10.7.5). In the Library it is an
  `IrreducibleOperatorSubquotient F r` (`CuspidalIsobaricRealizationStatement.md`
  §3). Its restriction to each place `v` is a direct sum of copies of
  `⊞_i π_(iv)` (Flath's factorization, background), so it contains
  `⊞_i π_(iv)`. By `IsobaricAutomorphicRepresentation.md` §4, containing
  `⊞_i π_(iv)` at every place is exactly what `IsCuspidalIsobaricSum` says:
  at a finite place through `IsIsobaricSum` (Kudla's segment form), at an
  infinite place through the Langlands quotient `J(ds')` of the ordered union
  of the archimedean blocks of the `π_(iv)`. So the Lean statement follows
  from GH Theorem 10.7.5 and those background facts.
- **The archimedean parameters.** The real-place condition asks for
  parameters `ds i` of the `T i` themselves. For cuspidal `T i` they exist
  and are determined up to the moves of `StandardModule.md` Derived choice 4
  (`IsobaricAutomorphicRepresentation.md` §4, first point), so this is no
  extra condition.
- **The places.** All places are covered: every finite place, every real
  place and every complex place. GH's "irreducible subquotient of
  `I(⊗π_i^1, λ)`" is not stated, since the Library has no global induced
  representation; only "hence automorphic" is, as the existence of `Q`.

## 4. Relation to other statements

- **`CuspidalIsobaricRealizationStatement`** (GH 10.7.5 at the finite places,
  accepted by review). Neither statement implies the other as stated. That
  one adds, at each finite place, that `A` is a subquotient of the normalized
  induced representation `i(σ_(1,v), …, σ_(k,v))` (`IsSubquotientOf`); this
  one drops that condition and adds the real and complex places. Given the
  local fact that a local isobaric sum of generic essentially unitary
  representations is such a subquotient (GH Theorem 10.6.4, background), this
  statement implies that one.
- **`CuspidalArchimedeanParameterExistenceStatement`**
  (`Langlands/Global/Factors/CuspidalPairFunctionalEquationReduction.lean`):
  every actual cuspidal realization has a standard-module parameter at every
  infinite place. Taking `k = 1` and a presentation with irreducible
  admissible components (which exists for `uQ = u`, §3), the real and complex
  conditions of this statement contain that one. So
  `CuspidalIsobaricAutomorphyStatement.{u, u}` implies it. This is not proved
  in Lean.
- **`CuspidalInducedConstituentAutomorphyStatement`** (GH 10.7.1, first
  half, at the finite places; proof Task 6519
  `7853bc94-5997-47b3-a5b2-c1607f7c07c9`): it prescribes the constituents at
  the finite places only, and so gives no control at the infinite places.
- **`IsobaricStrongMultiplicityOneStatement`** (GH Corollary 11.7.3, same
  contribution): if two isobaric `Q` agree at almost all finite places they
  are equivalent. With it, the `Q` of this statement is unique up to
  equivalence. This is not stated here.

## 5. Proof route (for the proof task; not part of the statement)

GH's route, place by place:

- **Finite places.** As for `CuspidalIsobaricRealizationStatement` (proof
  Task 6523 `dab321bc-8fad-40cc-bb66-d16b658b075a`): the local isobaric sum is
  a constituent of `i(σ_(1,v), …, σ_(k,v))` (GH Theorem 10.6.4) and is
  spherical for almost all `v` (GH Theorem 10.6.3).
- **Infinite places.** The parameters `ds i` exist
  (`CuspidalArchimedeanParameterExistenceStatement`, reduced in the Library by
  `cuspidalArchimedeanParameterReduction` to the generic standard-module
  statements and the genericity of cuspidal components). The archimedean case
  of GH Theorem 10.6.4 makes `J(ds')` a constituent of the archimedean induced
  representation `I(⊗_i π_(iv)^1, λ)`.
- **Global step.** Langlands' theorem (GH Theorem 10.7.1; Langlands 1979,
  Proposition 2 and Lemma 1), at all places: a restricted tensor product of
  local constituents, unramified almost everywhere, is a constituent of the
  global induced representation and therefore automorphic. The Library states
  this only at the finite places
  (`CuspidalInducedConstituentAutomorphyStatement`). An all-places form, with
  prescribed `(𝔤_v, K_v)`-constituents at the infinite places, is not in the
  Library; the proof task needs it, or a substitute.

## 6. Not asserted

- that `Q` is a subquotient of the global induced representation
  `I(⊗π_i^1, λ)`, which is not in the Library;
- that `A` is a subquotient of the local induced representation (this is in
  `CuspidalIsobaricRealizationStatement`, not here);
- uniqueness of `Q`, of `A`, of the parameters `ds i` or of `ds'`;
- admissibility of `Q`, or that its restriction to a place is isotypic;
- independence of the local components from the presentations;
- presentations in a universe `uQ ≠ u`.

## 7. Provenance

This is a source statement: GH Theorem 10.7.5. The following choices belong
to this formalization:

- `⊞_i π_i ≅ Q` is replaced by `Q.IsCuspidalIsobaricSum T P h`, the
  containment of the local isobaric sums at every place, with the
  conventions of the definition module (`IsobaricAutomorphicRepresentation.md`
  §7);
- "an irreducible subquotient of `I(⊗π_i^1, λ)`, hence automorphic" is
  replaced by the existence of an irreducible automorphic operator
  subquotient `Q`;
- the cuspidal data are arbitrary cuspidal realizations with `λ` absorbed,
  read through spectral presentations (as in
  `CuspidalIsobaricRealizationStatement`).

The Lean files were checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
declaration is a `def` returning `Prop`, with universe parameters `u` and
`uQ`.
