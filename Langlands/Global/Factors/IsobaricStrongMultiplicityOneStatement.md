# Strong multiplicity one for isobaric automorphic representations of `GL_n`

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition and proves nothing:

- `Langlands.Global.IsobaricStrongMultiplicityOneStatement`.

The module is `Langlands.Global.Factors.IsobaricStrongMultiplicityOneStatement`.
The proposition is Getz–Hahn (2024), Corollary 11.7.3: two isobaric automorphic
representations of `GL_n(𝔸_F)` whose local components agree outside a finite
set of places are isomorphic. "Isobaric" is the predicate
`IrreducibleOperatorSubquotient.IsIsobaric` (GH Definition 10.7.6) of the
definition module `Langlands.Global.Factors.IsobaricAutomorphicRepresentation`,
which is part of the same contribution (`IsobaricAutomorphicRepresentation.md`
§5). The statement module defines one `local instance`: the canonical
topology on `GL_n(F_v)`, the one of the correspondence category
`AutomorphicObject (padicField v)`, as in
`CuspidalIsobaricRealizationStatement`. Library vocabulary in the statement
itself:

- `Automorphic.IrreducibleOperatorSubquotient` and its `Equivalence`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`);
- `OperatorSubquotient.localRepresentation`
  (`Langlands/Automorphic/OperatorSubquotient.lean`);
- `Correspondence.AutomorphicObject`
  (`Langlands/Correspondence/AutomorphicRelations.lean`).

**Why it is here.** GH Corollary 11.7.3 is an L4 target of this task's
contract. The program ledger `notes/automorphic/global-program-coverage.md`
lists it as unstated in representation form; the Library has only its
numerical counterpart `CuspidalSpectralRigidityStatement` (§4).

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.IsobaricStrongMultiplicityOneStatement`. Its universe
parameters are `u` (the number field and every local carrier) and `uQ` (the
factor universe of the spectral presentations inside `IsIsobaric`).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | Thm 10.6.3, p.285 (PDF 297); Thm 10.6.4, p.286 (PDF 298); Thm 10.7.2, p.287 (PDF 299); Def 10.7.6, p.288 (PDF 300); Thm 11.7.2 (strong multiplicity one) and Cor 11.7.3, p.309 (PDF 320) |
| `knapp-1994-archimedean-llc` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Thm 1(c), p.400 (PDF 410); Thm 4, p.405 (PDF 415); used only for the proof route (§5) |
| `flath-1979-tensor-products` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | factorization of irreducible admissible representations of `G(𝔸)` into restricted tensor products, §3, pp.181–182 (PDF 177–178); background only (§3, §5) |

**What GH state.** GH p.309, after Theorem 11.7.2 (strong multiplicity one
for cuspidal representations):

> More generally, one has the following (see Exercise 11.8).
>
> **Corollary 11.7.3** Let `π` and `π'` be isobaric automorphic
> representations of `GL_n(𝔸_F)` and let `S` be a finite set of places of
> `F`. If `π^S ≅ π'^S` then `π ≅ π'`.

Here `π^S` is the restricted tensor product of the local components `π_v`,
`v ∉ S`. GH give no proof beyond the reference to Exercise 11.8.

## 2. The declaration

`IsobaricStrongMultiplicityOneStatement` says the following. Let:

- `F` be a number field with `[CompactSpace (AdeleQuotient F)]`;
- `r : ℕ` and `Q, Q' : IrreducibleOperatorSubquotient F r`, irreducible
  automorphic operator subquotients of `GL_(r+1)` over `F`;
- `IsIsobaric.{u, uQ} Q` and `IsIsobaric.{u, uQ} Q'`;
- `S : Finset (FinitePlace F)` be a finite set of finite places.

Suppose that for every finite place `v ∉ S` there is
`A : AutomorphicObject.{u, u} (padicField v) r.succPNat`, an irreducible
admissible smooth representation of `GL_(r+1)(F_v)`, with injective
intertwining maps from `A` into `Q.subquotient.localRepresentation v` and into
`Q'.subquotient.localRepresentation v`, the restrictions of `Q` and `Q'` to
`GL_(r+1)(F_v)`. Then `Nonempty (Q.Equivalence Q')`.

## 3. Hypotheses and conclusion, matched with GH

- **Isobaric representations.** GH's `π`, `π'` are isobaric automorphic
  representations of `GL_n(𝔸_F)`, `n = r + 1`. Here they are irreducible
  automorphic operator subquotients with `IsIsobaric`; this is GH Definition
  10.7.6 as formalized and explained in `IsobaricAutomorphicRepresentation.md`
  §5.
- **Local agreement.** GH's hypothesis `π^S ≅ π'^S` says, by the uniqueness
  of factors in Flath's factorization (background), that `π_v ≅ π'_v` for
  every `v ∉ S`. The Lean hypothesis at a finite place `v` is that one
  irreducible admissible `A` embeds into both restrictions. For admissible
  `Q`, Flath's factorization makes the restriction of `Q` to `GL_(r+1)(F_v)`
  a direct sum of copies of `Q_v`, so an irreducible `A` embeds exactly when
  `A ≅ Q_v`. So the Lean hypothesis at `v` says `Q_v ≅ Q'_v`. Conversely, if
  `Q_v ≅ Q'_v`, a copy of `Q_v` inside `Q` is such an `A`, with carrier in
  universe `u`. These translations are background; they are not asserted.
- **The infinite places.** GH's `S` is any finite set of places. Here `S`
  holds finite places only, and nothing is assumed at the infinite places.
  As for `CuspidalStrongMultiplicityOneStatement` (its Markdown §3), this is
  GH's corollary for sets `S` that contain every infinite place, and it is
  equivalent to GH's corollary. Given GH's `S`, take its finite places as the
  Lean `S`: GH's hypothesis gives the Lean hypothesis. Conversely, the Lean
  hypothesis with a finite set `S` of finite places is GH's hypothesis for
  `S` together with all infinite places. The comparison is at every finite
  `v ∉ S`, ramified or not.
- **The conclusion.** `Q.Equivalence Q'` is
  `Q.subquotient.Equivalence Q'.subquotient`, a linear equivalence of the
  quotient carriers that intertwines every operator: the finite adelic
  translations, the standard maximal compact subgroup at infinity and the
  enveloping algebra (`IrreducibleOperatorSubquotient.lean`,
  `OperatorSubquotient.lean`). By `IrreducibleOperatorSubquotient.isoClass_eq_iff`
  it is equality of the Library's isomorphism classes. This is GH's
  `π ≅ π'`. Equality of `Q` and `Q'` as subquotients is a different claim
  and is not stated.

So the Lean statement is GH Corollary 11.7.3, up to the background
translations above.

## 4. Relation to other statements

- **`CuspidalStrongMultiplicityOneStatement`** (GH Theorem 11.7.2, published):
  two cuspidal realizations `T`, `T'` whose presentations have equal local
  classes outside `S` have `T.isoClass = T'.isoClass`. It is phrased with
  cuspidal realizations and the local classes of presentations, this one with
  irreducible operator subquotients and embeddings. Cuspidal
  representations are isobaric with `k = 1` (background, through
  `IsobaricAutomorphicRepresentation.md` §4), so GH Theorem 11.7.2 is the
  cuspidal case of Corollary 11.7.3. Neither Lean statement is derived from
  the other here.
- **`CuspidalSpectralRigidityStatement`**
  (`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean`,
  proof Task 6446 `c4f0be57-1a49-4a42-b813-4354e297ab3f`): its
  `CuspidalEulerConstituentRecoveryStatement` recovers a list of cuspidal
  classes, with multiplicity, from the products of their unramified Euler
  polynomials outside a finite set. This is the numerical form of the
  cuspidal-data step of Corollary 11.7.3, without local components or
  isobaric representations.
- **`CuspidalInducingDataRigidityStatement`** (GH Theorem 10.7.2, published;
  proof Task 6447 `c6bba40a-b120-420c-9c51-9eae3198c17e`): cuspidal data
  whose induced representations share a spherical constituent at almost all
  finite places agree up to permutation.
- **`CuspidalIsobaricAutomorphyStatement`** (GH Theorem 10.7.5 at every
  place, same contribution): existence of an isobaric `Q` for given cuspidal
  data. This statement is the matching uniqueness up to equivalence.

## 5. Proof route (for the proof task; not part of the statement)

GH leave the proof as Exercise 11.8. A route with the Library's statements:

1. **Same cuspidal data.** Write `Q` and `Q'` as isobaric sums of `(T, P, h)`
   and `(T', P', h')`. Outside a finite set of finite places containing `S`,
   all local components of the `P i` and `P' j` are spherical. There the
   common `A` is the local isobaric sum of both families, hence spherical and
   a constituent of both induced representations (GH Theorems 10.6.3 and
   10.6.4). `CuspidalInducingDataRigidityStatement` then gives a bijection
   `e` of the index sets with `T' (e i)` equivalent to `T i`.
2. **Same local components.** Equivalent cuspidal realizations have
   isomorphic local components at every finite place (independence of the
   presentation, background) and the same archimedean parameters up to the
   moves of `StandardModule.md` Derived choice 4. So the local isobaric sums
   agree at every finite place (Kudla's Theorem 1.2.5, through
   `IsIsobaricSum`), and the Langlands quotients `J(ds')` agree at every
   infinite place (Knapp Theorems 1(c) and 4).
3. **Global step.** By §3 and `IsobaricAutomorphicRepresentation.md` §5,
   `Q_v ≅ Q'_v` at every place, and Flath's factorization gives `Q ≅ Q'`.
   This needs the admissibility of `Q` and `Q'` and a factorization theorem
   that includes the `(𝔤, K)`-modules at the infinite places. The Library
   has a factorization theorem for the finite adelic group
   (`flathRestrictedProductExistence`, used in
   `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`), but not
   one for irreducible operator subquotients with their archimedean
   operators.

## 6. Not asserted

- that `Q` and `Q'` are equal as subquotients;
- admissibility of `Q` or `Q'`, or that their restrictions to a place are
  isotypic;
- anything at the infinite places in the hypothesis;
- multiplicity one for isobaric representations in the space of automorphic
  forms;
- presentations in a universe `uQ ≠ u`. If none exist, `IsIsobaric.{u, uQ}`
  is false for every `Q`, and the statement at that `uQ` is vacuous.

## 7. Provenance

This is a source statement: GH Corollary 11.7.3. The following choices belong
to this formalization:

- "isobaric" is `IsIsobaric` (GH Definition 10.7.6, with the conventions of
  `IsobaricAutomorphicRepresentation.md` §7);
- `π^S ≅ π'^S` is replaced by the existence, at each finite place `v ∉ S`, of
  one irreducible admissible representation embedded in both restrictions;
- `S` is a finite set of finite places, with no hypothesis at the infinite
  places (§3);
- `π ≅ π'` is `Nonempty (Q.Equivalence Q')`.

The Lean files were checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
declaration is a `def` returning `Prop`, with universe parameters `u` and
`uQ`.
