# Isobaric automorphic representations of `GL_n` over a number field

Author: Worker 3657. Definition module of a statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** The module `Langlands.Global.Factors.IsobaricAutomorphicRepresentation`
defines seven declarations and proves nothing:

- `Langlands.LocalFactor.Archimedean.RealBlock.exponent`;
- `Langlands.LocalFactor.Archimedean.IsRealLanglandsOrdered`;
- `Langlands.LocalFactor.Archimedean.IsComplexLanglandsOrdered`;
- `Langlands.Automorphic.OperatorSubquotient.HasRealPlaceLanglandsQuotient`;
- `Langlands.Automorphic.OperatorSubquotient.HasComplexPlaceLanglandsQuotient`;
- `Langlands.Automorphic.IrreducibleOperatorSubquotient.IsCuspidalIsobaricSum`;
- `Langlands.Automorphic.IrreducibleOperatorSubquotient.IsIsobaric`.

Together they formalize Getz–Hahn (2024), Definition 10.7.6: an automorphic
representation `π` of `GL_n(𝔸_F)` is *isobaric* if `π ≅ π_1 ⊞ ⋯ ⊞ π_k` for
cuspidal automorphic representations `π_i` of `GL_(n_i)(𝔸_F)` with
`∑ n_i = n`. GH define `⊞_i π_i` as the restricted tensor product of the local
isobaric sums `⊞_i π_(iv)` over all places (GH (10.35)). The Lean definitions
state this place by place, at the finite places and at the real and complex
places.

The module also has `local instance`s. Six give the `AddCommGroup` structure of
the submodule carriers of automorphic functions and realizations, as in the
published place-action modules. One is the canonical topology on `GL_n(F_v)`,
the one of the correspondence category `AutomorphicObject (padicField v)`, as in
`CuspidalIsobaricRealizationStatement`. Library vocabulary used:

- `RealBlock`, `realRank` (`Langlands/LocalFactor/ArchimedeanPresentation.lean`)
  and `RealCharacterData`, `ComplexCharacterData`
  (`Langlands/LocalFactor/ArchimedeanAttachment.lean`);
- `realStandardKFinite`, `complexStandardKFinite`,
  `OperatorRealization.HasRealPlaceParameter` and
  `OperatorRealization.HasComplexPlaceParameter`
  (`Langlands/Automorphic/ArchimedeanPlaceParameter.lean`), over the standard
  modules of `Langlands/Representation/Archimedean/StandardModule.lean`;
- `OperatorSubquotient.realPlaceCompactRepresentation`,
  `complexPlaceCompactRepresentation`
  (`Langlands/Automorphic/OperatorSubquotientPlaceAction.lean`) and
  `realPlaceLieAction`, `complexPlaceLieAction`
  (`Langlands/Automorphic/OperatorSubquotientLieAction.lean`);
- `IrreducibleOperatorSubquotient`
  (`Langlands/Automorphic/IrreducibleOperatorSubquotient.lean`) and
  `OperatorSubquotient.localRepresentation`
  (`Langlands/Automorphic/OperatorSubquotient.lean`);
- `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`
  (`Langlands/Automorphic/CuspidalOperatorRealization.lean`),
  `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`
  (`Langlands/Global/Factors/CuspidalPairFactorData.lean`) and
  `LocalRealization.padicObject` (`Langlands/Automorphic/PadicLocalCategory.lean`);
- `PadicField.TopologicalData.IsIsobaricSum`, the local isobaric sum at a finite
  place (`Langlands/Representation/Classification/IsobaricSum.lean`), and
  `Correspondence.AutomorphicObject`
  (`Langlands/Correspondence/AutomorphicRelations.lean`).

The universe parameters of `IsCuspidalIsobaricSum` and `IsIsobaric` are `u`
(the number field, the local carriers and the multisegments) and `uQ` (the
factor universe of the spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | (10.28)–(10.31), p.283 (PDF 295); Thm 10.6.1, (10.32), the notation `⊞`, Thm 10.6.2, (10.33), p.284 (PDF 296); `π_i = \|det\|^(λ_i) π_i^1`, Thm 10.7.5, (10.35), Def 10.7.6, pp.288–289 (PDF 300–301) |
| `knapp-1994-archimedean-llc` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | `(𝔤, K)`-modules and infinitesimal equivalence, p.399 (PDF 409); building blocks (2.2), (2.3), unitary induction (2.4), ordering (2.5), Thm 1, p.400 (PDF 410); two-dimensional representations `(ℓ, t)` of `W_ℝ`, (3.3), p.402 (PDF 412); `(ℓ, t) ↦ D_ℓ ⊗ \|det(·)\|^t`, (3.4), p.403 (PDF 413); `GL_n(ℂ)`: (4.1)–(4.3), Thm 4, p.405 (PDF 415) |
| `flath-1979-tensor-products` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | factorization of irreducible admissible representations of `G(𝔸)` into restricted tensor products, with `(𝔤_v, K_v)`-modules at the archimedean places, §3, pp.181–182 (PDF 177–178); used only as background (§5) |

**What GH state.** GH §10.6 is local. For irreducible essentially
square-integrable `π_i` of `GL_(n_i)(F)`, with `A_(GL_(n_i)) = ℝ_(>0) I_(n_i)` in
the archimedean case (10.28), `π_i^1` is the representation of
`A_(GL_(n_i)) \ GL_(n_i)(F)` with `π_i(g) = |det g|^(λ_i) π_i^1(g)` (10.29).
After a permutation, `Re(λ_1) ≥ ⋯ ≥ Re(λ_k)` (10.30). With `P` the standard
parabolic of type `(n_1, …, n_k)` and `a_M^* = ℝ^k` identified so that
`⟨H_M(diag(x_1, …, x_k)), λ⟩ = ∑ λ_i log|det x_i|` (10.31), GH form
`I(⊗π_i^1, λ)`. Theorem 10.6.1: it "has a unique irreducible quotient
`J(⊗π_i^1, λ)`", determined by the data up to permutation, up to infinitesimal
equivalence in the archimedean case (proof: "the discussion and references after
[Kna94, Theorem 1 and 4]"). GH write `π_1 ⊞ ⋯ ⊞ π_k` for this quotient, for the
`π_i` in any order. Theorem 10.6.2: every irreducible admissible representation
is (infinitesimally) equivalent to such a `⊞`. (10.33) extends `⊞` to arbitrary
irreducible admissible `π_i`: write `π_i = ⊞_j π'_(ij)` with essentially
square-integrable `π'_(ij)` and set `⊞_i π_i = ⊞_i (⊞_j π'_(ij))`.

GH §10.7 is global. For cuspidal `π_i` of `GL_(n_i)(𝔸_F)`, Theorem 10.7.5
calls `⊞_i π_i := ⊗'_v (⊞_i π_(iv))` (10.35) automorphic. Then:

> **Definition 10.7.6.** An automorphic representation `π` of `GL_n(𝔸_F)` is
> isobaric if there are cuspidal automorphic representations `π_i` of
> `GL_(n_i)(𝔸_F)` with `∑_(i=1)^k n_i = n` such that `π ≅ ⊞_(i=1)^k π_i`.

GH add (p.289) that "Not all automorphic representations are isobaric"
(Exercise 10.8).

**What Knapp states.** p.400: the building blocks of `GL_n(ℝ)` are obtained by
"tensoring … with a quasicharacter `a ↦ |det a|^t` on the positive scalar
matrices of size 1 or 2": (2.2a) `1 ⊗ |·|^t`, `sgn ⊗ |·|^t` for `GL_1(ℝ)` and
(2.2b) `D_ℓ ⊗ |det(·)|^t` for `GL_2(ℝ)`. For a partition `(n_1, …, n_r)` of `n`
into 1s and 2s, `Q = DU` is the block upper triangular subgroup (2.3), and
`I(σ_1, …, σ_r)` is unitary induction from `Q` (2.4). Theorem 1: (a) under the
ordering (2.5), `I(σ_1, …, σ_r)` has a unique irreducible quotient
`J(σ_1, …, σ_r)`; (b) these exhaust the irreducible admissible representations
up to infinitesimal equivalence; (c) two of them are infinitesimally equivalent
iff the blocks agree up to permutation. p.405: for `GL_n(ℂ)` the blocks are the
characters `[z]^ℓ |z|_ℂ^t` of `GL_1(ℂ)` (4.1), with `[z] = z/|z|` and
`|z|_ℂ = |z|^2`; `I(σ_1, …, σ_n)` is unitary induction from the upper
triangular subgroup (4.2), and Theorem 4 is the analogue of Theorem 1 under the
ordering (4.3) `Re t_1 ≥ ⋯ ≥ Re t_n`.

## 2. The Langlands order of archimedean blocks

- **`RealBlock.exponent`.** A `RealBlock` is `.character d`
  (`d.character x = sgn(x)^ε |x|^t`) or `.induced d`, the real induction of
  the character `(z/|z|)^m |z|^(2t)` of `ℂˣ` (`StandardModule.md`). In both
  cases `exponent` returns `t = d.exponent`.
- **`IsRealLanglandsOrdered ds`**: `ds.Pairwise (fun a b => b.exponent.re ≤ a.exponent.re)`,
  that is, the real parts of the exponents weakly decrease along the list.
- **`IsComplexLanglandsOrdered ds`**: the same for a list of
  `ComplexCharacterData`.

**Match with the sources.** The exponent `t` is GH's `λ` of (10.29). For the
character `sgn^ε |·|^t` of `GL_1(ℝ)` this is clear. For Knapp's
`D_ℓ ⊗ |det(·)|^t`, the factor `D_ℓ` is trivial on `ℝ_(>0) I_2`, so `λ = t`;
the Library's induction block of weight `m ≠ 0` and exponent `t` is
`D_(|m|) ⊗ |det|^t` (`StandardModule.md`, Knapp (3.3)–(3.4) and Derived choice
2). For a weight-zero block the Library's standard module is the principal
series `Ind(sgn|·|^t ⊗ |·|^t)`, the standard module of the two characters
`sgn|·|^t`, `|·|^t` (`StandardModule.md`, Derived choice 3). Both have exponent
`t`, so splitting such a block does not change the order condition. At a
complex place, the Library's `(z/|z|)^m |z|^(2t)` is Knapp's
`[z]^m |z|_ℂ^t`, and the order is Knapp's (4.3). (GH's `|det|` at a complex
place may be read with `|·|_ℂ` or with `|·|`; this multiplies all exponents at
the place by the same positive factor and does not change the order.)

So `IsRealLanglandsOrdered` is GH's (10.30). Knapp's (2.5) is printed with
factors `n_j^(-1)`: "`n_1^(-1) Re t_1 ≥ n_2^(-1) Re t_2 ≥ ⋯ ≥ n_r^(-1) Re t_r`".
The definition follows GH (10.30) and compares `Re t_j` itself. In the Library's
normalization (principal series from the upper triangular Borel subgroup,
right translation, unitary induction; `StandardModule.md` Derived choices 1
and 7), the exponent `t_j` is the per-coordinate exponent of the block, and the
simple roots `e_a − e_(a+1)` that join adjacent blocks `j`, `j+1` take the value
`t_j − t_(j+1)` on the inducing parameter. So weakly decreasing `Re t_j` is the
closed positive chamber of the block upper triangular parabolic, the condition
under which the standard module has the Langlands quotient as a quotient. For
`GL_2(ℝ)` and two characters: the trivial representation is a quotient of
`Ind(|·|^(1/2) ⊗ |·|^(-1/2))` (integration over `B \ GL_2(ℝ)`) and a
subrepresentation of `Ind(|·|^(-1/2) ⊗ |·|^(1/2))`.

## 3. Langlands quotients inside an automorphic subquotient

`HasRealPlaceLanglandsQuotient Q v ds`, for `Q : OperatorSubquotient F n` and
a real place `v`, says:

1. `realRank ds = n` and `IsRealLanglandsOrdered ds`;
2. there is a `ℂ`-linear map
   `A : realStandardKFinite n ds →ₗ[ℂ] Q.Space` from the `O(n)`-finite
   functions of the Library's standard module of `ds` such that
   - for `k ∈ O(n)`, the right translate of `f` by `k` is again in the
     `O(n)`-finite functions, and `A` sends it to
     `Q.realPlaceCompactRepresentation v k (A f)`;
   - for `X ∈ 𝔤𝔩_n(ℝ)`, the right derivative of `f` along `X` is again
     `O(n)`-finite, and `A` sends it to `Q.realPlaceLieAction v (1 ⊗ X) (A f)`;
3. the range of `A` is nonzero;
4. every `ℂ`-subspace `W` of the range of `A` that is stable under the compact
   action at `v` and under the Lie action at `v` of all real `X` is `0` or the
   whole range.

Conditions 1–2 are those of `OperatorRealization.HasRealPlaceParameter`, with
the Langlands order added and injectivity of `A` replaced by conditions 3–4.
`HasComplexPlaceLanglandsQuotient Q v ds` is the same at a complex place `v`,
with `F_v` identified with `ℂ` as in the published place actions:
`ds.length = n`, `IsComplexLanglandsOrdered ds`, `U(n)` and real directions
`X ∈ 𝔤𝔩_n(ℂ)`. Since `W` is a `ℂ`-subspace, stability under `1 ⊗ X` for real
`X` is stability under the complexified Lie algebra.

**Meaning.** Since `A` is equivariant, its range is a `(𝔤_v, K_v)`-submodule
of `Q`, and conditions 3–4 say that it is irreducible. It is a quotient of the
`(𝔤, K)`-module `I(ds)_K` of `K`-finite vectors of the standard module. By
Knapp's Theorem 1(a) (Theorem 4(a) at a complex place) and Harish-Chandra's
correspondence between closed invariant subspaces and `(𝔤, K)`-submodules
(Knapp p.399), the ordered standard module has exactly one irreducible
quotient, `J(ds)`. So the predicate says: `Q` contains a
`(𝔤_v, K_v)`-submodule isomorphic to the Langlands quotient `J(ds)`.
Conversely, such a submodule gives `A` as the composition
`I(ds)_K → J(ds)_K → Q`. This equivalence uses Knapp's theorem and is not
proved here.

## 4. Isobaric sums of cuspidal realizations

`IsCuspidalIsobaricSum Q T P h`, for `Q : IrreducibleOperatorSubquotient F r`,
actual cuspidal realizations `T i` of `GL_(m i + 1)` (`i : Fin k`), spectral
presentations `P i` and `h i : HasIrreducibleAdmissibleComponents (P i)`, under
`[CompactSpace (AdeleQuotient F)]`, is the conjunction of three conditions.
Write `σ_(i,v)` for the canonical object
`((P i).localComponent v).padicObject (h i v).1 (h i v).2` of
`AutomorphicObject (padicField v)`, the local component of `T i` at the finite
place `v`.

- **Finite places.** For every finite place `v` there is an
  `A : AutomorphicObject.{u, u} (padicField v) r.succPNat` with
  `IsIsobaricSum (fun i => σ_(i,v).obj) A.obj` and an injective intertwining
  map from `A` into `Q.subquotient.localRepresentation v`, the restriction of
  `Q` to `GL_(r+1)(F_v)`. These are conditions 1 and 3 of
  `CuspidalIsobaricRealizationStatement`. By `IsobaricSum.md` §3 (Kudla's
  Theorem 1.2.5), `IsIsobaricSum` says `A ≅ ⊞_i π_(iv)` in GH's sense.
- **Real places.** For every real place `v` there are lists `ds i` of real
  blocks with `(T i).realization.HasRealPlaceParameter v (ds i)` for all `i`,
  and a list `ds'` that is a permutation (`List.Perm`) of the concatenation
  `(List.ofFn ds).flatten` with
  `Q.subquotient.HasRealPlaceLanglandsQuotient v ds'`.
- **Complex places.** The same with `ComplexCharacterData`,
  `HasComplexPlaceParameter` and `HasComplexPlaceLanglandsQuotient`.

**Match with GH at the infinite places.** Fix a real place `v`. The following
are background facts, used only in this explanation:

- `π_(iv)` is generic (GH Theorem 11.3.6, cited on GH p.288), so its standard
  module is irreducible (Vogan's theorem, as recorded in `StandardModule.md`
  through Shahidi 1985). With Flath's factorization, the restriction of the
  irreducible `T i` to `(𝔤_v, K_v)` is a direct sum of copies of `π_(iv)`. So
  parameters `ds i` with `HasRealPlaceParameter` exist
  (`ArchimedeanPlaceParameter.md`, Derived formulation 1–2). Each such
  `ds i` satisfies `I(ds i) ≅ π_(iv)`: an `I(ds i)` that embeds into a
  `π_(iv)`-isotypic module is semisimple with all constituents `≅ π_(iv)`,
  and the Langlands quotient occurs once in a standard module, so `I(ds i)`
  is irreducible. By Knapp's Theorem 1(c), `ds i` is determined up to
  permutation, the sign of the weight of an induction block and the splitting
  of a weight-zero block into its two characters (`StandardModule.md`,
  Derived choice 4).
- Knapp's blocks (2.2) are the essentially square-integrable representations
  of `GL_1(ℝ)` and `GL_2(ℝ)`, and `GL_n(ℝ)` has none for `n ≥ 3`. So the
  decomposition `π_(iv) = ⊞_j π'_(ij)` of GH (10.33) is
  `π_(iv) = J(blocks of ds i)`, and `⊞_i π_(iv)` is the Langlands quotient
  `J(ds')` of the union of all blocks, put in the order (10.30). This `J(ds')`
  depends only on the blocks up to the moves above (Knapp Theorem 1(c)).
- By §3, the real-place condition then says that `Q` contains `⊞_i π_(iv)` as a
  `(𝔤_v, K_v)`-submodule. If `Q` is admissible, Flath's factorization makes
  its restriction to `(𝔤_v, K_v)` isotypic, and this says `Q_v ≅ ⊞_i π_(iv)`.

The complex places are the same, with Knapp's (4.1)–(4.3) and Theorem 4; there
the essentially square-integrable representations are the characters of
`GL_1(ℂ)`.

The parameters `ds i` are existential. By the first point, for cuspidal `T i`
this is the same as fixing any choice of them.

## 5. Isobaric representations

`IsIsobaric Q` says that there are `k`, `m : Fin k → ℕ` with
`∑ i, (m i + 1) = r + 1`, actual cuspidal realizations `T i` of
`GL_(m i + 1)`, spectral presentations `P i` (universe `uQ`) and
`h i : HasIrreducibleAdmissibleComponents (P i)` with
`Q.IsCuspidalIsobaricSum T P h`.

**Match with Definition 10.7.6.**

- GH's `π` is an automorphic representation; isobaric ones are irreducible,
  since `⊞_i π_i` is. The Lean predicate is on
  `IrreducibleOperatorSubquotient F r`, the Library's irreducible automorphic
  representations of `GL_(r+1)` (`CuspidalIsobaricRealizationStatement.md` §3).
  GH's cuspidal `π_i` are the actual cuspidal realizations `T i`, with
  `n_i = m i + 1`.
- For `uQ = u`, every cuspidal realization has a presentation with irreducible
  admissible finite local components
  (`cuspidalIrreducibleAdmissibleFiniteSliceExistence` and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`). So the
  quantifier over `P` and `h` adds no condition at `uQ = u`.
- If `π ≅ ⊞_i π_i`, then by Flath's factorization `π_v ≅ ⊞_i π_(iv)` at every
  place, and `π` contains `⊞_i π_(iv)` in its restriction to each place: this
  gives the three conditions of §4 (at a finite place, the copy of
  `⊞_i π_(iv)` inside `Q` is an `A` with carrier in universe `u`).
  Conversely, if the three conditions hold and `Q` is admissible, then
  `Q_v ≅ ⊞_i π_(iv)` at every place (§4), and Flath's factorization gives
  `Q ≅ ⊗'_v (⊞_i π_(iv)) = ⊞_i π_i`, the isomorphism of the full operator
  representations. Both directions use admissibility and Flath's
  factorization; they are background and are not proved here.

## 6. Not asserted

- that `J(ds)`, the parameters `ds i` or the local isobaric sum `A` exist or
  are unique;
- that `IsIsobaric` is invariant under equivalence of operator subquotients,
  or independent of the presentations;
- admissibility of `Q`, or that its restriction to a place is isotypic;
- GH's description of `⊞_i π_i` as an irreducible subquotient of the global
  induced representation `I(⊗π_i^1, λ)`, which is not in the Library;
- GH's extension of `⊞` to tuples of isobaric representations (p.289);
- presentations in a universe `uQ ≠ u`. If none exist, `IsIsobaric.{u, uQ}`
  is false for every `Q`.

## 7. Provenance

The predicate `IsIsobaric` is GH Definition 10.7.6. The following choices
belong to this formalization:

- `π ≅ ⊞_i π_i` is replaced by the place-by-place containment of the local
  isobaric sums (§4, §5);
- at a finite place, the local isobaric sum is the derived relation
  `IsIsobaricSum` in Kudla's segment form;
- at an infinite place, the local isobaric sum is the Langlands quotient of
  the ordered union of the archimedean parameters of the `T i`, and
  containment in `Q` is a `(𝔤_v, K_v)`-map from the standard module with
  nonzero irreducible image (§3);
- the Langlands order compares the exponents as GH (10.30) does (§2);
- the cuspidal data are arbitrary cuspidal realizations, with `λ` absorbed
  (GH p.288), read through spectral presentations.

The Lean files were checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings.
