# Archimedean components of Weil representations and archimedean matching

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. The declarations lie in the namespaces
`Langlands.ClassField.Global.RelativeWeilGroup` and `Langlands.ClassField.Global.WeilMapSystem`.
The module defines four things:

- the archimedean components of representations of the relative Weil group `W_{E/F}` and of
  the absolute Weil group `S.WeilGroup` along archimedean local Weil maps;
- their presentation by the Library's archimedean Weil-group blocks;
- the archimedean parameter of a representation of `W_F` at an embedding of `F`;
- the matching of a representation of `W_F` with an actual cuspidal class at an infinite
  place.

It constructs no local map, representation, presentation or parameter, and asserts no
existence.

## Setting

The archimedean Weil groups are the published `RealWeil` (`W_ℝ`) and `ComplexWeil`
(`W_ℂ = ℂˣ`). The local maps are characterized by the published `ArchimedeanLocalWeilMap`
predicates `WeilMapSystem.IsRealLocalWeilMap φ θ` and `IsComplexLocalWeilMap φ θ` at an
embedding `φ : F →+* ℂ`. Blocks are `RealBlock` and `ComplexCharacterData`. Their sum models
are the published `realModel ds` and `complexModel ds` of `ArchimedeanPresentation`.
Representations are `FiniteRepresentation.{0, u, uV} ℂ _`, with independent carrier universes.

## Declarations

### Relative Weil groups

For `A` a representation of `W_{E/F} = RelativeWeilGroup c F E`:

- `realComponent A ι` and `complexComponent A ι` are the restrictions `A ∘ ι` along maps
  `ι : W_ℝ →ₜ* W_{E/F}` and `ι : W_ℂ →ₜ* W_{E/F}`, on the carrier of `A`.
- `HasRealPresentation A ι ds` and `HasComplexPresentation A ι ds` hold when the archimedean
  component is equivalent to the sum model of the blocks `ds`.

### Absolute Weil group

For `A` a representation of `S.WeilGroup`:

- `S.realComponent A θ` and `S.complexComponent A θ` are the restrictions along
  `θ : W_ℝ →ₜ* S.WeilGroup` and `θ : W_ℂ →ₜ* S.WeilGroup`.
- `S.HasRealArchimedeanParameter A φ ds` has two conjuncts. Some `θ` with
  `S.IsRealLocalWeilMap φ θ` exists. For every such `θ`, `S.realComponent A θ` is equivalent
  to `realModel ds`. `S.HasComplexArchimedeanParameter A φ ds` is the same for complex
  embeddings and `complexModel ds`.
- `realComponentEquiv` and `complexComponentEquiv`: an equivalence `A ≃ B` restricts to an
  equivalence of archimedean components, with the same linear equivalence. Consequently
  `HasRealArchimedeanParameter.of_equiv` and `HasComplexArchimedeanParameter.of_equiv` show
  that the parameters depend only on the equivalence class of `A`.

### Matching with cuspidal classes

Under `[CompactSpace (AdeleQuotient F)]`, for `π : PositiveRankCuspidalClass F`:

- `S.IsRealArchimedeanMatch A π v`, at a real place `v`, holds when some `ds : List RealBlock`
  is both the archimedean parameter of `A` at `v.embedding` and the published place parameter
  of `π` at `v` (`PositiveRankCuspidalClass.HasRealPlaceParameter`).
- `S.IsComplexArchimedeanMatch A π v`, at a complex place `v`, is the same with complex blocks
  and the embedding `v.embedding`. This is Mathlib's chosen representative embedding, which is
  also the identification `F_v ≅ ℂ` used by the published automorphic place actions.
- `IsRealArchimedeanMatch.exists_realRank_eq`: a match gives a parameter of `A` whose total
  rank is the rank of `π`.
- `IsRealArchimedeanMatch.of_equiv` and `IsComplexArchimedeanMatch.of_equiv`: matching
  depends only on the equivalence class of `A`.

## Source correspondence

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
  literature ID `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`. The PDF page is the
  printed page plus nine. §2.1, printed p.9 (PDF p.18): the restriction `V ↦ V_v` of
  representations of `W_F` along `θ_v` of (1.6.1). It depends only on `v`, since `θ_v` is
  determined up to conjugation. (2.2.2), printed p.10 (PDF p.19): representations of the
  archimedean Weil groups as sums of characters and induced representations.
- A. W. Knapp, *Local Langlands correspondence: the archimedean case*, Proc. Sympos. Pure
  Math. 55, Part 2 (1994), literature ID `knapp-1994-archimedean-llc`, SHA256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`, Theorem 2, printed
  p.403 (PDF p.413), and Theorem 5, printed p.406 (PDF p.416): the archimedean local Langlands
  correspondence between semisimple representations of `W_ℝ`/`W_ℂ` and irreducible admissible
  representations of `GL_n(ℝ)`/`GL_n(ℂ)`.

### Derived formulation

1. **Components along every local map.** Tate's `V_v` is the restriction along `θ_v`, which is
   determined up to conjugation by `W_F`. The parameter is required for every map satisfying
   the published local-map predicate, which needs no uniqueness theorem. Since conjugation
   gives equivalent restrictions, nothing depends on a choice. As for the unramified matching
   condition, the existence of one local map is a conjunct, so the condition is never vacuous.
2. **Presentations.** The archimedean component is described by an equivalence with the sum
   model of a block list, as in the published presentation modules. Semisimple components
   admit such a presentation (Tate (2.2.2), and the Lemma on Knapp's p.403), but that fact is
   not used or proved here. A non-semisimple component has no presentation, so it has no
   archimedean parameter in this sense.
3. **Matching.** By Knapp's theorems, the archimedean component of `A` corresponds to the
   archimedean component of `π` under archimedean local Langlands exactly when they have a
   common block list, with `π`'s parameter in the sense of the published
   `ArchimedeanPlaceParameter`. Blocks are compared as lists. A permutation of the blocks
   changes neither the Weil-side sum model up to equivalence nor the generic automorphic
   standard module up to equivalence, but this is not proved here.
4. **Identification at complex places.** Both sides use `v.embedding` to identify `F_v` with
   `ℂ`: the Weil side through the local-map predicate at `φ = v.embedding`, the automorphic side
   through the published mixed coordinates.

## Scope

The module does not prove existence of archimedean parameters, independence of block order,
or any statement that associated representations match at the archimedean places. These are
theorem obligations for the statement owners.
