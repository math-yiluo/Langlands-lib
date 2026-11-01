# Gluing from families indexed by finite types

Author: Worker 723.

This module is internal infrastructure, not taken from the literature. It
provides an index-type form of the Library predicate
`Langlands.IsGluedFrom` (module `Langlands.Representation.Filtration.Definitions`),
and closure properties needed for inductive gluing arguments such as
Bernstein–Zelevinsky (1977) Corollary 4.14(b). Every result here is a
statement about actual natural filtrations by subfunctors and their actual
quotient functors. No hypothesis on the representations is added.

## The predicate

For a functor `M : C ⥤ Rep R G`, a finite type `ι` and a family
`P : ι → C ⥤ Rep R G`,

```lean
def IsGluedFromFamily (M : C ⥤ Rep R G) {ι : Type uι} [Fintype ι]
    (P : ι → C ⥤ Rep R G) : Prop :=
  ∃ e : Fin (Fintype.card ι) ≃ ι, IsGluedFrom M (P ∘ e)
```

This says that `M` has a finite natural filtration with `Fintype.card ι` steps,
and that its successive quotients are naturally isomorphic, in some order, to
the members of `P`, each used exactly once. The Library's `IsGluedFrom M Q` for
`Q : Fin n → _` already allows any permutation of the grades. Therefore the
choice of `e` only fixes how `ι` is enumerated.

## Constructions on filtrations

- `RepFunctorFiltration.empty M hM` is the filtration with no steps, of a
  functor whose values are all zero (`Subsingleton`). Its only step is the
  Library zero subfunctor `RepSubfunctor.zero M` (module
  `Langlands.Representation.Filtration.OneStep`), which is then also the top.

The one-step filtration and the precomposition comparison are not defined
here. They come from the Library modules
`Langlands.Representation.Filtration.OneStep` (`isGluedFrom_singleton`) and
`Langlands.Representation.Filtration.Precomposition`
(`IsGluedFrom.precomp`).

## Closure properties of `IsGluedFromFamily`

- `of_isGluedFrom e h`: an ordinary gluing `IsGluedFrom M (P ∘ e)` along any
  equivalence `e : Fin n ≃ ι` gives `IsGluedFromFamily M P`. The proof reindexes
  by `finCongr` along `Fintype.card ι = n` (Library `IsGluedFrom.reindex`).
- `exists_equiv h n hn`: conversely, for any `n` with `Fintype.card ι = n`, an
  enumeration `Fin n ≃ ι` and an ordinary gluing exist.
- `iso h e`: transport along a natural isomorphism `M ≅ M'` (Library
  `IsGluedFrom.iso`).
- `equiv h σ a`: reindex along an equivalence `σ : ι ≃ κ`, given natural
  isomorphisms `P i ≅ P' (σ i)`. `isoPieces` is the case `σ = Equiv.refl`.
- `precomp h J`: if `M` is glued from `P`, then `J ⋙ M` is glued from the
  family `J ⋙ P i`, with the same enumeration. The proof applies the Library
  `IsGluedFrom.precomp`.
- `of_iso_unique e`: when `ι` has exactly one element, a natural isomorphism
  `M ≅ P default` gives a gluing. The proof applies the Library
  `isGluedFrom_singleton` (the one-step filtration `0 ⊆ M`) along
  `Equiv.ofUnique (Fin 1) ι`.
- `of_isEmpty hM`: when `ι` is empty and every value of `M` is zero, `M` is
  glued from the empty family, using `empty M hM`.
- `splice hL hQ ι' π hexact hinj hsurj`: for natural transformations
  `ι' : L ⟶ M` and `π : M ⟶ Q` whose components are injective, exact in the
  middle (`range = ker` of the underlying linear maps) and surjective, gluings
  of `L` from `P` and of `Q` from `P'` give a gluing of `M` from
  `Sum.elim P P'`. The proof applies the Library `IsGluedFrom.splice`
  (module `Langlands.Representation.Filtration.Splicing`). It identifies the
  concatenated piece family `concatPieces` with `Sum.elim P P'` along
  `spliceIndexEquiv` followed by `Equiv.sumCongr`.

## Imports

`Langlands.Representation.Filtration.Splicing`,
`Langlands.Representation.Filtration.Transport`,
`Langlands.Representation.Filtration.OneStep` and
`Langlands.Representation.Filtration.Precomposition`. These are generic
filtration modules; none of them involves derivatives, products or any
classification result.
