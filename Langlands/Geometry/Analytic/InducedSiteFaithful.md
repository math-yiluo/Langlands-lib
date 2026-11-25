# Induction on equivariant quasi-étale sites is faithful

This module proves that the induction functor
`quasiEtaleSiteInduction hH hC hQ X : Qét(X(H)) ⥤ Qét(X_{G/H}(G))` (module
`InducedEquivariantSite`) is faithful. Faithfulness is one of the three parts of
the equivalence in Berkovich's Example 1.2.1(i). It is a helper for the proof of
`InducedSpace.QuasiEtaleSiteEquivalenceStatement` (module
`InducedSiteEquivalenceStatement`). Fullness and essential surjectivity are not
treated here. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

## Declarations

Let `G : Type z` be a group, `H` a subgroup and `X` an `H`-object of
`LocalizedCategory` (Lean type `Action (LocalizedCategory …) H`).

- `foldHom H X : (copies H X).pt ⟶ X.V` is the fold morphism from the disjoint
  union of the copies of `X` (module `InducedAnalyticSpace`) to `X`. It is the
  identity on every copy. It is built from the coproduct property
  `isColimitCopies`.
- `copy_foldHom H X c : copy H X c ≫ foldHom H X = 𝟙 X.V`.
- `isSplitMono_copy H X c`: every copy inclusion `copy H X c` is a split
  monomorphism, split by `foldHom H X`.
- `inductionFunctor_map_injective H h`: if two morphisms `f f' : X ⟶ X'` of
  `H`-objects have the same induction `(inductionFunctor H).map f`, then
  `f = f'`.
- `faithful_inductionFunctor H`: `inductionFunctor H` (module
  `InducedSpaceAdjunction`) is faithful.

Now let `G` be a topological group, `hH : IsOpen (H : Set G)`, and `hC`, `hQ`
proofs of `InducedSpace.ContinuityStatement` and
`InducedSpace.MorphismPropertyStatement`.

- `faithful_gSpaceInduction hH hC`: induction of `H`-spaces to `G`-spaces,
  `gSpaceInduction hH hC`, is faithful.
- `faithful_quasiEtaleSiteInduction hH hC hQ X`: for an `H`-space `X`,
  `quasiEtaleSiteInduction hH hC hQ X` is faithful.

## Proof

Restrict the induced morphism to the copy indexed by the coset `H`. Library lemma
`copy_inductionFunctor_map` (module `InducedSpaceAdjunction`) gives
`copy H X c ≫ ((inductionFunctor H).map f).hom = f.hom ≫ copy H X' c`. So equal
inductions give `f.hom ≫ copy H X' c = f'.hom ≫ copy H X' c`. The copy
inclusion is a split monomorphism, so it can be cancelled, and `Action.Hom.ext`
gives `f = f'`.

The functor `gSpaceInduction` is `inductionFunctor H` lifted to full
subcategories. Two morphisms of the full subcategory `GSpace` are equal when
their underlying morphisms are (`ObjectProperty.hom_ext`). This gives
faithfulness of `gSpaceInduction`. A morphism of `EquivariantQuasiEtaleSite X`
is a morphism over `X` (Mathlib's `MorphismProperty.Over`). It is determined by
its morphism of `H`-spaces (`MorphismProperty.Over.Hom.ext`), and
`quasiEtaleSiteInduction` acts on that morphism by `gSpaceInduction`. This gives
faithfulness of `quasiEtaleSiteInduction`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
§1.1.2 (printed p.2) builds `X_{G/H}` from copies of `X` indexed by `G/H`.
§1.2, Example 1.2.1(i) (printed p.3) states without proof that induction
gives an isomorphism of sites. Faithfulness is part of that statement. The
argument here, through the fold morphism and the copy indexed by `H`, is
derived for this formalization.
