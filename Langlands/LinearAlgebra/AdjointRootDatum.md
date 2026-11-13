# The adjoint root datum of a root datum

Let `P : RootDatum ι X Y` be a Mathlib root datum with a finite index type `ι`: character
lattice `X`, cocharacter lattice `Y`, roots `P.root i` and coroots `P.coroot i`. Let `ℤR`
denote the root lattice `P.rootSpan ℤ ⊆ X`. All declarations are in the namespace
`Langlands.LinearAlgebra.AdjointRootDatum`.

## Definitions

- `coweightMap P : Y →ₗ[ℤ] Dual ℤ (ℤR)` restricts a cocharacter, viewed as a linear form on
  `X` through the perfect pairing, to the root lattice: `coweightMap P y x = ⟨x, y⟩`.
- `coroot P i` is `coweightMap P (P.coroot i)`, the restriction of the coroot to `ℤR`.
- `rootDatum P : RootDatum ι (ℤR) (Dual ℤ (ℤR))` is the adjoint root datum
  `(ℤR, R, Hom(ℤR, ℤ), R^∨)`. Its pairing is evaluation `Dual.eval ℤ ℤR`, which is perfect
  because `ℤR` is reflexive (`isReflexive_rootSpan`). Its roots are the roots of `P`, viewed
  in `ℤR` (`P.rootSpanMem ℤ`). Its coroots are the restricted coroots `coroot P i`. It reuses
  the reflection permutation of `P`.
- `fromRootDatum P : RootPairing.Hom (rootDatum P) P` is the canonical morphism. On weights
  it is the inclusion `ℤR → X`, on coweights it is `coweightMap P`, and on indices it is the
  identity.

## Results

- `isReflexive_rootSpan`: `ℤR` is a reflexive `ℤ`-module. `X` is reflexive because the
  pairing is perfect, and a submodule of a reflexive `ℤ`-module inherits reflexivity through
  the instance that Mathlib provides for this case.
- `coroot_rootSpanMem`: `coroot P i (α_j) = P.pairing j i`.
- `coroot_injective`: the restricted coroots are injective in `i`. If two restricted coroots
  agree, then `P.pairing i j = P.pairing j i = 2`, and `RootPairing.pairing_two_two_iff`
  gives `i = j`.
- `finite_rootSpan`: `ℤR` is a finitely generated `ℤ`-module, being spanned by the finitely
  many roots.
- `injective_fromRootDatum_weightMap`: the weight map of `fromRootDatum P` (the inclusion) is
  injective.
- `injective_fromRootDatum_coweightMap`: if `X / ℤR` is finite, the coweight map is injective.
  If `y` vanishes on `ℤR`, then for every `x` some positive multiple `n • x` lies in `ℤR`.
  Hence `n ⟨x, y⟩ = 0`, so `⟨x, y⟩ = 0`, and `y = 0` by perfectness of the pairing.
- `isReduced_rootDatum`: if `P` is reduced, so is `rootDatum P`. The pairings of the two root
  data agree, so the Coxeter-weight criterion
  `RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent` transfers linear dependence
  of two roots from `ℤR` to `X`. Reducedness of `P` then gives `α_i = ±α_j`.

The simp lemmas `coweightMap_apply`, `coroot_apply`, `rootDatum_root`, `rootDatum_coroot`,
`rootDatum_toLinearMap`, `fromRootDatum_weightMap` and `fromRootDatum_coweightMap` record the
defining formulas.

## Provenance

This is the standard construction of the adjoint root datum `(Q, R, P^∨, R^∨)` attached to a
root datum, where `Q = ℤR` is the root lattice and `P^∨ = Hom(Q, ℤ)` is the coweight lattice.
It is internal infrastructure written for the proof of
`QuasiSplitAdjointSimpleRootTransitivityStatement`. There it is used through
`Langlands.GroupScheme.Reductive.AdjointRootSpan` to show that the roots of a split adjoint
group span its character lattice.
