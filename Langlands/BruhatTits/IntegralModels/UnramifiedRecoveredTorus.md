# The lower integral split torus from recovered full fixer models

This internal construction supplies the closed split integral torus needed by
the depth-zero opposite-factor argument, conditional on actual recovered full
models. It derives the torus from published bounded-point closure and connected
factorization results. It does not assert existence of the supplied models.

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`, and `G` an
affine group scheme over `F`. Let `iS : S → G` be a maximal split torus and
`iT : T → G` a morphism from a commutative group scheme, with `f : S → T`
satisfying `f ≫ iT = iS`. Supply an upper `KPApartmentData` `D` for `T_K → G_K`,
its centralizer `C`, and their full `IntegerValuation.IsOmegaCompatible`
condition. The upper inclusion is a monomorphism. No maximality or splitting
hypothesis on `T_K` is needed for this construction beyond these supplied data.

Supply lower and upper relative-component model pairs `L` and `E` and an actual
`UnramifiedComponentModelRecovery L E`. For any subset `Ω` of the upper
apartment assume exactly

```text
E.full.integralPoints =
  characterValuationKernel (MaximalUnramified.valuation F) G_K
    ∩ D.pointwiseFixer (D.apartmentMap '' Ω).
```

`exists_closedSplitIntegralTorus_of_fullRecovery` constructs
`A : IntegralTorusData L S iS` with `A.IsClosedSplit`: its integral torus is
split, its map to `L.neutral` is closed, and its generic-fibre identification
commutes with the prescribed original inclusion `iS`.
`integralTorusOfFullRecovery` chooses this data and
`integralTorusOfFullRecovery_isClosedSplit` proves the stated property.
The universe is arbitrary.

The proof first establishes
`map_lowerTorus_characterValuationKernel_le_oneFixer`. Full V6 makes the
image of every scalar unit of `S_K` fix every upper apartment point, by the
published `map_torusUnits_smul_apartmentMap` applied to `f_K`. Character
valuation kernels are preserved by the map to `G_K`. Thus these scalar units
belong to the full one-fixer of `Ω`. Full-model recovery identifies that
one-fixer with the integral image of `L.full` after unramified base change.

The upper integer ring has algebraically closed, hence infinite, residue
field, and its units have normalized valuation one. Its intersection with
`F` is exactly the original integer ring. The published
`SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange`
therefore constructs a closed split torus in `L.full` with the specified
generic torus and map. The published `IntegralSplitTorusData.factorNeutral`
then factors its map through `L.neutral` because a split torus has geometrically
connected fibres. Closedness and the generic-fibre square are preserved.

This construction needs no equality describing neutral integral points, no
`UnramifiedZeroDatum`, and no boundedness or nonemptiness of `Ω`. It does not
prove special-fibre maximality of the resulting torus. The published
`unramifiedTorusClause` has a different input: it assumes the exact neutral
image in terms of a zero datum and also proves special-fibre maximality.
Neither statement is used here to assume the unresolved neutral-image equality.

The lower and upper models, their full recovery, the full image equality and
the supplied upper apartment/V6 remain hypotheses. This helper constructs no
model at a Galois-fixed point and does not prove
`UnramifiedFixedDepthZeroOppositeStatement`.
