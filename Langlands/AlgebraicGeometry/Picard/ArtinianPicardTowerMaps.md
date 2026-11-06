# The actual inverse diagram of Picard source tests

This internal construction makes the original Picard source tests into an
actual inverse diagram on the oppositely ordered natural numbers. It keeps
the original quotient rings, augmentations and adjacent elementary arrows,
and proves compatibility with every bounded map to an ordinary adic test.

Keep the arbitrary common universe `u`, commutative `k`, specified field
`K/k`, fixed Noetherian local source `R` with its surjective augmentation
`ε`, actual flat proper scheme morphism `f`, residue-fibre line bundle `M`,
and actual initial pointed source stage `s₀` from the imported tower.
Write `A_n` for its actual test at index `n`, `C` for its unchanged quotient
source, and `p_n : C → A_n` for the existing surjective algebra projections.
The actual ideals `ker p_n` are antitone, and every projection retains the
same original residue augmentation.

For `n ≤ m`, `towerMap` is an actual augmented test arrow `A_m → A_n`.
It descends `p_n` through the surjection `p_m` with
`AlgHom.liftOfSurjective`, using `ker p_m ≤ ker p_n`. The augmentation
triangle is checked on source preimages using the two original augmentation
identities. No source test or augmentation is replaced.

`towerMap_projection` proves the exact equation `towerMap.comp p_m = p_n`
for its underlying actual algebra map. `towerMap_surjective` follows from
the surjectivity of `p_n`. `towerMap_unique` says that any actual augmented
test arrow with that same equation equals `towerMap`; its proof evaluates
the two algebra maps on preimages under `p_m`.

`towerMap_refl` proves that the equal-index map is the identity.
`towerMap_comp` proves, for `n ≤ m ≤ p`, that the composite
`A_p → A_m → A_n` is the direct map `A_p → A_n`.
Both follow from uniqueness and their exact source projection equations.
`step_eq_towerMap` proves that the map for `n ≤ n+1` equals the original
actual elementary successor reduction, using `projection_step`.

`diagram` is the resulting actual functor `ℕᵒᵈ ⥤ ArtinianTest k K`.
Its object at index `n` is the unchanged `A_n`, and its map on an order
arrow is the just constructed `towerMap`. The identity and composition
fields use the two preceding exact arrow identities, so this is a genuine
functor of the original augmented tests.

Finally `towerMap_toAdic` retains compatibility with every given explicit
bound `ker p_n ≤ m_C^(a+1)`. Descending from any later test `A_m` through
`towerMap` and then using `toAdic` gives exactly the map from `A_m` to the
same ordinary adic test obtained by propagating the bound. The uniqueness
of `toAdic` reduces this to the original projection equations.

The provenance is internal descent through the actual source projections
and their established kernel containments. These results need no
completeness or cofinality assumption beyond the imported tower data;
the final compatibility uses an explicitly given containment. This module
does not extend the adjacent pointed isomorphisms to an arbitrary-index
coherent family, supply the unproved general cofinality theorem, construct
an adic formal line-bundle system or prove the exact atlas.
