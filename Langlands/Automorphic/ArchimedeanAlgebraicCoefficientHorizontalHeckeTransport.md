# Full automorphic transport for the original finite Hecke actions

This internal construction integrates the existing full automorphic transport
maps on the analytic and algebraic coefficient horizontal complexes. It uses
`Hecke.heckeActionIntertwiner`, the existing
`Algebra.LinearIntertwiner`, and the original horizontal quotient transport.
It introduces no alternative complex or quotient.

The field `F` is an actual number field. The rank `n` is nonzero, `I` is a finite
index type, and `e : I → EmbeddingIndex F` selects the embeddings used by the
coefficient construction. The coefficient input `ρ` is the existing matrix
representation of `GeneralLinearProductDualNumber.groupScheme` over `ℂ`, on a
finite type `m`. No injectivity or surjectivity of `e`, irreducibility of `ρ`, or
regularity of its weights is required. The source, middle, and target are actual
`OperatorRealization F n` objects. An input `L : S.Intertwiner T` intertwines
their full operator representations, rather than just their finite translations.
The finite adelic group has a Borel measurable structure and a single supplied
Haar measure `μ`. Every integrated action in a given map or law uses this same
measure.

The six constructors have the following original carriers and named actions.
Each result is an `Algebra.LinearIntertwiner` from the action for `S` to the
same action for `T`, in every natural degree `q`.

| Constructor | Original carrier for `S` | Named source action |
| --- | --- | --- |
| `tensorAnalyticHorizontalHeckeMap` | `S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q` | `tensorAnalyticHorizontalHeckeAction e ρ S μ q` |
| `tensorAnalyticHorizontalCyclesHeckeMap` | `tensorAnalyticHorizontalCycles e ρ S q` | `tensorAnalyticHorizontalCyclesHeckeAction e ρ S μ q` |
| `tensorAnalyticHorizontalCohomologyHeckeMap` | `TensorAnalyticHorizontalCohomology e ρ S q` | `tensorAnalyticHorizontalCohomologyHeckeAction e ρ S μ q` |
| `tensorAlgebraicHorizontalHeckeMap` | `S.tensorHorizontalSubmodule (compactRepresentation e ρ) q` | `tensorAlgebraicHorizontalHeckeAction e ρ S μ q` |
| `tensorAlgebraicHorizontalCyclesHeckeMap` | `tensorAlgebraicHorizontalCycles e ρ S q` | `tensorAlgebraicHorizontalCyclesHeckeAction e ρ S μ q` |
| `tensorAlgebraicHorizontalCohomologyHeckeMap` | `TensorAlgebraicHorizontalCohomology e ρ S q` | `tensorAlgebraicHorizontalCohomologyHeckeAction e ρ S μ q` |

For each constructor, the original group map is the corresponding
`tensorAnalyticHorizontalMap`, `tensorAnalyticHorizontalCyclesMap`, or
`tensorAnalyticHorizontalCohomologyMap`, and similarly for the algebraic model.
The cochain map acts on the automorphic tensor factor by `L` and retains the
coefficient factor. The cycle map restricts this cochain map to the kernel of
the actual differential. The cohomology map descends it to cycles modulo the
actual boundaries. Existing reduced Lie compatibility and differential
commutation establish these restrictions and descents before integration.
Existing degreewise smoothness results supply all six integration premises.

Every constructor has a `_toLinearMap` equality identifying its underlying
linear map with that original group map, and an `_apply` equality identifying
its value on any element with the value of the original map. Integration retains
the map and bundles its integrated equivariance. The two
`tensorAnalyticHorizontalCohomologyHeckeMap_class` and
`tensorAlgebraicHorizontalCohomologyHeckeMap_class` formulas send the original
`tensorAnalyticHorizontalClass` or `tensorAlgebraicHorizontalClass` of a cycle
to the class of its image under the corresponding original cycle map.

Each of the six constructors has `_id` and `_comp` laws. The identity law uses
the identity of the full operator representation and returns the identity
linear intertwiner of the corresponding named Hecke action. Given
`L : S.Intertwiner T` and `M : T.Intertwiner U`, the composition law identifies
the map for `M.comp L` with the map for `M` composed after the map for `L`.
The cochain and cycle laws apply the generic integrated equality helpers to the
existing original-map laws. The quotient laws specialize
`Horizontal.mapCohomologyHeckeIntertwiner_id_of_eq` and
`Horizontal.mapCohomologyHeckeIntertwiner_comp_of_eq` with the existing cochain
identity and composition laws. The insertion, action, chain, and smoothness
premises of those generic helpers are all discharged here by the existing
coefficient-complex constructions.

The laws are abbreviations of proved equality terms; their inferred types avoid
repeated expansion of the original quotient during elaboration. The six map
constructors also infer their types from the integrated constructor. Their
types are the original named actions displayed above by definitional equality.
The class formulas specialize the generic original-quotient class formula.
Scoped finite heartbeat limits on the larger specializations affect elaboration
only.

This is internal assembly of existing constructions, with no additional
literature identification. It asserts no existence of an automorphic
representation, restricted tensor decomposition, spectral or geometric
occurrence, canonical measure normalization, cohomological nonvanishing, or
archimedean globalization.
