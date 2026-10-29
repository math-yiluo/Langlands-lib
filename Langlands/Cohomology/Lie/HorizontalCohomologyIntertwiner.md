# Equivariant transport on the actual horizontal cohomology quotient

Author: Worker 2.

This internal construction combines the published actual horizontal quotient
transport and quotient action. It restricts an equivariant chain map to the
existing cycle representations and descends it to the existing cohomology
representations. No new cycle, boundary, quotient or action is supplied by the
result.

Let `K : Type u` be a characteristic-zero field and let `L : Type v` be a
`K`-Lie algebra. The coefficient Lie modules `M : Type w` and `N : Type w'`
have independent universes. Let `G : Type ug` be a group, `H : Submodule K L`,
and let `σ`, `ρ`, `τ` be the existing representations of `G` on `L`, `M`,
`N`. The bracket covariance, the two coefficient covariances and the two
all-degree infinitesimal insertion identities are the same inputs used by
`HorizontalCohomology`. They fix the actual horizontal full-group-equivariant
complexes and their differentials. No dimension or finite-group hypothesis is
imposed, and every natural degree, including zero, is allowed.

Let `P : Type up` be a monoid. The supplied degreewise representations
`actionM` and `actionN` act on those horizontal cochains and commute with
the respective actual differentials, as witnessed by `hActionM` and
`hActionN`. The source and target cycle and quotient actions are exactly the
ones constructed in `HorizontalCohomologyAction`. They use kernels of the
actual differential and its actual image boundaries; degree-zero boundaries
are zero. The explicitly named local additive groups on the cochain and
cycle subtypes are the canonical `Submodule.addCommGroup` structures.

The input `cochainMap q` is an intertwiner from `actionM q` to `actionN q`.
Its additional condition `hMap` says that it commutes with the same actual
differentials. `mapCyclesIntertwiner q` has the existing cycle
representations as source and target. Its linear map is the existing
`mapCycles` of the underlying cochain maps, as stated by
`mapCyclesIntertwiner_toLinearMap`. Subtype extensionality reduces its
intertwining law to that of `cochainMap q`. `mapCyclesIntertwiner_val`
identifies the underlying cochain with `cochainMap q f.val` by reflexivity.

`mapCohomologyIntertwiner q` has the existing quotient representations as
source and target. Its linear map is exactly the published `mapCohomology`,
as stated by `mapCohomologyIntertwiner_toLinearMap`. The quotient map already
preserves boundaries by the chain-map condition. To prove equivariance,
choose a cycle representing the source class, use the existing class-action
and class-transport formulas, and apply the cochain intertwining law on the
underlying cycle. Thus no quotient equivariance is assumed.

`mapCohomologyIntertwiner_class` identifies the image of a class with the
class of the transported cycle. This is a definitional equality.
`mapCohomologyIntertwiner_class_comp` is the same naturality square as an
equality of bundled intertwiners with the actual quotient projections. Its
proof uses intertwiner and linear-map extensionality, followed by reflexivity.
`mapCyclesIntertwiner_id` and `mapCohomologyIntertwiner_id` say that identity
cochain intertwiners induce the identity on the cycle and quotient
representations. They follow from the existing linear transport identity laws.

For a third coefficient Lie module `V : Type w''` with the same kinds of
covariance and insertion data, a third action `actionV` commuting with its
actual differential, and a second equivariant chain map `secondMap`,
`mapCyclesIntertwiner_comp` and `mapCohomologyIntertwiner_comp` prove that
restriction and descent preserve composition as equalities of bundled
intertwiners. In `(secondMap q).comp (cochainMap q)`, the first applied map
is `cochainMap q`. The composite chain-map condition follows by successive
application of the two given chain-map conditions. Intertwiner extensionality
and the published linear transport composition laws prove both equalities.

The provenance is the internal combination of
`HorizontalCohomologyTransport` and `HorizontalCohomologyAction`, using
Mathlib's bundled representation intertwiners. All new equivariance and
naturality laws are proved. Full `G` equivariance is retained. The actions
of `P` are algebraic; no continuity, smoothness, finite dimensionality,
nonvanishing, analytic or sheaf comparison, actual arithmetic specialization,
or relative-to-absolute injectivity is asserted.
