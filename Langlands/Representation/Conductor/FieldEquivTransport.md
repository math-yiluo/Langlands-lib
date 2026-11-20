# Fixed-level conductors under change of local field

A bicontinuous field isomorphism restricts to an isomorphism of the
actual integer rings. The Lean proof uses `Ideal.map_pow` and
`IsLocalRing.map_ringEquiv_maximalIdeal` to transport the last-row
congruences of every integral representative. Applying the same argument
to the inverse gives equality of the transported level subgroup with the
target level subgroup.

A vector fixed under the pullback action at a given level is therefore
fixed under the original action at that level and conversely. The
resulting equality of fixed submodules gives the finite newvector
conductor equivalence and preserves the total first fixed level, including
infinite values. These are consequences of the Library's actual
`Conductor.levelSubgroup` and `Conductor.levelFixedVectors` definitions.
