# Linear transport on actual horizontal cohomology quotients

This internal construction uses the existing horizontal complexes and their
actual kernels, differential images and quotients. The scalar field has
characteristic zero. The Lie algebra, two coefficient Lie modules and full
acting group have independent universes. Both coefficient modules use the
same Lie algebra, horizontal submodule `H`, and group representation `σ` on
the Lie algebra. Each has its own coefficient representation, covariance
proof and all-degree infinitesimal insertion proof, as required by
`HorizontalCohomology`.

The additional input is a `K`-linear map in every degree between these
existing cochain modules, with an explicit equation commuting with the two
actual horizontal differentials. This is a conditional generic construction.
Actual full operator maps are later specializations.

`map_mem_cycles` proves kernel preservation from the commutation equation
and preservation of zero. `map_mem_boundaries` treats degree zero using its
zero boundary submodule. In successor degree it sends a differential image
to the differential of the mapped original cochain, giving an actual boundary
witness.

`mapCycles` restricts the original linear map to cycles. Its underlying
cochain formula is `mapCycles_val`. The proved membership criterion for
boundaries inside cycles yields `mapCycles_mem_boundariesInCycles`.
`mapCohomology` then uses Mathlib's `Submodule.mapQ` on the actual boundary
submodules inside cycles. `mapCohomology_class` identifies its value on a
class with the class of the mapped cycle by reflexivity.

`mapCycles_id` and `mapCohomology_id` prove that the degreewise identity
induces the identity. `mapCycles_comp` and `mapCohomology_comp` prove that
composition in every cochain degree induces composition on cycles and on
cohomology. The third coefficient Lie module used for composition has its
own independent universe and the same explicit covariance and insertion
inputs. The composite differential-commutation proof is the composition of
the two supplied commutation equations. The cycle identities use linear-map
and subtype extensionality. The quotient identities use surjectivity of the
existing class projection to reduce to a cycle and its representative formula.

All natural degrees, including zero, and equivariance under every element
of the full group are retained. The provenance is internal kernel
restriction and quotient descent using the published horizontal complex and
Mathlib's quotient construction. No external literature identification,
topology, smoothness, finiteness, nonvanishing or comparison with absolute,
analytic or sheaf cohomology is asserted.

Authorship: Worker 2.
