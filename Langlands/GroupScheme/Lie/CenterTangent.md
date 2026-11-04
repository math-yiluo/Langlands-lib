# Tangents of the full scheme center

Author: Worker 1296.

This is a derived interface for actual group schemes over any commutative ring
`R : CommRingCat.{u}`. It uses the existing all-test definitions of `center`,
`Lie.elementCentralizer`, and subgroup tangent submodules. It imposes no
field, smoothness, finite type, connectedness, or reducedness hypothesis.
The assertions involving the center assume that the ambient group is affine
over `Spec R`. No smoothness hypothesis is imposed on the center.

`Lie.commute_of_mem_elementCentralizer` says that an affine point fixing an
actual tangent vector commutes with every evaluation of that vector along an
algebra map from the base dual numbers. Its proof first uses the actual
constant-point commutation condition over the coefficient dual numbers. It
then evaluates the infinitesimal parameter at the square-zero element which
is its image under the given map. The imported
`Lie.dualNumberEvaluation_factor` identifies the resulting composite.
This first assertion does not require the ambient group to be affine.

`Lie.elementCentralizer_eq_top_iff_mem_center_lie` identifies full actual
centralizer with membership in the tangent submodule of the full scheme
center. In the forward direction, each map from an arbitrary relative test
scheme to the affine group is factored through its relative affinization.
The first assertion gives commutation there, and precomposition with the
affinization unit gives the required equality on the original test scheme.
This verifies the full all-test center condition, including refinements whose
map from the base dual numbers sends the infinitesimal parameter to an
arbitrary square-zero element. In the reverse direction, restrict the center
condition along coefficient extension and test against constant group points.

For any homomorphism `z : Z ⟶ G` representing the full center functor,
`Lie.centerTangentFactor` constructs an actual element of `lieKernel Z R`
mapping to a given tangent vector with full centralizer. The construction
uses the representing points equivalence to lift the original dual-number
point. Monicity of the representing inclusion shows that its reduction is
the identity. `Lie.targetMap_centerTangentFactor` proves the exact image
formula. Finally,
`Lie.elementCentralizer_eq_top_iff_exists_center_tangent` gives the equivalent
existence of an actual tangent preimage in any such representative.

These are internal consequences of the imported actual point and
representability interfaces, rather than assertions quoted from literature.
In particular, this module does not identify a full tangent centralizer with
a full scheme centralizer. That converse requires additional hypotheses and
is a separate step. Nor does this module construct a center quotient, remove
a nonsmooth center, or prove an isogeny reduction or Cartan generation.
