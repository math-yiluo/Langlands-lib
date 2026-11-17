# Fibrewise root data and free root lines on arbitrary affine charts

This internal derived module transports supplied coordinate root data and
free actual root-weight lines along an arbitrary specified map from Spec A
to Spec R. The rings are arbitrary commutative rings. No flatness, local-ring,
reducedness or nontriviality hypothesis is imposed on the base map or rings.

`HasFreeRootWeightDatum i P` is a Prop-valued conjunction: P is the actual
full fibrewise root datum of the given coordinate-torus inclusion i, and
every actual root exponent weight space has a supplied linear equivalence
with the coefficient ring. It does not assert reductivity, smoothness,
closedness or maximality of the inclusion.

`splitTorus.isFibrewiseMaximalTorus_affineBaseChangedTorusHom` transports a
supplied fibrewise maximal-torus assertion along the specified affine map
and then the canonical split-torus coordinate isomorphism. It assumes the
ambient affine group is smooth, as required by the existing transport theorem.

`splitTorus.exponentWeightLine_affineBaseChange` assumes the ambient affine
group is smooth and that one actual exponent weight space is a free line.
It proves that the same exponent weight space in the pullback, expressed
using the canonical coordinate torus, is a free line over A. The proof uses
the algebra structure on A induced by the affine map. It composes the
inverse actual-weight base-change equivalence with the tensor extension of
the supplied trivialization and the tensor-unit equivalence. This preserves
the actual module, rather than only its fibrewise rank.

`IsFibrewiseRootDatumOf.affineBaseChange` transports the full supplied
fibrewise root datum P. It equips A with the induced R-algebra structure,
uses full faithfulness of Spec to identify the resulting algebra base map
with the specified chart map, and transports the existing coefficient
base-change theorem across that equality. It needs no smoothness premise.

`HasFreeRootWeightDatum.affineBaseChange` combines these two transports for
a smooth affine ambient group. The same P and all of its actual free
root-weight lines remain available on the specified affine chart.

The provenance is direct composition of the existing full fibrewise
root-datum base-change theorem, the actual affine weight-module
base-change equivalence, tensor extension of linear equivalences, and
maximal-torus base change with coordinate transport. No additional source
theorem is asserted. These lemmas construct neither compatible root-datum
isogenies nor conjugators; those remain separate inputs to the rigidity
assembly.
