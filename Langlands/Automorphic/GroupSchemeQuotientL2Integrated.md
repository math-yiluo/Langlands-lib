# Bochner integration of the original canonical quotient L2 action

This internal adapter applies the existing `integratedIsometricAction`
constructor to the original positive right regular action on the actual
positive-central quotient L2 space. Its quotient, canonical quotient
measure, null classes and group multiplication convention are unchanged.

`haarQuotientL2BoundedRightAction` bundles the original linear
representation using the continuous linear maps of its original
isometries. The original identity and multiplication laws supply its
group homomorphism laws, and the norm equality is the original isometry
law. Each original continuous orbit is strongly measurable: the actual
adelic group is second countable and has its existing Borel structure.
Thus this step does not assume separability of the full L2 space.

For any supplied measure `ν` on the actual adelic group and any specified
complex function `f` with `Integrable f ν`,
`haarQuotientL2IntegratedAction` is a bounded complex-linear operator
whose value on a vector `φ` is exactly
`∫ a, f a • quotientL2RightAction ... a φ ∂ν`.
The inherited constructor first proves absolute Bochner integrability
from the scalar majorant `‖f a‖ * ‖φ‖`. The operator norm is at most
`∫ a, ‖f a‖ ∂ν`. The application identity is definitional.

The quotient uses precisely the original
`positiveRationalQuotientHaarMeasure`, independently of the supplied
group integration measure. In particular, the latter may be specialized
to the inverse of canonical group Haar to use the right Haar convention.
This construction does not assert any convolution identity or need a
Haar property for the supplied integration measure.

All original number-field, affine locally finite-type group, supplied
central split torus, injective finite-index character restriction,
finite splitting and norm-one right-Haar hypotheses remain explicit.
There is no reductivity, finite quotient volume, pointwise L2 evaluation,
or smoothness assumption.

Provenance is internal: this is direct composition of the original
canonical quotient continuity and norm-preserving action with the
published Bochner integrated-operator construction and pinned Mathlib
continuous-map strong measurability. It claims no compactness, smoothing,
trace formula or spectral decomposition.
