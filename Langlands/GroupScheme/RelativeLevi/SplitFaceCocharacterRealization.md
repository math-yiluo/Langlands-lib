# Actual groups of a face-height cocharacter realization

Fix an arbitrary commutative ring, an affine group scheme, a supplied split parabolic face chart, and actual root parametrizations for its root datum. `faceRealization` chooses a coordinate cocharacter realizing a positive integral multiple of the chart's integral face-height functional on the entire root span. Its extension and multiplier are choices. The chart's secondary weights remain the original unscaled face heights.

`faceMultiplier` is the positive natural multiplier and `faceCocharacter` the resulting coordinate cocharacter. `facePairing` proves the precise root-pairing formula. Positive roots have nonnegative pairing, and negative roots have nonpositive pairing; the latter follows by negating roots and using linearity.

Under reductivity, fibrewise maximality of the supplied split torus, the supplied fibrewise root datum, and actual root parametrizations, `unipotent_faceCocharacter` proves equality of the realized cocharacter's actual contracting subgroup functor with that of the original cocharacter on every scheme test. No field, nontrivial-ring, or regularity assumption on the original cocharacter is needed here. The proof uses the actual open big cell indexed by the chart's base, multiplies the chart's secondary weights by the positive realization multiplier, and applies the existing supported-coordinate representation theorem. Positive scaling preserves precisely the zero weights, so the same actual scaled inclusion represents both contracting functors. `isRepresentedBy_faceCocharacter` then identifies the realized contracting functor using the original unscaled positive term and original ambient inclusion.

For a nontrivial base ring, `parabolic_faceCocharacter` also identifies the actual parabolic subgroup functors. It applies the previously proved fixed-torus theorem that equality of contracting functors determines the parabolic. This step uses actual root-sign detection and centralizer comparison; equality of parabolics is not assumed from a formal face label.

This is a derived interface for realizing canonical face filtrations. It does not establish compatibility across different tori, global descent, or the final relative radical filtration statement.

Provenance: internal combination of the root-span cocharacter realization, actual split big-cell comparison, positive root-weight scaling, and fixed-torus parabolic comparison.
