# Common origins and exact depths for coherent SL2 coordinates

This internal construction works over an arbitrary field `k : Type u`. Fix
`i : S → G`, with the monomorphism and affine hypotheses required for the
actual normalizer action, and a represented `CentralizerDatum Z` whose group
is a torus. `CentralizerDatum.asTorus` retains its actual group and maps and
uses torus commutativity to view it as a commutative group scheme. Supply an
`AlgebraicSL2RootCoordinates C` record for `i`, `Z.j`, `Z.s`, and `b`.

Assume that the image under `C.rho` of the standard SL2 Weyl matrix belongs
to `normalizerPoints i`. `weylNormalizer` is this actual normalizer point.
For an integer valuation `v` and a supplied `KPApartmentData A`,
`coordinateOrigin` is the midpoint of an arbitrarily chosen apartment point
and its image under this normalizer. The apartment is already nonempty;
this construction does not assert existence of apartment data.

The main proved result, `AlgebraicSL2RootCoordinates.coordinateOrigin_depths`,
requires full `IntegerValuation.IsOmegaCompatible v A Z`, connected
reductivity of `G`, maximal splitness of `i`, `b ∈ relativeRoots i`, affine
underlying schemes for `S` and `Z`, and a supplied additive valuation `w` on
`C.extension` satisfying `IntegerValuation.IsNormCalibrated v w`. At the
single origin `x = C.coordinateOrigin Z hZ A hn`, it proves both equalities
for every `t` in the same coordinate field:

- `x.val b (C.positive.equiv (Multiplicative.ofAdd t)) = w t`;
- `x.val (-b) (C.negative.equiv (Multiplicative.ofAdd t)) = w t`.

The stronger helpers `val_positive_of_fixed` and `val_negative_of_fixed`
hold at any point fixed by this Weyl normalizer. These results do not need
henselianity directly: it is enough that the supplied extension valuation
has the stated norm calibration.

## Implemented proof

The elementary matrix identities show that the Weyl matrix squares to the
diagonal at `-1`, and that for `t ≠ 0` the product
`lower(-t⁻¹) * upper(t) * lower(-t⁻¹)` is
`diag(-t,-t⁻¹) * Weyl`. Transport through the common homomorphism gives
`opposite_factorization`, `opposite_factor_pair`, and
`opposite_factor_pair_normalizer`. Both factors lie in the actual negative
root group. The product normalizes the supplied torus because it is an
actual centralizer coroot point times the supplied Weyl image.

The square of the Weyl normalizer is `Z.toNormalizer (C.corootPoint (-1))`.
This centralizer point has square one. The generic helper
`IntegerValuation.IsOmegaCompatible.smul_eq_self_of_mul_self` proves that
a centralizer point of order dividing two has zero translation: twice its
translation vector is zero, and multiplying by the real scalar one half
makes the vector zero. Thus the square of the normalizer fixes every
apartment point. The midpoint fixed-point theorem proves
`weylNormalizer_smul_coordinateOrigin`.

For a nonzero upper parameter, the published opposite-pair displacement
comparison, used through `val_eq_half_centralizer_of_pair`, gives one half
of the positive centralizer root pairing at the coroot parameter `-t`.
The calibration theorem gives that pairing as `2 • w(-t)`. An additive
valuation has `w(-t) = w(t)` and finite value at nonzero `t`, so division
by two yields exactly `w(t)`. The identity parameter case follows from
the valuation's value at one and `w(0) = ∞`.

The actual opposite pair at upper parameter one negates `b` by the
published opposite-pair Weyl-action theorem. Centralizer factors have
trivial Weyl action, so `weylNormalizer_root` proves that the common
Weyl normalizer itself negates `b`. The explicit SL2 conjugation identity
then carries the lower parameter `t` to the upper parameter `-t` in the
normalizer action on valuation families. At a fixed point, the negative
depth is therefore the positive depth of `-t`, which is `w(t)`.

## Provenance and scope

This is a derived internal application of the existing algebraic
coordinate records, elementary SL2 matrix identities, apartment midpoint
action, actual opposite-pair displacement and Weyl-action results, and
coroot calibration. No additional source-level assertion is made. The
coordinate record, actual Weyl normalization, apartment, and norm
calibration remain supplied data. This focused unit does not prove
coordinate existence or the SU3 branch of
`QuasiSplitValuedRankOneCoordinatesStatement`.
