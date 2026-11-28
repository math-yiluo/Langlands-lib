# The ambient estimate for the actual density ratio

`exists_weightedCAmbientCompactBound` works with the compact pictures at the
vertices `x = P_s` and `y = P̃_s` and at the translated vertex `θ = s·P`.
The ambient continuation system uses the given compact subgroup and
Iwasawa decompositions. The density packages have nonzero canonical
scalars and satisfy `CommonCompactNormalization`. The other inputs are
the two generic comparison data for `y → θ` and `x → y`, a nontrivial
irreducible inducing representation square integrable modulo the actual
split center for the given quotient Haar measure, a fixed invariant
positive form on that representation, and a split component of the
represented parameter Levi. The theorem gives regular functions `a` and
`d` and a set `S`, open and
dense in the unramified characters and on their unitary subgroup, such that:

- every point of `S` is regular for the five vertices, and lies in the
  generic loci of both comparisons, and `d` does not vanish there;
- the cleared weighted tensor numerator `galleryWeightedNumerator`, with
  scalar numerator `a` and denominator `galleryWeightedDenominator d`,
  satisfies `HasClearedUnitaryBound` in the fixed compact tensor norm;
- on the weighted domain, wherever the lifted parameter lies in `S`, the
  actual density ratio `µ^G · (µ^{M'})⁻¹` equals `a/d`.

The region is the one from `exists_weightedCScalar_roundTrip`, intersected
with the dense open regions of the two comparisons.
`exists_actual_induction_irreducibility_factor` supplies the irreducibility
hypotheses. `isDistanceAdditive_auxiliary` supplies the distance condition for
`y, θ, x`. `galleryWeightedCompact_hasClearedUnitaryBound` gives the bound.

This is the ambient part of Lemma V.2.2 and the boundedness step of the
proof of Corollary V.2.3 in Waldspurger, printed pp. 293–294 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). The
quotient measures are those of the given compact pictures, so the identity is
only up to the positive constant `κ`, which is enough for boundedness.
