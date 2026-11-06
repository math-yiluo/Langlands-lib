# Original integral points under a valued-field extension

Let `F` and `L` be fields in the same arbitrary universe `u`, with supplied
valuative relations, an algebra structure `F → L`, and
`ValuativeExtension F L`. The latter says that the valuative relation on `F`
is the relation induced from `L`. There are no topology, completeness,
discreteness, finite-degree, algebraicity, or Galois hypotheses.

`integerRange_intersection` proves that the inverse image of the actual
valuation integer ring of `L` is the actual valuation integer ring of `F`.
The proof identifies the range of each integer-ring subtype inclusion with
valuation at most one. Compatibility of the two valuative relations implies
equivalence of the canonical valuations under restriction, so Mathlib's
`Valuation.HasExtension.val_map_le_one_iff` proves the result.

For a supplied `M : IntegralModel 𝒪[F] F G`, `baseChangeValued` constructs its
actual coefficient base change over `𝒪[L]`, with fraction field `L` and generic
group the existing scalar extension of `G`. The integer-ring algebra and
commuting scalar towers are Mathlib's instances for an extension of
valuations. The generic identification is the one constructed by
`IntegralModel.baseChange` from the supplied `M.genericIso`.

`mem_integralPoints_rationalExtend_iff_valued` proves that the existing
`rationalExtend F L G g` lies in the integral image of this extended model if
and only if `g` lies in the original `M.integralPoints`.
`integralPoints_eq_comap_baseChangeValued` expresses this as equality of the
original subgroup with the comap of the extended subgroup under that existing
homomorphism. Both proofs apply the coordinate-descent theorems of
`IntegralPointDescent` to the proved integer-ring intersection condition.

This is an internal specialization of affine-coordinate point descent and
Mathlib's valuation-extension algebra instances. It invokes no additional
literature assertion. The supplied integral model and its generic
identification are retained. This construction supplies no classification of
reductive models, special point, metric, building, or integral-image/stabilizer
equality, and does not prove `BuildingComparisonStatement`.
