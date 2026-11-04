# Actual full-product sections and conditional dominant assembly

Author: Worker 1292.

This derived development assembles the seven conclusions of
`DominantCentralizerLatticeConclusions` from finite positive-root support,
finite index of the actual split valuation image, and a bijection from the
actual `C0` subgroup onto that split image under integer valuation. These
are explicit premises. This module does not prove the structural facts and
does not prove the closed `RenardDominantComparisonStatement`.

`fullProductValuation` takes an actual pair in `C0 × F0` to the integer
valuation of its product, as an element of the actual valuation image.
`fullProductValuation_bijective` assumes a finite full-lattice transversal
`F0`. For injectivity, pass equality of product valuations to the quotient
residue. The uniformizer factors have trivial residue, so the transversal's
injectivity identifies the two representative factors. Cancel their common
valuation factor and use injectivity on `C0` to identify the uniformizer
factors. For surjectivity, choose the transversal representative of the
requested valuation's residue. The quotient of valuations lies in the split
image; surjectivity on `C0` supplies the other factor.

`isValuationSection_tildeC0_of_bijOn` passes this bijection from product
pairs to the set of actual products, using factorizations witnessing set
membership. It also records injectivity of the product-pair valuation in
the unrestricted integer dual, which is the same equality after taking
subtype values.

`isDominantValuationSection_tildeC0Plus_of_bijOn` cuts the full section by
the dominant chamber and transfers it to the actual real valuation image,
using the fiber-invariance and transport lemmas in `RenardDominantValuation`.
`chamberCompatible_positiveProducts_of_bijOn` rewrites this dominant
intersection using the separately assumed chamber-compatibility equality.
Nonrepetition on positive pairs follows by including `C0Plus` in `C0` and
restricting the full-pair injectivity result.

Finally, `dominantCentralizerLatticeConclusions_of_latticeComparison`
combines uniformizer normalization, the chamber cut and image comparison,
the dominant transversal from `RenardDominantTransversal`, the dominant
section just proved, the finite cover from `RenardDominantFiniteCover`, and
the chamber-compatible positive product result. It retains universe `u`
and uses actual rational points and actual valuation images throughout.

The provenance is elementary quotient, product, restriction and image
reasoning using the published interfaces and the focused derived helper
modules named above. To obtain the closed host target, its maximal-split
centralizer hypotheses must still imply the finite root support and the
lattice comparison through published structural theorems. No structural
conclusion is hidden in this assembly's premises or claimed as established.
