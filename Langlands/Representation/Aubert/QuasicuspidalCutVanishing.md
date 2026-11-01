# Vanishing above the common support degree

At positive rank, every actual cut degree above `B.length - 1` vanishes for an
actual subquotient of induction from quasicuspidal data of shape `B`. This
internal prerequisite preserves the supplied p-adic topology, independent
universes and saturated actual carriers. It requires neither finite length nor
irreducibility.

`DegreesVanishAboveSupport F T B π` means that the unchanged actual product
carrier `(ActualCutComplex.diagram T π.representation).Degree k` is
subsingleton whenever `B.length - 1 < k`.

The proof first treats a single cut term. If its normalized Jacquet coefficient
carrier is zero, the actual induced smooth-function carrier is zero, since its
functions take values in a subsingleton type. A degree `k` is the actual finite
product indexed by cut sets of cardinality `k`. At positive rank their shapes
have `k + 1` blocks. Positive source block length and `B.length - 1 < k` imply
`B.length < k + 1`. The proved actual Jacquet block bound therefore kills every
coefficient carrier, and hence every product coordinate.

`degreesVanishAboveSupport_of_jacquetBlockBound` establishes this implication
for any object satisfying the block bound.
`quasicuspidal_degreesVanishAboveSupport` supplies that bound from the actual
induced-subquotient hypothesis using
`quasicuspidal_subquotient_hasJacquetBlockBound`.
No equality of Grothendieck classes or choice of a split filtration is used:
the actual carriers themselves are zero.

The Jacquet quotient map onto the coinvariant carrier is surjective.
Consequently, `jacquet_degree_subsingleton_of_aboveSupport` proves that each
normalized Jacquet carrier of each higher degree is zero, at every shape `C`.
No association restriction on this vanishing is needed.

This supplies the upper-vanishing clause of `JacquetConcentratedAt` at
`m = B.length - 1` for the family of Levis associated to `B`. Initial
injectivity and range-kernel equality below `m` remain to be proved for the
existing actual Jacquet images of the signed cut differentials before the
concentration-reflection and terminal-effectivity theorems apply. This module
does not prove those clauses or the unconditional signed-effectivity
statement. Rank zero is handled separately by the existing rank-zero
effectivity theorem.

The provenance is internal: the actual Jacquet block bound, the existing
cut-shape length identity, pointwise induced-function carriers, finite-product
carriers and surjective actual Jacquet quotient maps give the result.
