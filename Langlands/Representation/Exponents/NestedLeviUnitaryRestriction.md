# Central restriction of inner exponents of an outer unitary Jacquet part

This internal construction and its laws supply the restriction step used in the
proof of temperedness in Renard VII.2.3. They are derived from the published
normalized Jacquet quotient and exponent comparison. No external-source theorem
is added by this module.

Let `q : Q → G` be an actual parabolic with its supplied rational Levi `L`,
geometric radical and multiplication isomorphism, and let `a : A → L` be a split
component. For a supplied actual inner parabolic `pL : PL → L` with rational Levi
`M`, geometric radical and multiplication isomorphism, let `b : B → M` be a split
component. A homomorphism `e : A(k) → B(k)` is supplied, with its composite into
`L(k)` equal to the original map from `A(k)`.

`innerUnitaryJacquetCentralQuotient` is the ordinary inner coinvariant projection
on the actual outer unitary module `(r_Q π)_0`, viewed as an intertwiner for the
outer split-component action. The inverse half modulus is one on central points,
so the quotient intertwines that action without a scalar correction. This map is
surjective by surjectivity of the actual coinvariant projection. Its construction
requires neither temperedness nor admissibility. Only the supplied point factor
and its compatibility are used; no continuity of that factor is imposed.

`normalizedRealPart_eq_zero_of_leviUnitaryGroupExponent` identifies a group
exponent on the actual Levi-point unitary module with a generalized eigencharacter
on the original unitary subrepresentation. The existing theorem
`normalizedRealPart_eq_zero_of_unitaryJacquetPart` then gives zero normalized real
part. This also requires neither temperedness nor admissibility.

For a tempered ambient representation `π`, the published actual-Levi
admissibility theorem makes its unitary Jacquet module admissible.
`normalizedJacquetExponent_restrict` reflects an inner exponent along the central
coinvariant quotient to a group exponent on this module. The preceding unitary
spectrum result proves that the restricted character `χ.comp e` has zero
normalized real part. This is
`normalizedRealPart_comp_eq_zero_of_innerUnitaryExponent`; it retains both the
restricted group-exponent assertion and the vanishing real part.

The field and carrier universes are independent. The field is a nonarchimedean
local field with its Hausdorff topology; the ambient rational points use their
canonical topology and supplied local compactness and nonarchimedean-group
instances. The topology and group instances on `L(k)` are the published actual
Levi ones. All original group schemes, parabolic, Levi, radical and split-component
data are retained. This result does not construct the point factor, compare root
cones, establish inner root-presentation coverage, or prove the remaining full
temperedness or square-integrability target.
