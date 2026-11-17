# Actual smooth closed multiplicative-type centralizers

For every homomorphism from a commutative multiplicative-type group into a
smooth affine group over any scheme `S`,
`relativeMultiplicativeTypeCentralizerModel` chooses an actual smooth closed
group scheme over `S` representing the full all-test centralizer. The original
homomorphism need not be an immersion. Multiplicative type retains the
published fppf-local diagonalizability meaning, including finite nonsmooth
subgroups.

This is derived infrastructure. The all-test commutation equation is detected
after an arbitrary fppf covering family: pull the cover to each test scheme
and use subcanonicity to identify the two product morphisms. Therefore the
centralizer equals the subgroup descended from its local base changes.
`CoverDescent.isClosedRepresentable_subgroup_fppf` glues closed local models.
For a diagonalizable source, the affine base cover and the existing ring-level
smooth centralizer models supply those local models. The multiplicative-type
splitting cover then supplies them for arbitrary source groups of that type.
Finally the existing supplied-representative smoothness theorem proves
smoothness of the chosen global representative.

The full representing property is retained for use inside normalizers when
constructing their Weyl quotients. No assertion about reductivity or local
finite presentation of the original subgroup is added.
