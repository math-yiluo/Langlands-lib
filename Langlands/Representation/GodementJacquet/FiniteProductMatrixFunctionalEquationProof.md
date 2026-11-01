# Normalized matrix data on a finite actual normalized product

`Langlands.GodementJacquet.finiteProductMatrixFunctionalEquation` proves
`Langlands.GodementJacquet.FiniteProductMatrixFunctionalEquationStatement`
with independent field and block-carrier universes. For a positive total rank,
it constructs normalized matrix functional-equation data on the actual
canonical normalized product from full data on its smooth admissible factors
and their supplied scalar central quasicharacters. The supplied additive
character, scalar additive Haar measure and self-duality premise are retained.
The theorem is conditional on the factor data; it supplies no unconditional
Tate, supercuspidal or general irreducible analytic base.

The implemented proof first transports the rank-indexed existence predicate
across a genuine representation equivalence. At rank zero both sides are
`False`. At successor rank it retains the same two polynomials, complex unit
and integer exponent, and applies
`GodementJacquet.normalizedMatrixFunctionalEquationData_equiv` with the
canonical residue cardinality, normalized absolute value and general-linear
Haar measure. This preserves all fields of the existing analytic-data
predicate rather than transporting only a scalar equation.

For a singleton block shape, the sum-of-sizes condition identifies the sole
block rank with the total rank. The proof uses
`singleBlockTransportedProductEquiv`, the actual single-block evaluation
equivalence, and transports the bundled factor family along its equality
with the supplied family. For an arbitrary two-block shape, positivity writes
both ordered block sizes as successors. The proof chooses the four
normalization parameters from each factor's data and invokes the published
`twoBlockMatrixFunctionalEquationInduction`.

The main induction is on the number of blocks minus one. A positive total
rank rules out an empty block family. In the successor step, the original
product is related to its head followed by its actual tail product using
`headTailProductInductionEquiv`. The induction hypothesis supplies full data
on the tail. Finite external tensor admissibility and normalized induction
admissibility supply tail admissibility. The tail quasicharacter is the
finite product of the original tail quasicharacters; evaluation as a monoid
homomorphism identifies its underlying scalar character with the product
used by `hasScalarCharacter_normalizedProductInduced`.

Only the outer two-factor construction raises the head to the common
carrier universe using `SmoothRep.universeLiftEquiv`. Admissibility is
transported by `isAdmissible_universeLift_iff`, and the head scalar-character
identity follows by applying the original identity to the lowered vector.
The recursive tail uses the original factor-carrier universe, so the
induction hypothesis is not required at progressively larger universes.
The two-block adapter supplies data on this head/tail product, and the
actual head/tail equivalence transports them back to the original product.

This is an internal derived closure proof. Its mathematical inputs are the
imported actual singleton and head/tail equivalences, normalized induction
and tensor admissibility, product scalar-character theorem, full-data
equivalence transport, and conditional two-block analytic theorem. No new
literature assertion is introduced. The inherited analytic-data predicate
retains both common convergence half-planes, all actual test/coefficient
rational continuations, both normalized Laurent-span generator equalities
with polynomial constant coefficient one, Fourier witnesses before all
coefficients, and the guarded equation for every continuation pair. Its
measure product, transpose Fourier pairing, inverse-transpose coefficient,
normalized shifts, spectral variable, central scalar and sign convention
are those of the unchanged imported definition.
