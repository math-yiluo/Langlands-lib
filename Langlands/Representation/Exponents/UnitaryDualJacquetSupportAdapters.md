# Adapters for prescribed unitary dual-exponent support

This internal prerequisite constructs an actual dual eigenfunctional and
collects derived adapters for
`GLUnitaryDualJacquetTemperedSupportStatement`. They use the published actual
opposite Jacquet module and normalized opposite induction. The final support
statement remains a separate proof obligation: this module does not construct
an irreducible scalar quotient or establish analytic temperedness of its
inducing representation.

All declarations are in `Langlands.UnitaryDualJacquetSupport`.

- `moduleFinite_of_irreducible` installs the supplied irreducibility instance
  and uses Mathlib's simple-module finiteness instance to obtain finite
  generation over the complex group algebra. The group and representation
  carrier universes are independent.
- `jacquetAction_eq` identifies `OppositeSupport.jacquetAction` with the
  action of `CuspidalJacquetMultiplicity.oppositeJacquet` by definitional
  equality. Both use the same actual opposite-unipotent coinvariants and the
  same normalized action.
- `jacquet_admissible` extracts admissibility from the supplied analytically
  tempered source and applies
  `Parabolic.isAdmissible_standardOppositeJacquet` to its bundled opposite
  Jacquet module.
- `levi_compactOpen_cofinal` applies the published product-Levi compact open
  neighborhood basis to each open subgroup at the identity, giving a compact
  open subgroup contained in it.
- `exists_dualEigenfunctional` uses the nonzero ordinary character space in
  `IsDualJacquetExponent` to choose a nonzero algebraic dual vector. Evaluating
  its transpose eigenvector equation on every vector gives
  `phi (rho (blockScalarLevi a) v) = (chi a : Complex) * phi v`. The transpose
  has no character inversion or complex conjugation; the prescribed character
  and block shape are retained.
- `dualEigenfunctional` chooses that actual algebraic dual functional from
  the proved existence theorem. `dualEigenfunctional_ne_zero` and
  `dualEigenfunctional_apply` expose its nonzero and prescribed-character
  properties. The choice has no asserted uniqueness or canonicity.
- `classExponent_of_quotient` takes an actual surjective intertwiner from the
  whole opposite Jacquet module to an independently carried irreducible
  admissible representation. The top subrepresentation, its subtype map,
  and composition with the supplied quotient witness the published actual
  class-exponent predicate. This needs no subquotient-to-quotient promotion.
- `embedding_of_quotient` applies
  `OppositeSupport.quotient_iff_embedding`. Under source smoothness and source
  and target irreducibility, it turns the supplied whole-Jacquet quotient
  into an actual injective intertwiner from the source to normalized
  opposite parabolic induction.

These are internal consequences of the imported Library constructions and
Mathlib, rather than a separately cited analytic theorem. Field, source
carrier and constituent carrier universes remain independent wherever those
objects occur. No extra smoothness condition on the full dual functional,
finite-length assertion, tensor presentation, analytic comparison, or
semisimplicity assumption is introduced. Finite generation of the actual
opposite Jacquet module, extraction of an irreducible scalar quotient, and
its analytic temperedness still require their own proofs before the exact
support theorem can be assembled.
