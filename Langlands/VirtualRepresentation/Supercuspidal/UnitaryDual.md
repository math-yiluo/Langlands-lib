# Conditional smooth duality on the unitary supercuspidal lattice

This construction restricts the published actual smooth contragredient to the
genuine unitary supercuspidal basis over a finite p-adic field and extends it to
the free integral lattice. Field and representation-carrier universes remain
independent. A carrier need not be finite dimensional, normed or topological.
Unitarizability means existence of an actual invariant positive Hermitian form.

## Explicit theorem inputs

The construction takes proofs of the existing propositions:

- `GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}`, which supplies
  supercuspidal closure for the actual smooth dual;
- `Classification.UnitaryAdmissibleHermitianClause.{uF, uV} F T`, which supplies,
  for every positive rank, admissible smooth representation and invariant
  positive form, an equivariant conjugate-linear equivalence onto the actual
  smooth dual with the prescribed Hermitian evaluation.

The lattice operation specializes the second input to the canonical topology
of `F`. The two preliminary transport lemmas allow any compatible
`F.TopologicalData`. Neither input is proved here. In particular, this module
does not provide an unconditional unitary dual operation or prove the Hermitian
identification by an infinite-dimensional Riesz theorem.

## Construction and implemented proofs

`TopologicalData.isUnitarizable_smoothContragredient` unpacks a positive form
`b`, applies the Hermitian clause to obtain an actual conjugate-linear
equivalence `E`, and transports form existence using
`isUnitarizable_iff_of_conjugateEquiv`. That published transport pulls `b` back
along the inverse of `E` and reverses its arguments. The Hermitian clause's
evaluation identity is available but is not needed for this consequence.

`isUnitarizable_supercuspidalClassContragredient_iff` descends preservation to
actual isomorphism classes by quotient induction. The supercuspidal
representative already supplies admissibility. Applying preservation twice and
the published class contragredient involution gives reflection.

`PadicSupercuspidal.unitaryDualBasisEquiv` restricts the actual
`dualBasisEquiv` by this equivalence of membership in the unitary subset.
Its underlying class is exactly the existing dual class and its positive group
rank is unchanged. The representative lemma identifies its value on the class
of an actual object with the class of that object's smooth contragredient,
equipped with the transported unitarizability witness. Subtype extensionality
transfers the self-inverse and involution laws from the ambient basis.

`unitaryDualLatticeEquiv` is the integral reindexing equivalence of this genuine
unitary basis. The single-coefficient and generator formulas, coefficient
preservation, self-inverse, square and composition laws follow from this
reindexing and the basis involution. Induction on finitely supported integral
combinations proves that inclusion into the ambient supercuspidal lattice
commutes with the operation. The ambient dual's rank-weighted degree law then
proves `unitaryDegree_dual`. The coefficient formula and linear induction prove
the multiplicity pairing law. Surjectivity of the basis equivalence proves
preservation and reflection of the nonnegative coefficient cone.

The full ambient unramified compatibility lemmas require the supercuspidal
closure input but not the Hermitian input. They specialize the published
inverse-character duality law to the actual determinant unramified character:
dualizing a twist with parameter `z : ℂˣ` gives the twist with parameter `z⁻¹`
of the dual. Subtype extensionality restricts this identity to norm-one
parameters on unitary classes, and linear induction extends it to their
integral lattice.

## Provenance and boundaries

This is a derived construction from the published `Supercuspidal/Dual`,
`Supercuspidal/Unramified`, `Unitary/ConjugateEquiv` and
`Classification/UnitaryGenericCompatibilityStatement` modules, using Mathlib
subtype equivalences and finitely supported reindexing. The inherited
mathematical meanings and normalizations are unchanged; no new claim from
external literature is used. All implications from the two explicit theorem
inputs and all intrinsic restriction and lattice laws are proved in Lean.

The degree is the positive rank of the general linear group extended
integrally, not the dimension of its representation carrier. The pairing is
the integral coefficient pairing on the specified unitary basis. This is no
claim about a correspondence isometry, global spanning, numerical finiteness,
or identification of a representation linearly with its ordinary dual.
