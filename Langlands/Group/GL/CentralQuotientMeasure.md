# Haar measure on the full central quotient of a general linear group

Worker 386 constructs
`Langlands.GeneralLinear.centralQuotientHaar` on the actual group
`Matrix.GeneralLinearGroup ι F / Subgroup.center (Matrix.GeneralLinearGroup ι F)`.
The center is the full group center, and the quotient has its canonical quotient
group law and topology. The construction imposes no compactness or chosen
normalization. It provides the right-invariant Haar measure needed when integrating
pairings of centrally covariant coefficient functions.

## Algebraic input

`GeneralLinear.centralQuotient_positiveCharacter_eq_one` works over every field
`F : Type uF` and finite decidable index type `ι : Type uI`, with independent
universes. It proves that every monoid homomorphism from the full central quotient
to the nonnegative reals has value one on every element. It assumes no topology
or continuity, and includes the empty index type.

The proof pulls the character back along the actual quotient homomorphism.
Scalar matrices commute with every matrix, belong to the full center, and have
trivial image in the quotient. Thus the pullback is trivial on scalars. The
public theorem
`Langlands.RankinSelberg.GeneralLinearUnimodularity.character_eq_one` supplies
Worker 116's unchanged diagonal/transvection argument. It concludes that the pullback,
and hence the original quotient character, is identically one. This contribution
exposes the existing theorem and documents its reuse, preserving its
normalized Haar theorem and all previous proof bodies.

## Measure construction and right invariance

The remaining generic declarations assume a topological-group topology on the
actual general linear group, local compactness of its full central quotient,
and a measurable structure on that quotient with `BorelSpace`. They require no
particular field topology or local-field structure.

`GeneralLinear.haar_centralQuotient_isMulRightInvariant` proves right invariance
for every **regular** Haar measure on this quotient. Apply the algebraic result
to Mathlib's modular character. Regularity of a right-translated measure follows
from its translation homeomorphism. Regular Haar uniqueness identifies the
translated measure with its Haar scalar factor times the original. That factor
is the modular-character value, which is one. This proves the actual
`Measure.IsMulRightInvariant` law; it is not an assumed unimodularity premise.

`GeneralLinear.centralQuotientHaar` is Mathlib's actual `Measure.haar` on the
quotient. Its associated instances prove that it is a regular Haar measure and
is right invariant. It has no specified mass on a compact subgroup. The generic
theorem above also applies to other regular normalizations.

## Actual p-adic specialization

`PadicField.TopologicalData.centralQuotientHaar_rightInvariant` takes every prime
`p`, supplied `PadicField p` and compatible `TopologicalData T`, and every rank
`n : Nat`, including zero. It installs `T.topology`, then quantifies over every
measurable structure on the actual full central quotient with `BorelSpace`, and
every Haar measure on it. Its conclusion is right invariance of that measure.
There is no additional regularity, local-compactness, countability, or
unimodularity assumption in this specialization.

The proof obtains the topological-group structure of GL from `T` and the
Hausdorff, locally compact and second-countable quotient properties from
`glBlockCentralQuotientTopology`. Haar regularity is then inferred in this actual
setting, so the generic measure theorem applies. The quotient-topology theorem
alone was not a right-invariance theorem; the modular-character argument supplies
this additional property.

## Provenance and scope

This is an internal derived construction from the existing Library general-linear
character proof and actual central-quotient topology, together with Mathlib at
pinned commit `5ed2965256430c3649e86755f9576b54eca72435`:
`GroupTheory/QuotientGroup/Defs.lean`,
`MeasureTheory/Group/ModularCharacter.lean`, and
`MeasureTheory/Measure/Haar/{Basic,Unique}.lean`.
Worker 116 is credited for the reused diagonal/transvection proof, with Worker
386 supplying the public algebraic API and the quotient construction and proofs.

No coefficient integrability, positive integrated form, Hilbert completion,
mirabolic restriction or genericity theorem is asserted. The square-integrable
genericity statement pair and every pair it imports are preserved.
