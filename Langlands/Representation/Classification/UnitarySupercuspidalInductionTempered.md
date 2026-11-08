# Tempered induction of unitarizable supercuspidal blocks

Author: Worker 1811.

This module supplies a local bridge for Henniart (2000), §2.4, printed
page 445 (PDF page 7): after Théorème 2.4, the normalized induction of
unitary supercuspidal blocks is tempered. It is an internal composition of
proved Library results, rather than a proof of Théorème 2.4 or its
Corollaire. The original is registered as `henniart-2000-simple-proof`,
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

For every prime `p`, p-adic field `F : PadicField.{uF} p`, and positive
rank, all objects and analytic predicates use
`F.canonicalTopologicalData` and its topology. Supercuspidality has its
published meaning: irreducibility, admissibility, and vanishing of the
actual Jacquet quotients for proper block parabolics and their conjugates.
Unitarizability means existence of an invariant positive definite Hermitian
form.

`Langlands.Classification.unitarizableSupercuspidal_isSquareIntegrable`
proves square-integrability modulo the full center of each supplied
unitarizable supercuspidal object. The field and carrier universes are
independent. The proof eliminates rank zero using positivity and then uses
`Langlands.RankinSelberg.supercuspidal_isEssentiallySquareIntegrable` at
the resulting successor rank. Irreducibility supplies a nontrivial carrier.
`Langlands.unitarizableCentralCharacter` uses the object's admissibility,
irreducibility, and invariant positive form to supply a unitary central
character. Finally,
`Langlands.Classification.isSquareIntegrable_of_essential_of_unitaryCentralCharacter`
removes the real exponent in the essential-square-integrability witness.
The resulting square-integrability concerns the original action.

`Langlands.Classification.unitarizableSupercuspidalProduct_isTempered`
accepts any positive total rank, any ordered block shape, and actual
unitarizable supercuspidal objects with carriers in
`Type (max uF uV)`. Apply the first theorem to every positive block size.
The proved
`Langlands.Classification.squareIntegrableBlockInduction`
then gives temperedness of the normalized product induction functor's
object. Its action is definitionally
`F.canonicalTopologicalData.normalizedProductInduced B
(fun i => (σ i).obj.representation)`, as recorded by
`PadicField.TopologicalData.normalizedProductInductionFunctor_obj`.
Thus the conclusion uses the exact representation in the published
`AssociatedSupercuspidalInductionStatement`.

`Langlands.Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct`
uses
`Langlands.PadicField.TopologicalData.isTempered_iff_of_equiv`
to transfer this conclusion to any supplied equivalent action. Its
carrier has an independent universe `uW`. No smoothness, irreducibility,
admissibility or unitarity premise is added for that action; the
equivalence and the block hypotheses give the full conclusion.

The analytic temperedness conclusion quantifies over every Borel Haar
measure on the actual central quotient and every positive `δ`, with all
absolute smooth-dual matrix coefficients in `L^(2+δ)`. The proof retains
the full center, the supplied order of the blocks, normalized induction
from the standard upper block parabolic, and the right-translation action.
It does not infer temperedness from unitarizability alone.

`Langlands.Classification.UnitarizableSupercuspidalInductionTemperedStatement`
is the `Prop`-valued definition packaging the transfer theorem uniformly
over all primes, fields, positive ranks, ordered block shapes, block
objects and equivalent actions at the three independent universes
`uF`, `uV`, `uW`. The theorem
`Langlands.Classification.unitarizableSupercuspidalInductionTempered`
proves this proposition by introducing its data and applying
`isTempered_of_equiv_unitarizableSupercuspidalProduct`.

For the global application, instantiate `uF = uV = u`; the block carrier
universe then reduces to `u`, as required by Théorème 2.4. The public
theorems used above are proved in the imported modules
`SquareIntegrableBlockInductionProof`,
`SegmentSpecialSquareIntegrabilityCriterionProof`,
`TemperedTwistSupercuspidalPoleClassification`, and
`Unitary.CentralCharacterProof`. Their paired Markdown documents the
implemented proofs and source dependencies. No local Langlands
correspondence or unproved global association proposition is assumed.
This module alone does not prove
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCuspidalFactorStatement`;
its unconditional proof still requires the separate association results.
