# Noetherian models for the fibrewise-isogeny argument

This module isolates the noetherian approximation input in Conrad's proof
of Proposition 6.1.10, *Reductive group schemes* (2014), p.192. The source
first obtains a quasi-finite flat surjection, then reduces to a noetherian
base by limit arguments. The interface here records the actual
homomorphism and its recovery, so subsequent reductions preserve the map
appearing in the original target.

`NoetherianQuasiFiniteModel f` consists of a noetherian subring of the
original base ring, reductive source and target groups over its spectrum,
and a locally quasi-finite flat surjective homomorphism between them.
Two group-scheme isomorphisms identify the original groups with these
models after base change along the subring inclusion. The recovery
equation says that these isomorphisms carry the original supplied
homomorphism to the base change of the model homomorphism.

`ReductiveQuasiFiniteNoetherianModelStatement` asserts existence of such
a model for every locally quasi-finite flat surjective homomorphism of
reductive groups over an arbitrary ring, in every universe. It does not
assume or assert that either homomorphism is finite. The base subring is
required to be noetherian; finite generation over the integers, which
would be stronger and sufficient, is not part of this interface.
This existence proposition is **not proved** in this module.

The formulation is a derived version of the source's limit reduction.
An independent proof can descend smooth affine group models and the
homomorphism to finitely generated coefficients, then enlarge those
coefficients until reductivity, local quasi-finiteness, flatness, and
surjectivity hold. The published `DirectLimitReductiveStatement` and
`Descent.FiniteCoefficient.HomGeneralStatement` are related input
propositions with separate proof obligations; this module does not
claim their proofs or an implementation of that approximation route.
All models use subtypes of the original ring in the same universe.

The implemented helper
`isogeny_of_quasiFinite_flat_surjective_over_field` proves that a
quasi-compact locally quasi-finite flat surjective group homomorphism
over a field is an isogeny. Its actual kernel is a quasi-compact locally
quasi-finite scheme over the field, hence finite by Mathlib's
`IsFinite.of_locallyQuasiFinite`. The published finite-kernel fpqc
descent theorem then makes the homomorphism finite.

`isFibrewiseIsogeny_of_quasiFinite_flat_surjective` applies that argument
to every residue-field fibre. The four morphism properties needed in the
field argument are preserved by the actual base-change pullback square.
`isFibrewiseIsogeny_iff_quasiFinite_flat_surjective` combines this result
with the earlier forward reductions for smooth groups. Its source
structure map is assumed quasi-compact and its target structure map
quasi-separated; the reverse direction uses these hypotheses to obtain
quasi-compactness of the homomorphism.

`isogeny_of_noetherianQuasiFiniteModel` assumes a supplied model and the
DVR criterion. The helper gives fibrewise isogenies of its homomorphism,
the noetherian affine DVR reduction gives an isogeny, and base change
and the recovery equation transfer the isogeny to the specified original
map. The final two theorems use the unproved model-existence proposition
and the DVR criterion as explicit hypotheses to deduce respectively the
affine criterion and the unchanged arbitrary-base target.

The source supports the approximation formulation; the conditional
proofs are internal consequences of the named Library constructions.
The unconditional arbitrary-base theorem remains open.
