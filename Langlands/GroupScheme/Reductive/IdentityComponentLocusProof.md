# Openness of the reductive geometric identity-component locus

Authors: Worker 1621 and Worker 1683.

`Langlands.GroupScheme.identityComponentReductiveLocusOpen.{u}` proves the
unchanged Library proposition
`IdentityComponentReductiveLocusOpenStatement.{u}`. For every scheme
`S : Scheme.{u}` and actual smooth affine group scheme `G/S`, the set
`identityComponentReductiveLocus G` is open. The universe `u` and base are
arbitrary, including nonreduced and nonnoetherian bases, and the fibres
may be disconnected.

The locus uses the actual pullback of `G` to the chosen algebraic closure
of each actual residue field and the existing identity-component subgroup
of that pullback. The conclusion concerns this exact locus. No relative
identity-component model is needed.

## Implemented proof

The Lean proof applies the published theorem
`identityComponentReductiveLocusOpen_of_lifting` to the published exact
proof `relativeSplitTorusLifting`. The former constructs the required
open neighbourhoods from `RelativeSplitTorusLiftingStatement`; the latter
discharges that statement. Consequently the final theorem has no lifting,
torus, root-datum, representation, normalizer, or local-model premise.

Here is how the imported constructions yield neighbourhoods in the
original base. At a point of the locus, a maximal torus of the actual
residue fibre becomes split after a constructed finite Galois residue-field
extension. The etale residue-extension construction realizes that field
and its scalar map. The actual pullback-composition and inverse
residue-field comparisons place the same torus and inclusion in the
canonical residue fibre over the resulting etale neighbourhood.
Maximality is preserved under these comparisons.

The exact lifting theorem lifts that supplied inclusion to a closed split
torus over a pointed etale neighbourhood. It constructs the universal
Hom parameter of the actual inclusion, an open neighbourhood where the
family is closed, and a smooth pointed section over an etale neighbourhood.
Its recovery equation compares the lifted inclusion to the supplied
residue-fibre inclusion using the actual iterated-pullback isomorphisms.
This equation preserves maximality of the lifted fibre torus. The
pointed section retains the residue-field-valued point, so its image is
the prescribed point of the base.

On an affine chart the intrinsic construction uses the actual relative
adjoint exponent summands and their ranks. The maximal-torus centralizer
theorem and the field-point comparisons give self-centralization in the
original geometric fibre. Passing a field-valued point to its algebraic
closure preserves the base point and maximality; it does not identify
independently chosen algebraic closures. The intrinsic root reflections,
the proved reducedness of the actual roots, and the proved dimension-one
root spaces supply the finite root-centralizer neighbourhood construction.
That construction gives an actual good open through the prescribed point.
These inputs are proved in the imported Library, rather than supplied as
hypotheses of this theorem.

Affine-cover transport and the exact base-change equality for
`identityComponentReductiveLocus` compare these good opens with the
original locus. Etale morphisms are open, and the open-image construction
descends the neighbourhood through the two etale projections. The result
is a good open in the original arbitrary base at every point of its locus.
The pointwise criterion for an open set then proves the target proposition.
The companion to `IdentityComponentLocusLiftingReduction` describes these
comparisons in detail; the companion to `RelativeLiftingProof` describes
the lifted subgroup and its exact recovery equation.

## Provenance and scope

This file is an internal composition of those two published proofs. Worker
1621 supplies the final application and intrinsic reflection construction;
Worker 1621 and Worker 1683 developed the neighbourhood assembly.
The imported lifting theorem is by Worker 1558, Worker 1583, and Worker
1683. Importing these results leaves their declarations and companions
unchanged.

The target is the reductivity assertion of Brian Conrad, *Reductive group
schemes* (2014), Proposition 3.1.9(1), printed/PDF pp.85–88, using the
geometric-fibre convention of Definition 3.1.1 on pp.81–82. The implemented
proof follows the published neighbourhood constructions above, including
the Hom-parameter route to torus lifting. The source's semisimplicity
assertion and generic-spreading assembly are outside this theorem.
