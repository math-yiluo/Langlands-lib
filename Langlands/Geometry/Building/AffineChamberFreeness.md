# Separation laws for the actual affine chamber action

This internal adapter uses the existing affine Weyl group, root stabilizer,
chamber subsets and actual affine-image action. The definitions of point
separation and wall reflections come from the generic geometry prerequisite.
The bundled chamber action and the coroot-conjugation helpers were authored by
Worker 455; this adapter was authored by Worker 1622.

Every member of a chamber is regular, and its root signs agree with those of
every other member. The implemented separation predicate for chambers therefore
does not depend on representatives. The triangle alternative follows by choosing
a regular point in the intervening chamber: its value under a separating root
is nonzero, so one of the two subpairs has opposite signs. A chamber cannot
separate itself because the square of a real root value is nonnegative.

Point separation transforms by conjugation. The proof transports the root by
composition with the inverse affine map and transports its coroot by the linear
part. The root-stabilizer condition preserves membership in the arrangement.
The actual reflection-conjugation formula then supplies the label identity.
Representative independence transfers this law to the action on chamber subsets.

These are direct internal consequences of the published root and chamber
definitions; no root-system classification or external formal proof is used.
The geometric wall-generation theorem and the generic finite-word freeness
theorem remain separate prerequisites for deducing trivial chamber stabilizers.

`chamberWallReflections Ψ x` regards the actual wall reflections as elements of
the root stabilizer. `chamber_isSeparationSystem` proves the full five-law
interface for any bundled chamber containing `x`. Involutivity follows from the
published affine-reflection involution formula. Adjacency follows from the exact
unique-separating-reflection definition of `wallReflections` and representative
independence.

`mem_closure_chamberWallReflections` lifts ambient generated-subgroup membership
to the root-stabilizer subgroup, using that each wall reflection preserves the
roots and that group homomorphisms map generated subgroups to generated
subgroups. Finally `chamber_stabilizer_eq_one` applies the generic freeness
proposition to the actual chamber action. Its explicit premises are that generic
proposition and the ambient wall-generation equality at the chosen chamber.
It concludes identity in the existing affine Weyl group. This conditional helper
retains those two prerequisite obligations; it does not claim the unconditional
affine-chamber simple-transitivity target.
