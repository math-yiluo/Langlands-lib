# Ambient irreducibles for an open subgroup

This construction supplies the open-subgroup embedding used in the remark
following Renard VI.2.3 (French edition dated 9 July 2026, printed p.141,
PDF p.147), and hence in VI.3.4. It applies to any topological group, open
subgroup with its inherited topology, and field of coefficients.

The cyclicity and finite-generation lemmas allow independent group and carrier
universes. The bundled extension constructor uses a source carrier in
`Type (max uG uV)`, as required by the existing categorical open-adjunction
functor, and keeps that carrier universe for its ambient object. Applying the
constructor to a source presented in a smaller universe requires a separate
carrier-lifting comparison. It does not assert an extension of the original
action on its original vector space.

The proof first expresses each compactly induced function as a finite sum of
translates of unit functions using the published open Frobenius reciprocity
construction. If the subgroup representation is irreducible, the inverse image
of an ambient invariant submodule under the unit is either zero or the entire
subgroup representation. A submodule containing the unit of any nonzero vector
therefore contains every unit function and every compactly induced function.
Thus compact induction is cyclic over the ambient group algebra.

A nonzero finitely generated module has a maximal proper invariant submodule.
The actual smooth quotient by it is irreducible. Open Frobenius reciprocity
sends the quotient map to a nonzero subgroup intertwiner; irreducibility of its
source makes it injective. `OpenIrreducibleExtension` stores that ambient smooth
representation, its irreducibility, and this actual injective morphism into
its restriction. `openIrreducibleExtension` constructs the data.

No admissibility, local compactness, reductive structure, coefficient
compactness, dual extension, or common support conclusion is claimed here.
Those are separate steps of the uniform-support argument. This is an internal
generalization of Renard's stated norm-kernel case.
