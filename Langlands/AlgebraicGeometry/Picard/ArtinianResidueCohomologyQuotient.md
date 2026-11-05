# Residue cohomology across an elementary kernel quotient

This internal construction identifies the actual residue pushforward before
and after quotienting an elementary kernel by a residue-field subspace.
All schemes and rings have an arbitrary common universe. The setup uses an
augmented Artinian test over a field, an elementary surjection of such tests,
and any subspace of its kernel. It does not require a section of the residue
augmentation or an algebra structure over the residue field on the source test.

For actual scheme maps `j`, `h`, and `i` with `j ≫ h = i`,
`factorizationPushforwardIso` identifies pushforward along `i` with successive
pushforwards along `j` and `h`. It is the canonical pushforward comparison
for the equality of scheme maps followed by the inverse canonical pushforward
composition comparison. This general definition has no closed-immersion premise.

`residueQuotientIso` specializes this identification to the actual residue
immersion and its factorization through the actual subspace quotient test.
Its source is the existing `residueStructureModule` on the original relative
scheme; its target is the pushforward, along the quotient immersion, of the
same construction on the quotient relative scheme.

`residueStructureCohomologyIso_quotient` proves that the canonical cohomology
map of this sheaf identification becomes the identity under the existing
residue-structure cohomology isomorphisms. The equality is an equality of
underlying elements of the same actual residue-fibre cohomology module in
every nonnegative degree. Each comparison retains its specified augmentation
restriction of scalars. No flatness, properness or finiteness of cohomology is
assumed for this equality.

The proof first establishes a general pointwise factorization identity for
closed-immersion cohomology maps. It substitutes the two supplied equalities
of scheme maps and coefficient ring maps, applies the actual cohomology
composition theorem, and cancels the canonical pushforward composition
isomorphism with its inverse. The scalar-composition map acts identically on
underlying elements. The residue application uses the already proved residue
factorization and compatibility of the augmentation with the quotient map.
Unfolding the existing residue comparison and the canonical closed-immersion
cohomology map then identifies the same pushforward and base-ring comparisons.
The affine and closed-immersion vanishing proofs occur only as proofs of the
same vanishing proposition.

This is a formal consequence of the imported constructions and their
transitivity theorem. It does not yet identify the independently constructed
finite-product quotient map in residue cohomology coordinates, prove tensor
or obstruction naturality, or construct a Picard-stack atlas. Those remain
further obligations of the host task.
