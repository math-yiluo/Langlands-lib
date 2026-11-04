# Residue fields of finite diagonalizable groups

This internal prerequisite proves that the full group algebra `k[A]` of a finite
abelian group over any field has finitely many prime points and that every prime
residue field is a finite separable extension of `k`. It retains characteristic
torsion and all nilpotents in the group algebra. Neither reducedness nor an
étale structural morphism is asserted.

The proof first shows that an element of finite multiplicative order in any field
extension is separable. Its actual order has nonzero image in the field, by
Mathlib's primitive-root order lemma. The polynomial `X^order - 1` is consequently
separable over the base field and annihilates the element. Its minimal polynomial
divides this separable polynomial.

For an algebra homomorphism from `k[A]` to a field, each monomial image has finite
multiplicative order. The additive monoid algebra induction principle writes any
image as a finite sum of scalar multiples of these monomial images. Closure of
separable elements under sums and products proves separability of every image.
A surjective algebra homomorphism therefore makes the target field separable.

The group algebra is finite as a module, hence Artinian. Its prime spectrum is
finite and every prime ideal is maximal. The algebra map from the group algebra
to a maximal residue field is surjective and finite as a module. The actual
canonical algebra map is exposed as `groupAlgebraResidueFieldMap`, with a
surjectivity theorem when the indexing group is finite. Module
finiteness passes down the scalar tower, and the image argument gives
separability. These are the implemented steps for the two residue-field
instances.

The provenance is internal, using Mathlib's proved order, polynomial,
separable-element, monoid-algebra and Artinian-ring results. This file does not
choose a common splitting extension, construct reduced components of a group
scheme, select a dominating torus component, or prove unipotent splitness or
maximal-torus conjugacy.
