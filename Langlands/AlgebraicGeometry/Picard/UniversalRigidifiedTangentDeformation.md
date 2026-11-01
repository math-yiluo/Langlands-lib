# Actual universal parameter tangent and ordinary deformation classes

This internal construction applies to any scheme `X` over an arbitrary field
`k` with a section, and to any actual universal rigidified family on a parameter
`P`. Universality is the imported predicate on all test schemes. The sole
explicit comparison argument is the pullback/tensor preservation property
already proved in the imported module infrastructure.

`tangentDeformationEquiv` is a bijection from the actual sheaf-defined tangent
module of `P` at `trivialParameter` to `DeformationClasses preservation f`, the
subgroup of actual line-bundle isomorphism classes on the actual dual-number
thickening whose zero-section restriction is trivial. It composes the published
linear tangent-to-stalk-derivation comparison, the actual stalk-derivation to
dual-number scheme-map equivalence, universal classification on the fibre over
the trivial class, and the proved rigidified-to-ordinary deformation equivalence.
`tangentDeformationEquiv_val` records the resulting actual classifying-map and
forgetting formula.

`tangentDeformationEquiv_add` identifies tangent addition with actual tensor
multiplication of deformation classes. The proof equips the universal parameter
with the published universal commutative group structure and uses its proved
identity formula. The generic monoid tangent-addition theorem identifies the
point associated to the sum of stalk derivations with the product of their
dual-number points. Universal classification carries this product to rigidified
tensor, and the published forgetting equivalence carries rigidified tensor to
ordinary tensor. `tangentDeformationAddEquiv` packages this result as an additive
equivalence with `Additive DeformationClasses`.

This module is an internal composition of published constructions. Its proof
uses the concrete maps just described. It asserts an additive equivalence;
compatibility with arbitrary field scalars and comparison with derived H1 are
subsequent constructions.
