# Coherent Hom functors on coefficient algebras

For fixed finite-coordinate formal O-modules M and N over an O-algebra R,
this module constructs their integral and rational Hom functors on the
category of commutative R-algebras. This is an internal coherence
construction needed for restriction of morphisms on open sets.

`overAlgebra M A` extends M along the structural O-algebra map R → A.
The O-algebra structure on A is the composite O → R → A, using the
existing `coefficientAlgebra` and `coefficientScalarTower` constructions.
For an R-algebra morphism φ : A → B, `coefficientAlgHom` forgets to the
induced O-algebra map. `overAlgebraIso` identifies the successive
extension of M through A and φ with its direct extension to B. Its
forward and inverse maps have identity coordinates; equality of their
laws follows from φ commuting with R.

`Hom.algebraMapLinear` extends actual homomorphisms along φ and composes
with these canonical comparisons. The resulting coordinates are exactly
the original coordinates with φ applied to their coefficients. This
formula proves the identity and composition laws for coefficient maps,
and preservation of identity and composition of formal homomorphisms.
Linearity follows from the existing bilinearity of formal composition
and linearity of coefficient extension. `algebraHomFunctor` packages
these maps as a functor to O-modules.

`RationalHom.algebraMapLinear` is scalar extension of the constructed
integral restriction map to F. Tensor induction proves its analogous
functoriality and preservation of formal composition. The resulting
`rationalHomFunctor` is a functor to F-modules. It uses the actual
F tensor_O Hom, with no additional fraction-field hypothesis required
for this functor construction.

This module constructs no Hom sheaf or local quasi-isogeny condition.
The coefficient algebra universe may be different from the base and
field universes. No source theorem is asserted: the provenance is the
algebraic coherence of the existing power-series and tensor operations.
