# Factoring central GL morphisms through scalar matrices

This derived construction supports the GL split-component example associated
to Renard (2026), V.2.1, printed p.104, and Waldspurger (2003), I.1, printed
pp.238–239. The matrix index type is nonempty, and the coefficient ring is
arbitrary.

Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar` identifies the
centre of GL over every commutative ring with the scalar matrices. For a
nonempty index type, the scalar map is injective, so this identification is a
multiplicative equivalence from units to the centre.

`centralScalarFactor` takes a group-scheme morphism whose point matrices are
central on every test scheme. The inverse of the scalar-centre equivalence
extracts a unit from each point. These units are natural in the test scheme,
so the published construction from natural point homomorphisms yields an
actual group-scheme morphism to the multiplicative group.

For any morphism with the scalar-matrix point formula, the resulting factor
composes to the original central morphism. If that central morphism is a
monomorphism and the scalar morphism factors through it, the two
factorizations are inverse. This supplies the maximality argument for the
scalar split component, without assuming a structure theorem about split
components.
