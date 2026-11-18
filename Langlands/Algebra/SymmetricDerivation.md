# Endomorphism derivations of the genuine symmetric algebra

For a commutative ring `R`, a free `R`-module `M`, and an endomorphism
`f : Module.End R M`, `induced f` extends `f` to a derivation of Mathlib's
actual `SymmetricAlgebra R M`. There is no finite-rank assumption. Its value
on a linear generator is `induced f (ι x) = ι (f x)`.

`ofBasis` constructs this derivation using Mathlib's symmetric-algebra
isomorphism with multivariate polynomials and `MvPolynomial.mkDerivation`.
The latter sends each basis generator to the image of its original vector
under `f`. Conjugating by the algebra isomorphism preserves the Leibniz rule.
The generator formula and induction on symmetric-algebra products prove
independence from the chosen basis. `induced` chooses a basis internally.

The Leibniz rule proves `induced_mem_homogeneousSpan`: every degree-`d`
homogeneous-span submodule is preserved. `homogeneous f d` is the resulting
endomorphism of that actual submodule. The proof first treats products of
exactly `d` generators and then uses linear-span induction.

This construction is internal algebraic infrastructure for the companion
Frobenius obstruction. It formalizes the source's extension of the operator
on a representation to a derivation of its symmetric algebra. It constructs
no group-scheme representation and asserts no classification theorem.

Source: M. Demazure and P. Gabriel, *Groupes algebriques*, Tome I (1970), IV, section 3, Theorem 3.6, printed p.510 (PDF p.540). Registered source `provided-fbc22c29e33197d3b9f2e242cdac44714e2e1a2f5faa337e9ebc1d657ad1d6fe`, SHA-256 `fbb2f907cc281afba245917449bae4bca1175c35215539c700575c517069e127`.
