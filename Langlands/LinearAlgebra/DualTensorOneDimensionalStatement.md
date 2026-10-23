# Full duals of finite tensor products in dimension one

Author: Worker 174.

`Langlands.LinearAlgebra.DualTensorOneDimensionalStatement` is an internal
proposition target, not a theorem or an assumption. It ranges over an arbitrary
field, an arbitrary finite index type, and arbitrary vector spaces, with
independent universes for the field, index and vector-space carriers.

It states that the full algebraic dual of `PiTensorProduct k V` has a nonzero
functional spanning the entire dual if and only if every full factor dual has
such a functional. The same scalar-multiple condition occurs on both sides.
No finite-dimensionality, nonzero-factor, or nonempty-index hypothesis is
imposed. In particular, zero factors and the empty tensor product are covered.

This target supplies only the final linear-algebra step for the planned
Whittaker heredity proof. Its provenance is derived: a vector space has
one-dimensional dual precisely when it is one-dimensional, and a finite tensor
product of vector spaces is one-dimensional precisely when every factor is.
These facts can be derived using Mathlib's duality and indexed tensor-product
basis constructions. The statement does not identify the full dual of an
arbitrary tensor product with the tensor product of the full duals. It makes no
claim about parabolic induction, characters, equivariant quotients or Rodier's
geometric argument, and it does not assert the Whittaker theorem.

The only imports are Mathlib's actual indexed tensor product and algebraic dual.
There is no external-source transcription in this internal auxiliary target.
