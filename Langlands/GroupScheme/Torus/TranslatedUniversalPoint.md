# Translation of the universal split-torus point

This module provides internal infrastructure for the coefficient proof motivated
by Milne, *Algebraic Groups* (2017), Theorem 12.12, printed pp.234–235
(PDF250–251). That source expands a representation in the group-like basis and
identifies its coefficients as weight vectors. The translation construction and
identities here are derived infrastructure over an arbitrary commutative base;
the module does not yet assert the weight decomposition.

Let `R : CommRingCat`, let `I` be a finite type in the same universe, and let `A`
be any commutative `R`-algebra. For a family `t : I → Aˣ`,
`splitTorus.translatedEvaluation I t` is the `R`-algebra homomorphism
`R[I → ℤ] → A[I → ℤ]` that sends a monomial with coefficient `r` and exponent
`m` to the same monomial with coefficient
`algebraMap R A r * ↑(∏ j, t j ^ m j)`. The product and integer powers
are taken in `Aˣ`, as implemented by the published `splitTorus.exponentValue`.

`translatedEvaluation_single` proves this defining formula, and
`coeff_translatedEvaluation` proves it for each coefficient of every finite
Laurent polynomial. The latter proof uses linear induction on its finitely
supported coefficient family.

`universalPoint_translatedEvaluation` identifies the image of the actual
universal split-torus point under this algebra map. It is the product of the
constant extension of `t` and the coefficient extension of the universal point
to `A[I → ℤ]`. The proof uses the existing point equivalence with families of
units and checks each coordinate. This preserves the published split torus and
its actual scheme points.

For any affine group scheme `G` over `Spec R`,
`kernelCoefficient_translatedEvaluation` says that changing a Lie vector along
translated evaluation multiplies its `m`-th coefficient, extended from `R` to
`A`, by `exponentValue I t m`. The vector belongs to the actual dual-number
identity kernel, with its existing epsilon-scaling module structure. The proof
uses its identity-derivation coordinates, the coefficient formula, and
naturality under algebra maps. It needs neither local finite type nor a field.
