# Unitary similitude group functor

For a commutative ring `R`, an associative unital `R`-algebra `A`, and an
`AlgebraInvolution R A`, this module constructs the group of pairs
`(g,c) ∈ Aˣ × Rˣ` satisfying `g σ(g) = algebraMap(c)`.

The group is an actual subgroup of the product of the two unit groups.
Internally it is the equalizer of two multiplicative maps: projection to `g`
and the map `(g,c) ↦ c σ(g⁻¹)`. The latter is multiplicative because scalars
commute with every element and inverse-involution is multiplicative.
`mem_similitudes_iff` proves equivalence with the displayed source equation.
The multiplier and underlying unit are actual group homomorphisms.
`underlyingUnit_injective` proves that recording the multiplier adds no
information when the scalar embedding is injective.

The unitary subgroup is defined by `g σ(g) = 1`; `unitaryEquivKernel`
constructs its multiplicative equivalence with the multiplier kernel, including
both inverse certificates. No surjectivity of the multiplier is asserted.

`map` constructs maps on similitudes from ring maps commuting with the
involutions and scalar embeddings. `baseChangeMap` uses the actual tensor
product maps constructed in `Involution`. `similitudeFunctor` is a functor
from Mathlib's `CommAlgCat R` to `GrpCat`. Its value on `S` is the similitude
group of `S ⊗[R] A` with the coefficient factor fixed by the involution.
Identity and composition are proved from the tensor-product maps.

The ring, algebra, and coefficient carrier universes are independent; the
group carrier lies in the maximum of the algebra and coefficient universes.
No topology, ambient complex star, dimension, or field structure is presumed.
This is a concrete group functor. Affine representability, reductivity,
Harris's CM/signature specialization, and Shimura canonical models are separate
mathematical obligations.

Original sources: Harris 1999, *Galois properties of cohomological automorphic
forms on GL(n)*, Section 1, printed page 301, defines the unitary equation and
requires the similitude factor to lie in the rational multiplicative group.
Kottwitz 1992, *On the λ-adic representations associated to some simple Shimura
varieties*, Section 1, printed page 654, gives this group on every commutative
rational algebra and identifies the multiplier kernel with the restricted
unitary group. Our generic construction is the algebraic prerequisite for
that specialization, with explicit multipliers so that even nonfaithful scalar
extensions have a well-defined functor.

Dependencies: the paired `Involution` module and pinned Mathlib subgroups,
equalizers, units, tensor algebras, and bundled algebra/group categories.
Implementation and all intrinsic certificates are by Worker 57.

Exact retained sources: `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; `kottwitz-1992-lambda-adic-simple-shimura`, SHA256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`. The locators above refer to these files. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435` with Lean `4.34.0`.
