# Composite parabolic and normalization for an actual block refinement

Author: Worker 8. This construction imports the published outer preimage,
outer character, and inner refinement definitions.

For an ordered block shape `B` of rank `n` and an actual `BlockRefinement B`,
this module constructs the smaller parabolic directly as a matrix subgroup.
The outer block projection takes this subgroup into the actual inner parabolic;
the latter's projection takes it into the actual inner Levi subgroup.
No chosen identification with another group is supplied as data.

## Actual groups and maps

`composedParabolic` is the published `leviPreimage` of `refinedParabolic`.
`composedUnipotent` is the `leviPreimage` of `refinedUnipotent`. Thus the
full radical includes both the outer radical and the embedded inner radical.
`composedLeviProjection` composes the two actual projections.
`composedLeviSection` composes the two sections; its ambient matrix is precisely
the outer block diagonal embedding of the actual refined Levi element.
The projection-section law and surjectivity are proved.

`composedLeviProjection_ker_map` identifies the ambient image of the kernel
with the stated full radical. It uses compatibility of subgroup preimages
with the outer projection, followed by the inner projection's radical law.
`composedLeviProjection_ker` gives the corresponding subgroup-preimage identity.
Normality of the kernel then proves that the composed parabolic normalizes the
ambient radical. `composedLeviNormalizer` is the actual embedded Levi map into
that normalizer, suitable for constructing the action on radical coinvariants.

`composedUnipotentPart g` removes the diagonal component on the right.
`composedDecomposition` proves that multiplication gives a bijection from the
kernel times the refined Levi onto the composed parabolic. This is a type
equivalence, not a direct product of groups. All of these constructions work
over any commutative ring, with no nonempty-block hypothesis.
For a topological ring, the projection, section, and normalizer map are
continuous in the actual subgroup and matrix topologies.

## Normalization

Over a finite extension of `Q_p`, with compatible topological data `T`,
`refinedOuterModulus_projection` proves that the outer full modulus on an
inner parabolic element equals its value on the inner Levi projection.
The proof applies the already proved outer-character triviality to the inner
radical component `q * section(projection(q))⁻¹`, then cancels in the group of
positive units. The same law for the positive half follows from its canonical
square root construction.

`composedLeviModulus` multiplies the outer modulus restricted to the refined
Levi by the inner full modulus. The outer factor accounts for the rectangular
blocks between distinct outer blocks; the inner factor accounts for blocks
within an outer block. Each factor is the published determinant-norm product.
`composedLeviHalfModulus` is the complex embedding of the canonical positive
square root of this product. The half is proved equal to the product of the
two positive halves; its inverse is the product of the two inverse halves.
`composedParabolicHalfModulus` inflates the positive half through the actual
composed projection.

The full product has open kernel because that kernel contains the intersection
of the two open factor kernels. The canonical positive half has the same
kernel, and the inflated character has open kernel by continuity of the
projection. These are the smoothness inputs for subsequent actual induction
and Jacquet constructions.

## Source and outstanding obligations

This is a derived coordinate construction motivated by Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
registered source `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original printed pages 445–446 (PDF pages 6–7) were read for this work.
Proposition 1.9(c) composes parabolic triples and requires compatibility of
normalizing factors. Sections 2.1–2.2 give the standard triple and ordered
block-refinement specialization to `GL_n`; Proposition 2.3(c) gives the two
normalized transitivity identities that this construction will support.

The Lean proofs here are intrinsic split-projection and character algebra;
the module does not state or prove normalized functor transitivity. It also
does not identify the explicit determinant product with Haar scaling.
Those theorem obligations remain separate. No theorem truth, replacement
functor, quotient equivalence, or flattened-block identification is assumed.
