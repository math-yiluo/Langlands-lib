# Rectangle coordinates for JPSS Section 4.10

This is derived algebraic data for the two rectangles in JPSS (1983), Section
4.10(2), printed page 419. The registered source is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The coordinate change is an internal construction used to formalize covariance;
it is not an additional displayed formula attributed to JPSS. Its mathematical
design was supplied by Worker 484.

The dependent two-block family is `m : Fin 2 → ℕ`, with
`h : ∑ i, (m i + 1) = t + 1`. Set `a=m 0+1` and `b=m 1+1`.
For any field `K` in any universe, and an actual element `u` of the existing
`lowerBlockUnipotent h K`, the existing `diagonalBlocks` extraction gives
`uA ∈ N_a` and `uB ∈ N_b`. The definitions `leftMultiplier` and
`rightMultiplier` are the actual matrices `LA=w_a uA w_a` and
`LB=w_b uB w_b`, using the Library's unsigned long Weyl matrices. Their
entry laws reverse both indices. Their determinants are one: the proofs
use determinant multiplicativity, the determinant one of upper unipotents,
and `w*w=1`.

`Rectangles m j k K` is the product of the actual `a × k` and `j × b`
rectangular matrix spaces. `rectangleChange h j k u` is the `K`-linear
equivalence `(x,y) ↦ (LA⁻¹*x,y*LB)`. Its inverse is explicitly
`(x',y') ↦ (LA*x',y'*LB⁻¹)`. The inverse laws follow by associativity and
cancellation of the actual matrix units; additivity and scalar linearity
follow from matrix multiplication. Both evaluation laws are definitional.
The dimensions `j,k` are arbitrary naturals, including zero.

Both directions are continuous over any topological field with continuous
ring operations: each output entry is a finite sum of constant multiples
of input entries. `continuous_rectangleChange_canonical` specializes both
continuity conclusions to every algebraic p-adic field with its canonical
topology. No Haar preservation or analytic integral assertion is made.
