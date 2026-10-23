# Primary decomposition for commuting endomorphisms

These internal deductions by Worker 307 support the primary-decomposition
step in Bernstein–Zelevinsky (1976), §4.12(1), printed p.40, registered
source `bernstein-zelevinsky-1976-representations-gln`.

Subtracting a scalar from each generator preserves its unital generated
algebra and pairwise commutation. For a finite family of invariant subspaces
spanning the vector space, restriction embeds the algebra into the product
of its restriction images. Thus the dimension is bounded by the sum of the
image dimensions. If the subspaces are also independent, their dimensions
sum to the ambient dimension.

For real exponent at least one, a finite sum of powers of nonnegative
numbers is bounded by the corresponding power of their sum. The proof
uses the two-term real power inequality by finite-set induction. Combining
this with the restriction injection transports a common real-power
dimension bound from the summands to the full algebra.

`commuting_dimension` proves the general bound over any algebraically closed
field `K`. For `l = 0`, the scalar-algebra bound gives dimension at most one.
For positive `l`, Mathlib's simultaneous generalized eigenspaces of the
commuting family form an independent family spanning `V`. Finite dimension
makes the subtype of nonzero summands finite. Every element of the generated
commutative algebra preserves each summand because it commutes with each
generator.

On a summand indexed by a tuple of eigenvalues, restrict the generators
and subtract their respective eigenvalues times the identity. The resulting
operators commute, and Mathlib's nilpotence theorem for restriction to a
generalized eigenspace makes each nilpotent. The scalar-shift lemma identifies
the generated algebra with the image of the original restriction map.
`nilpotent_dimension` bounds its dimension. Independence adds the dimensions
of the summands, and the preceding real-power inequality gives the full bound
`dim C ≤ (dim V)^(2 - 2/2^l)`.

`commuting_dimension_nat` raises both sides to `2^l`, using nonnegativity.
The exponent identity
`(2 - 2/2^l) * 2^l = 2^(l+1) - 2`
then yields the natural-power inequality
`(dim C)^(2^l) ≤ (dim V)^(2^(l+1)-2)`.
The argument includes the zero vector space and zero generators. The
independent universes of the field and vector space are retained.

This is a formal deduction of the source's primary-decomposition argument,
combined with the preceding nilpotent proof. The source's retained PDF has
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed p.40 is zero-based PDF page 39.
