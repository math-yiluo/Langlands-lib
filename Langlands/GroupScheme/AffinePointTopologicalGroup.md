# Topological groups of actual affine points

Let `R` be a commutative ring and `A` an `R`-algebra, in the same universe as `R`.
This module uses the evaluation topology from `AffinePointTopology` on the actual carrier
`Hom_{Spec R}(Spec A, G)`, with its inherited group-scheme point multiplication.

For any group-scheme isomorphism `e : G ≅ H`, `affinePointsIsoHomeomorph e A` is a
homeomorphism between these point spaces. Its forward map is postcomposition with `e.hom`,
and its inverse is postcomposition with `e.inv`. The lemma
`affinePointsIsoHomeomorph_map_mul` proves multiplicativity. This construction only needs a
topology on `A`; neither group scheme needs to be affine.

The instance `affinePointsIsTopologicalGroup` establishes that, when the underlying scheme
of `G` is affine and `A` is a topological ring, the actual point group is a topological group.
No topology on the base ring or continuity hypothesis on its algebra map is needed.

The implemented proof uses Mathlib's equivalence between affine group schemes and spectra of
commutative Hopf algebras. On a Hopf spectrum the actual point multiplication corresponds to
convolution of algebra homomorphisms. Each comultiplication value is a tensor, and tensor induction
shows that its evaluation is continuous using only finite sums and products of coordinate values.
The isomorphism of actual group schemes transports this result to an arbitrary affine group scheme.
Continuous inversion was established in `AffinePointTopology`.

This is derived content accompanying the point-space homeomorphism construction. Its
source motivation is Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Theorem 2.2.1 and its coordinate-evaluation injection (2.8), printed pp.51–54, and
Proposition 2.2.2, printed p.54. The source asserts the topological-group property at
finite type. The implemented Hopf-algebra proof proves it without a finite-type hypothesis
for the topology induced by all regular functions.
Finite-coordinate presentations, local compactness and the restricted-product comparison are
separate obligations.
