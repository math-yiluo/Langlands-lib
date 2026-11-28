# Reflection of relative polarizations across a square-zero base reduction

Suppose a homomorphism from an abelian scheme to its actual dual becomes a
polarization after base change. If every field-valued point of the original
base factors through the base-change map, test the homomorphism on these
factorizations. The direct and successive pullbacks agree under the
canonical abelian and dual comparisons. On each residue-field fibre the
successive pullback is an isogeny, so the direct base change of the original
homomorphism is an isogeny. The fibrewise isogeny theorem supplies finiteness,
flatness and surjectivity on the original base.

For an algebraically closed field point, the polarization on the changed
base supplies an ample Mumford presentation for its fibre. Transport
along the canonical composition isomorphism gives that presentation for
the original homomorphism at the same geometric point. This verifies the
second clause of `IsPolarization` using the original dual-valued map.

A surjective map of commutative rings with square-zero kernel has the
required factorization for every field-valued point. The corresponding
ring map into a field kills the square-zero kernel and descends through
the given surjection. This gives
`DualWitness.isPolarization_of_squareZero_reduction`.

The argument is a consequence of the Library's geometric-fibre definition
of relative polarization, the fibrewise isogeny theorem and the dual
base-change coherence. It supplies the positivity verification after a
polarization morphism lifts in the deformation setting of Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, revised
14 March 2021, Corollary 2.2.4.8, printed p. 157. The retained source is
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
