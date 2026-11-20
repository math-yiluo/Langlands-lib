# Real approximation for rational tori

`TorusRealApproximationStatement` asserts density of the rational points of
every affine rational torus in its actual real points, for the affine
evaluation topology. `torusRealApproximation` proves this assertion.

A finite Galois set is realized by the embeddings of a product of intermediate
fields of the splitting field. Its lattice of integer-valued functions is the
character lattice of the corresponding Weil restriction, with the given
permutation action. The coordinate basis makes this an induced torus.

The proof embeds a finite Galois splitting field in `ℂ` and restricts complex
conjugation to it. For a specified real point of the target torus, its complex
character is a norm times the sign of a fixed integral form. A permutation
lattice embedding has a retraction on abelian groups, so the character in the
norm extends by composition with the retraction. It also has a fixed coordinate
inducing the specified integral form, which extends the sign. Their product is
equivariant under complex conjugation and descends to an actual real point of
the induced torus. The equivariant lattice embedding gives a homomorphism
from the induced torus to the target. Character evaluation and injectivity of
extension to `ℂ` show that the descended point maps to the specified real point.
Continuity and the density result for induced tori place that point in the
closure of the rational points of the target.

This proves the torus case of Milne, *Algebraic Groups* (2017), Theorem 25.70,
p. 564. The induced torus and its map in this proof can depend on the specified
real point.
