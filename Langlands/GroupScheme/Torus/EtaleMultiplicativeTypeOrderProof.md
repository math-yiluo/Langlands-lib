# Étale groups of multiplicative type

`Langlands.GroupScheme.etaleMultiplicativeTypeOrderStatement` proves the exact,
unchanged published proposition
`Langlands.GroupScheme.EtaleMultiplicativeTypeOrderStatement.{u}` in every
universe. For every field `k` with characteristic exponent `p`, separable
closure `Ks`, and affine étale group scheme `G`, it proves that `G` is of
multiplicative type if and only if it is commutative and
`Nat.card (G.affinePoints (CommAlgCat.of k Ks))` is coprime to `p`.

The source is the corrected last sentence of Milne, *Algebraic Groups* (2017),
Example 12.28, as documented in the target statement's Markdown. In particular,
the exact target includes commutativity. The implementation uses character
separation and a closed embedding into a split torus for the converse, rather
than a Fourier isomorphism of coordinate algebras.

The forward implication is `EtaleMultiplicativeTypeOrder.forward`.
Published multiplicative-type geometry supplies commutativity and a
diagonalization over `Ks`. In a field the characteristic Frobenius is injective,
so the geometric points of a diagonalizable group have no nonidentity point
killed by `p`. The point group is finite since its affine coordinate algebra
is étale over a field. Cauchy's theorem gives the required coprimality in
positive characteristic; in characteristic zero the exponent is one.

For the converse, `extensionPointsEquiv` identifies the rational points of the
base change to `Ks` with the original `Ks`-coefficient points. This comparison
follows the base-change point-equivalence construction from Worker 238's
draft. The base-changed group remains affine, étale and commutative. Its
coordinate algebra is finite-dimensional, so it is a finite scheme.

`EtaleMultiplicativeTypeOrder.exists_diagonalizableIso_of_coprime_order`
then constructs a finite separating family of abstract unit-valued characters,
lifts them to actual multiplicative-group morphisms by interpolation of
global functions, and takes their product. The resulting morphism into a
split torus is injective on rational points. Over the separably closed field,
the source's functions are determined by those points, so interpolation on the
target gives a closed immersion. The published closed-subgroup presentation
theorem for split tori produces a diagonalizable group with finitely generated
character group isomorphic to the base-changed group. This is precisely a
witness to `IsMultiplicativeType G`.

The paired helper modules explain their interpolation, characteristic,
Frobenius, and character-embedding arguments in detail. Every additional
assumption of their intermediate lemmas is discharged in this proof.
