# The solvable radical of the Lie algebra of a semisimple group

`Langlands.GroupScheme.Lie.semisimpleLieAlgebraCharZero` proves
`Langlands.GroupScheme.Lie.SemisimpleLieAlgebraCharZeroStatement` in every universe.
For a semisimple group over a field of characteristic zero, the radical of the actual
dual-number tangent Lie algebra is zero. This is the first assertion of Milne,
*Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*, 2022 corrected
reprint, Theorem 22.53, printed p. 482, with the discussion of semisimplicity in §22c,
pp. 476–477. The retained source is `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.

## The solvable radical is central

Write `L` for the tangent Lie algebra. On any finite-dimensional `L`-module, every
vector in `⁅L, rad L⁆` acts by a nilpotent endomorphism. The proof extends the Lie
algebra and the module to an algebraic closure. Mathlib's derived-series formula
shows that the scalar extension of `rad L` is solvable. Its bracket with the extended
Lie algebra therefore lies in the bracket with the new radical, to which
`Langlands.Algebra.isNilpotent_toEnd_of_mem_lie_radical` applies. The scalar-extension
map of endomorphism algebras is injective, so nilpotence descends to the given field.

The differential of a closed matrix embedding is a Lie homomorphism. It sends
`⁅L, rad L⁆` to a subspace of nilpotent tangent endomorphisms normalized by all
tangent endomorphisms. Reductivity supplies a trivial ground-field unipotent radical,
so `MatrixRepresentation.eq_one_of_nilpotent_normalized` makes every tangent in this
ideal the identity in the dual-number kernel. Thus every bracket with the radical
vanishes and the radical is contained in the Lie center.

## The Lie center is zero

The adjoint differential is the tangent bracket in finite coordinates, so the
scheme centralizer of a Lie-central vector has the full tangent space. This
centralizer is closed and locally of finite type. Cartier's theorem makes it
smooth, and the full-tangent subgroup theorem identifies it with the connected
ambient group on all tests. `centerTangentFactor` then lifts the vector to the
scheme-theoretic center.

The center is finite by semisimplicity and reduced by Cartier's theorem. Its
coordinate algebra is a finite-dimensional reduced algebra over the field, hence
a finite product of finite separable field extensions in characteristic zero. It
is formally unramified, so its derivations at the identity augmentation vanish.
The tangent lift is therefore the identity. Since the radical is contained in this
zero Lie center, the actual tangent Lie algebra has `LieAlgebra.HasTrivialRadical`.
