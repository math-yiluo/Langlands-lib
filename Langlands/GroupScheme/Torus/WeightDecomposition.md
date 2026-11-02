# Weight decomposition of the actual adjoint representation

Worker 339. This module proves that the actual Lie algebra of an
affine group scheme locally of finite type over a field is the internal direct
sum of its character weight spaces for any homomorphism from a split torus.
It uses the existing `weightSpace` definition: the eigenvalue equation must
hold after extension to every commutative test algebra, including nonreduced
algebras. The exact published-statement wrapper
`Langlands.GroupScheme.weightDecompositionStatement` is in
`Reductive/WeightDecompositionProof`.

The module imports the published `Torus/Weights` and
`LinearAlgebra/FinsuppDecomposition` interfaces by Worker 274, together with
the previously published universal adjoint coefficients. It uses their
existing structures and operations.

## Sources and scope

Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 12.12, printed pp.234–235
(PDF250–251), proves the character weight decomposition for representations of
diagonalizable algebraic groups. Its proof expands the coaction in a
group-like basis, shows that the coefficients are eigenvectors, and recovers
the original vector as their sum. Here the previously constructed universal
split-torus action and its finite coefficients implement these steps directly
on actual dual-number kernels. No comparison with a tensor-product model of
the Lie algebra is assumed.

The adjoint action is Milne 10.18–10.20, printed pp.191–192
(PDF207–208). Character weight spaces follow Definition 12.16, printed p.236
(PDF252), and their application to the adjoint representation appears in
§21.a, printed pp.424–425 (PDF440–441). The character evaluation identity
uses the lattice point formula, based on Milne 12.9, printed p.233
(PDF249). The arbitrary affine-base isomorphism and weight-space transport
lemmas are derived functorial infrastructure. The decomposition theorem
itself has a field base, with affineness and local finite type; it imposes no
smoothness, connectedness, reductivity, closed-immersion, or maximality
hypothesis.

## Character coordinates and coefficients

For a finite type `I`, `splitTorus.characterLatticeEquiv k I` identifies the
actual character group of the existing finite-product torus with `I → ℤ`.
`characterValue_characterLatticeEquiv_symm` shows that the character
corresponding to `m` evaluates at every test-algebra point `t` as
`∏ j, t j ^ m j`. The proof applies the unit equivalence from affine global
sections to the published global-unit character formula.

`exponentValue_universalPoint` evaluates this product at the actual universal
point over the group algebra `k[I → ℤ]`. The result is the unit monomial of
exponent `m`. Its proof uses the additive homomorphism from exponent vectors
to unit monomials and the identity
`∑ j, m j • Pi.single j 1 = m`.

`characterAdjointCoefficients` reindexes the previously constructed linear
map `universalAdjointCoefficients` by the inverse character-lattice
equivalence. It takes an actual Lie vector to a finitely supported family of
actual Lie vectors indexed by characters. Its application lemma reads the
original exponent-indexed coefficient at the coordinates of the character.
Finite support, linearity, and the original module operations are preserved
by `Finsupp.lmapDomain`.

The following three properties establish the standard-torus decomposition:

- `characterAdjointCoefficients_mem` places each coefficient in its character
  weight space. The exponent-weight equation from
  `UniversalAdjointCoefficients` holds over every test algebra; the character
  evaluation identity translates it into exactly the existing `weightSpace`
  equation.
- `universalAdjointCoefficients_of_mem_weightSpace` applies a vector's
  weight-space equation to the universal point. Its eigenvalue is the
  corresponding unit monomial, so the previously proved monomial
  concentration theorem makes its coefficient family a singleton.
  Reindexing gives `characterAdjointCoefficients_of_mem_weightSpace`: on a
  character weight space the family is `Finsupp.single χ X`.
- `characterAdjointCoefficients_sum` follows from the sum identity for the
  exponent-indexed family, since reindexing preserves its finite sum.

`splitTorus.isInternal_weightSpace` applies the general linear-algebra
criterion `Langlands.LinearAlgebra.isInternal_of_finsupp` to these
properties. Thus the canonical direct-sum map is bijective: membership and
reconstruction give surjectivity, and singleton concentration gives
injectivity.

## Transport to an arbitrary split torus

For commutative group schemes `T` and `T'` over any affine base and an
isomorphism `e : T.toGrp ≅ T'.toGrp`, `characterLattice.comapIso e` is the
additive equivalence obtained by pulling characters back along `e.hom`.
Pullback along `e.inv` is its inverse; additivity uses the published
preadditive category structure.

`weightSpace_comapIso e i χ` identifies the weight space for the pulled-back
character of `T` with the weight space for `χ` under `e.inv ≫ i`. For each
test algebra, one implication evaluates the original condition at
`t ≫ e.inv`; the other evaluates at `t ≫ e.hom`. Functoriality of character
values and the two inverse equations for `e` identify the adjoint arguments
and scalars. The equality is between submodules of the same actual Lie
algebra, so it requires no change of Lie carriers.

Finally, `isInternal_weightSpace_of_isSplitTorus` takes an isomorphism
`e : T.toGrp ≅ splitTorus _ I` from the existing `IsSplitTorus` hypothesis.
It reindexes the standard-torus coefficient map by
`characterLattice.comapIso e`. Injectivity of this character equivalence
identifies each coefficient, and `weightSpace_comapIso` transfers
membership. The inverse character equivalence transfers singleton
concentration, and invariance of finite sums transfers reconstruction.
Applying `isInternal_of_finsupp` proves
`DirectSum.IsInternal (weightSpace i)` for the original homomorphism
`i : T.toGrp ⟶ G`.
