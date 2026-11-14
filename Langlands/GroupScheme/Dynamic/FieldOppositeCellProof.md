# Proof of the opposite dynamic open cell over a field without smoothness

Worker 3483 wrote the proof in the parent program's shared draft; Worker 524
prepared this proof pair for Task 6034.

`Langlands.GroupScheme.dynamicFieldOppositeCell` proves the unchanged
published proposition
`Langlands.GroupScheme.DynamicFieldOppositeCellStatement.{u}` for every
universe `u`. It imports the statement and its published dependencies.

For every field `k : Type u`, let `G` be an affine group scheme over
`Spec k` whose structure morphism is locally of finite type, and let
`χ : 𝔾_m ⟶ G` be a cocharacter. Suppose the homomorphisms `iU : U ⟶ G`
and `iP : P ⟶ G` represent, respectively, the actual dynamic subgroup
functors `U_G(-χ)` and `P_G(χ)` on every test scheme over `k`, including
nonreduced tests. Then ordered multiplication
`SubgroupFunctor.cellMultiplication iU iP`, sending `(u,p)` to
`iU(u)iP(p)`, is an open immersion on underlying schemes.
Here `-χ` is precomposition with `Gm.powerHom (-1)`.

## Implemented proof

The proof follows the published theorem
`Langlands.GroupScheme.oppositeCellStatement` in
[`Absolute.OppositeCellProof`](../Absolute/OppositeCellProof.md).
That theorem obtains local finite type from smoothness. The present target
supplies local finite type directly, so the same proof applies:

1. `affineLinearEmbeddingStatement` gives a finite integer `N` and a closed
   embedding `ρ : G ⟶ GL_N` from affineness and local finite type.
2. `GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter` supplies a
   `k`-point `g` and integer weights `e : Fin N → ℤ` such that
   `(χ ≫ ρ) ≫ innerIso(g).hom` is the diagonal cocharacter of `e`.
3. Set `ι = innerIso(g)`. Its underlying scheme morphism is an isomorphism,
   obtained by applying the forgetful functors to this group-scheme
   isomorphism. Thus `ρ ≫ ι.hom` is again a closed immersion. Associativity
   gives the required identity for `χ ≫ (ρ ≫ ι.hom)`.
4. `Dynamic.mono_oppositeCellMul χ hU hP` proves that the ordered
   multiplication is a monomorphism from the all-test representation
   hypotheses and the affineness of `G`.
5. `Dynamic.isOpenImmersion_mul_of_diagonal` applies to the closed
   embedding, its diagonal identity, the two representation hypotheses and
   that monomorphism. Its multiplication expression is definitionally
   `SubgroupFunctor.cellMultiplication iU iP`, so it proves the exact target.

The final helper uses the explicit open cell of `GL_N` and the
ideal-theoretic stabilizer argument: the two matrix factors of a point of
`G` in that cell lie in `G`, and representability lifts them to `U` and `P`.
The multiplication is then an isomorphism onto a basic open subscheme.
No smoothness or connectedness hypothesis, and no unproved proposition
parameter, enters this proof. The theorem retains the full field and
universe scope of the target and includes the trivial cocharacter.

## Provenance

The assertion is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Proposition 2.1.8(3), printed p.53/PDF p.79, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. Its field proof is Step 3,
printed pp.55–56/PDF pp.81–82. The source PDF is
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The implementation reuses the published closed-linear-embedding and
diagonal-cell route. Its ideal-theoretic stabilizer of a subspace of
bounded-degree polynomials replaces the source's stabilizer of a line.
The imported statement Markdown explains the finite-presentation and
all-test representative comparisons. This theorem proves the
open-immersion assertion only; it does not assert the additional
ambient-intersection identity in the source.
