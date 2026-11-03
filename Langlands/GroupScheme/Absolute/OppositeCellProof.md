# Proof of the opposite open cell for a smooth affine group over a field

`Langlands.GroupScheme.oppositeCellStatement` proves `OppositeCellStatement.{u}` from
`Absolute.BorelStatement`. Let `k : Type u` be a field and `G` a group scheme over `Spec k` with
smooth and affine structure morphism. Let `χ : 𝔾_m ⟶ G` be a cocharacter, and let `iU : U ⟶ G`
and `iP : P ⟶ G` represent `U(χ⁻¹)` and `P(χ)`. Then the morphism of schemes underlying the
multiplication `(fst ≫ iU) * (snd ≫ iP) : U ×_k P ⟶ G` is an open immersion.

## Proof

1. **Linear embedding.** A smooth morphism is locally of finite type. The published theorem
   `affineLinearEmbeddingStatement` therefore gives `N` and a homomorphism
   `ρ : G ⟶ GL_N` that is a closed subgroup.
2. **Diagonalizing the cocharacter.** The published theorem
   `GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter` (from
   `Dynamic.GeneralLinearCocharacterDiagonal`) applies to the cocharacter `χ ≫ ρ` of `GL_N`.
   It gives a `k`-point `g` of `GL_N` and weights `e : Fin N → ℤ` such that
   `χ ≫ ρ ≫ inn(g) = diagonalCocharacter e`, where `inn(g)` is the inner automorphism
   `innerIso g`.
3. **The new embedding.** Set `ρ' = ρ ≫ inn(g)`. Its underlying morphism of schemes is a closed
   immersion followed by an isomorphism, so it is again a closed immersion. The isomorphism is
   the image of `inn(g)` under the forgetful functors to schemes. By construction,
   `χ ≫ ρ' = diagonalCocharacter e`.
4. **Monomorphism.** By the theorem `Dynamic.mono_oppositeCellMul` (from
   `Dynamic.OppositeCellMono`), the multiplication `U ×_k P ⟶ G` is a monomorphism. Its
   hypothesis is that `G` is affine. That theorem is stated for
   `SubgroupFunctor.cellMultiplication iU iP`, which is by definition
   `(fst ≫ iU) * (snd ≫ iP)`, so it is used here without conversion.
5. **Conclusion.** `Dynamic.isOpenImmersion_mul_of_diagonal` (from
   `Dynamic.OppositeCellEmbedding`) applies to the closed subgroup `ρ'`, the diagonal identity
   from step 3, `hU`, `hP` and the monomorphism from step 4. It shows that the multiplication
   is an open immersion.

Smoothness of `G` enters only through local finite type in step 1. Connectedness is not
assumed, and the trivial cocharacter is included. The proof uses no unproved proposition. In
particular it does not use `DynamicSmoothStatement`, `DynamicConnectedStatement` or
`DynamicLieStatement`.

## Supporting modules

All are internal to this proof.

* `Dynamic.GeneralLinearCell`: the cell minor of `GL_n` and the cell decomposition `g = u p`.
* `Dynamic.GeneralLinearCellBlock`: the block lemma and Levi conjugation.
* `Dynamic.GeneralLinearTranslation`: right translation on bounded-degree polynomials in the
  coordinates, and its weights.
* `Dynamic.GeneralLinearStabilizer`: the ideal-theoretic stabilizer argument.
* `Dynamic.OppositeCellEmbedding`: the scheme-theoretic assembly for a closed subgroup of `GL_n`
  with diagonal cocharacter.

## Provenance

The statement is Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition),
Proposition 2.1.8(3), over a field. The implemented route follows Step 3 of their proof:
embed `G` in a general linear group and show that the factors of a point of `G` in the open
cell of the ambient group lie in `G`. Two differences from the book:

* The cocharacter is first conjugated to a diagonal one, so the open cell of the ambient group
  is explicit.
* The book's stabilizer of a line in a representation is replaced by the stabilizer of a
  subspace of the polynomials of bounded degree, as described in `GeneralLinearStabilizer`.
