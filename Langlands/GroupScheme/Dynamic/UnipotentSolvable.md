# Solvability of the points of dynamic unipotent subgroups over a field

Worker 303. This module proves that for an affine group scheme `G` locally of
finite type over a field `K`, and a cocharacter `χ` of `G`, the group of points
of the published dynamic unipotent subgroup functor `Dynamic.unipotent χ` over
every test scheme `U` is solvable. It also proves that the points of
`Dynamic.parabolic χ` over `U` form a solvable group whenever those of
`Dynamic.centralizer χ` do.

These are statements about abstract groups of points, on every test scheme
over `Spec K`, nonaffine and nonreduced ones included. They are not
statements of scheme-theoretic unipotence: no notion of unipotent group scheme
is defined or used. They are what the published `IsSolvableGroupScheme` needs
(solvability of the group of `k̄`-points of the base change). This is helper
material for clause 1 of `RegularCocharacterBorelStatement` (proof task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`).

## Source and route

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, has
two relevant passages:

- Example 14.13 (printed p.283, PDF p.299): `U(λ)` is unipotent because, as in
  the proof of Theorem 13.33, it can be realized as a subgroup of the upper
  unitriangular group `U_n`.
- The proof of Theorem 13.33 (printed p.266, PDF p.282) diagonalizes `λ` in a
  suitable basis of `V` for `G = GL_V`. In general it embeds `G` into `GL_V`,
  and `U_G(λ) = U_{GL_V}(λ) ∩ G`.

The Lean proof follows this route at the level of point groups:

- diagonalization of cocharacters of `GL_n`, from `GeneralLinearCocharacterWeights`;
- the published computation of the dynamic subgroups of `GL_n` for diagonal
  cocharacters, `GeneralLinear.dynamicStatement`;
- Worker 308's published solvability of upper triangular matrix groups,
  `Langlands.GeneralLinear.UpperTriangularSolvable.isSolvable`;
- the published closed linear embedding `affineLinearEmbeddingStatement`;
- the published limit homomorphism `Dynamic.limitHom`.

## Block unipotent matrices

`GeneralLinear.antitoneEnumeration e : Fin (card n) ≃ n` enumerates the index
type so that the weights `e` decrease (`antitone_antitoneEnumeration`). It is
built from Mathlib's `Tuple.sort` applied to `-e`.

`blockUnipotentToUpper A e` reindexes a matrix of the published
`blockUnipotentSubgroup A e` along this enumeration. The result lies in the
published `upperTriangularSubgroup`. Take entries below the diagonal, at
positions `(i, j)` with `j < i`. Their weights satisfy
`e (π i) ≤ e (π j)`, so the block-unipotent condition makes them entries of
the identity matrix, hence zero. The map is an injective group homomorphism
(`blockUnipotentToUpper_injective`), since reindexing is an algebra
isomorphism.

`isSolvable_blockUnipotentSubgroup` follows by
`Group.isSolvable_of_isSolvable_injective`, over every commutative ring `A`.

## `GL_n`

`GeneralLinear.isSolvable_unipotent_carrier` takes a field `K`, a cocharacter
`ψ` of `GL_n` over `Spec K` and a test scheme `U`. It states that
`(Dynamic.unipotent ψ).carrier U` is a solvable group.

- Choose `g` and `e` with `ψ ≫ int(g) = diagonalCocharacter e`
  (`exists_matrix_innerIso_comp_eq_diagonalCocharacter`).
- Let `c` be the constant point of `baseOfMatrix K g` over `U`. The published
  `Dynamic.mem_unipotent_conj` gives `x ∈ U(ψ)(U) ↔ c x c⁻¹ ∈ U(ψ ≫ int g)(U)`.
- The published `dynamicStatement` identifies `U(ψ ≫ int g)` with
  `blockUnipotent n K e`. Its points have matrices in
  `blockUnipotentSubgroup Γ(U, ⊤) e`.
- The resulting map `x ↦ matrix of c x c⁻¹` is an injective group
  homomorphism into a solvable group.

## Affine groups over a field

`Dynamic.isSolvable_unipotent_carrier` assumes that `G` is affine and locally
of finite type over a field `K`, with `χ` a cocharacter and `U` a test scheme.
It states that `(Dynamic.unipotent χ).carrier U` is a solvable group.

- The published `affineLinearEmbeddingStatement` gives a closed subgroup
  `ρ : G ⟶ GL_N`.
- The published `Dynamic.unipotent_le_comap` sends `U(χ)(U)` into
  `U(χ ≫ ρ)(U)` by `x ↦ x ≫ ρ`. This is a group homomorphism. It is
  injective because the closed immersion `ρ` is a monomorphism of schemes.
- The `GL_N` case then applies.

## Parabolic subgroups

`Dynamic.isSolvable_parabolic_carrier` works over any base scheme. Its
hypotheses are that `G` is separated and that the point groups of
`Dynamic.unipotent χ` and of `Dynamic.centralizer χ` over `U` are solvable.
Its conclusion is that the point group of `Dynamic.parabolic χ` over `U` is
solvable.

The proof uses the published limit homomorphism
`Dynamic.limitHom χ U : P(χ)(U) →* Z(χ)(U)`, whose kernel is
`U(χ)(U)` (`Dynamic.ker_limitHom`). It then applies
`Group.isSolvable_of_ker_le_range`, with the inclusion `U(χ)(U) ≤ P(χ)(U)`.

For the Borel application, the remaining input is solvability of the points of
`Z(ν ≫ j)`. For a regular cocharacter of a split maximal torus, it would
follow from two published statements, once both are proved:

- `GenericCentralizerStatement`, which is not yet proved;
- the statement candidate `MaximalTorusCentralizerStatement`.

Together they say `Z(ν ≫ j) = T`, which is commutative. This module does not
assume either statement.
