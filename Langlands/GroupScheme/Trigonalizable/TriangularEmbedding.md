# Trigonalizable groups embed in the upper triangular group (Milne 16.2, (a) ⇒ (c))

Author: Worker 158.

This helper module proves the implication (a) ⇒ (c) of
`Langlands.GroupScheme.TrigonalizableCharacterizationStatement` (see
[`CharacterizationStatement`](CharacterizationStatement.md)): a
trigonalizable affine group scheme of finite type over a field `k` admits a
homomorphism `j : G ⟶ T_N` that is a closed immersion, where `T_N` is
`GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
(fun i => -(i.val : ℤ))`, the closed subgroup of `GL_N` cut out by the
entries strictly below the diagonal. All declarations are in the namespace
`Langlands.GroupScheme.Trigonalizable`. Nothing new is defined.

## Linear algebra over a field `K`

- `exists_last_ne_zero`: a vector `c : Fin N → K` with `c i ≠ 0` has a last
  nonzero coordinate `m ≥ i`, that is, `c m ≠ 0` and `c l = 0` for `l > m`.
  *Proof.* `m` is the maximum of the finite set of indices with nonzero
  coordinate.

- `sum_smul_notMem_of_adapted`: let `W : Fin (N + 1) → Submodule K (Fin N → K)`
  be monotone and let vectors `p j` satisfy `p j ∈ W (j+1)` and
  `p j ∉ W j` ("adapted" to the flag). If the last nonzero coefficient of
  `c` is at `m`, then `∑ l, c l • p l ∉ W m`.
  *Proof.* All terms with `l < m` lie in `W (l+1) ⊆ W m`, and the terms with
  `l > m` vanish. If the sum were in `W m`, then so would be `c m • p m`, and
  hence `p m` because `c m ≠ 0`, which is false.

- `exists_adapted_matrix`: for a maximal flag `W` of `Kᴺ` (monotone,
  `finrank (W i) = i`), there is `P : GL (Fin N) K` whose `j`-th column lies
  in `W (j+1)`, and such that for every `w ∈ W (j+1)` the coordinates of
  `P⁻¹ w` with index `i > j` vanish.
  *Proof.* The dimensions force `W j < W (j+1)`, so choose
  `p j ∈ W (j+1) \ W j`. Let `A` be the matrix with columns `p j`; then
  `A c = ∑ l, c l • p l`. `A` is injective: if `A c = A c'` with `c ≠ c'`,
  take the last nonzero coordinate `m` of `c - c'`; then
  `0 = ∑ (c - c') l • p l ∉ W m` by the previous lemma, a contradiction
  since `0 ∈ W m`. So `A` is invertible (`Matrix.mulVec_injective_iff_isUnit`);
  let `P` be the corresponding unit. For the second property, if
  `(P⁻¹ w) i ≠ 0` for some `i > j`, let `m ≥ i` be the last nonzero
  coordinate of `P⁻¹ w`. Then `w = A (P⁻¹ w) ∉ W m`, but
  `w ∈ W (j+1) ⊆ W m` since `j < m`, a contradiction.

## Triangularity and the closed embedding

- `conjugate_pointMatrix_eq_zero_of_adapted` (assuming `[IsAffineHom G.X.hom]`):
  let `ρ : MatrixRepresentation G (Fin N)` stabilize every term of `W` and let
  `P` be as in `exists_adapted_matrix`. Then the conjugate representation
  `ρ.conjugate (basePoint P⁻¹)` (Library: `MatrixRepresentation.conjugate`
  composes with inner conjugation of `GL_N` by a `k`-point, and
  `basePoint` is the `k`-point of `GL_N` given by an invertible matrix) has
  point matrix entry `(i, j)` equal to `0` for `j < i`, on every scheme test
  `x : T ⟶ G.X`.
  *Proof.* By `conjugate_pointMatrix` and
  `pointsEquiv_constantPoint_basePoint`, the conjugate point matrix is
  `P⁻¹ ρ(x) P` (with entries mapped to `Γ(T, ⊤)`). Its `(i, j)` entry is the
  row `φ` (the `i`-th row of `P⁻¹`) applied to `ρ(x)` applied to the `j`-th
  column of `P`. That column lies in `W (j+1)`, and `φ` kills `W (j+1)` since
  `i > j`. The lemma `IsStableSubspace.mulVec_pointMatrix_eq_zero` (module
  [`StableLines`](StableLines.md)) gives the vanishing.

- `exists_closed_blockParabolic_factor`: a matrix representation
  `ρ : MatrixRepresentation H (Fin N)` with `IsClosedSubgroup ρ`, whose point
  matrix at the universal point `𝟙 H.X` has zero entries below the diagonal,
  factors through a homomorphism `j : H ⟶ T_N` with `IsClosedSubgroup j`.
  *Proof.* The hypothesis says, via `GeneralLinear.mem_blockParabolic`, that
  the universal point `ρ` lies in the block parabolic subgroup functor, hence
  every point of the range of `ρ` does. Since `ρ` is a monomorphism (a closed
  immersion), the range functor is represented by `ρ`, and the block parabolic
  functor is represented by `blockParabolicHom`
  (`GeneralLinear.isRepresentedBy_blockParabolic`). The inclusion of functors
  lifts to `j` with `j ≫ blockParabolicHom = ρ`
  (`SubgroupFunctor.IsRepresentedBy.lift`, `lift_comp_eq`). Since
  `blockParabolicHom` is a closed immersion
  (`GeneralLinear.isClosedSubgroup_blockParabolicHom`) and the composite is a
  closed immersion, so is `j` (`IsClosedImmersion.of_comp_isClosedImmersion`).
  This follows the same steps as the Library's
  `exists_closed_blockParabolic_factor_of_rational` (in
  `Absolute.SolvableTriangularEmbeddingReduction`).

- `exists_closed_triangular_of_isTrigonalizable` (Milne 16.2, (a) ⇒ (c);
  assuming `[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]`):
  `IsTrigonalizable G` implies that there exist `N` and `j : G ⟶ T_N` with
  `IsClosedSubgroup j`.
  *Proof.* The published `affineLinearEmbeddingStatement` gives a closed
  embedding `ρ : G ⟶ GL_N`. Module [`Flag`](Flag.md)
  (`exists_stableFlag_of_card_eq`) gives a stable maximal flag `W` of `kᴺ`,
  and `exists_adapted_matrix` gives `P`. The conjugate
  `ρ.conjugate (basePoint P⁻¹)` is still a closed immersion, being `ρ`
  followed by an isomorphism (inner conjugation). It is upper triangular at
  every point by `conjugate_pointMatrix_eq_zero_of_adapted`, in particular at
  the universal point, so `exists_closed_blockParabolic_factor` gives `j`.

## Provenance

The implication is Milne, *Algebraic Groups* (2017), Proposition 16.2,
(b) ⇒ (c) combined with (a) ⇒ (b), pp.324–325 (source ID
`milne-2017-algebraic-groups`). Milne applies (b) to a faithful
finite-dimensional representation (his 4.9) and chooses a basis adapted to
the stable maximal flag. The Lean proof does the same: the faithful
representation is a closed embedding from the published
`affineLinearEmbeddingStatement`, and the adapted basis is the matrix `P` of
`exists_adapted_matrix`. The linear-algebra lemmas are elementary and
internal.
