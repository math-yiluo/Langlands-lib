# Stable lines and stable subspaces of matrix representations

This helper module for the proof of
`Langlands.GroupScheme.TrigonalizableCharacterizationStatement` (Milne 2017,
Proposition 16.2; see
[`CharacterizationStatement`](CharacterizationStatement.md)) relates two
existing Library notions for a matrix representation
`ρ : MatrixRepresentation G n` of a group scheme `G` over `Spec k`, `k` a
field:

- `ρ.IsStableLine v` (from [`Trigonalizable`](../Trigonalizable.md)): for
  every scheme `T` over `Spec k` and every point `g : T ⟶ G.X`, the matrix
  `ρ(g)` sends the image of `v` in `Γ(T, ⊤)ⁿ` to a multiple `c • v` with
  `c : Γ(T, ⊤)`;
- `ρ.IsStableSubspace V` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md)):
  for every commutative `k`-algebra `A`, every point `x` of `G` with values in
  `A`, every `w ∈ V` and every `k`-linear map `ℓ : A → k`, applying `ℓ` to the
  coordinates of `ρ(x)w` gives a vector of `V`.

All declarations are in the namespace
`Langlands.GroupScheme.MatrixRepresentation`. Nothing new is defined; the
module consists of theorems.

## Declarations

- `IsStableLine.affine`: a stable line gives, at every affine point
  `x : Spec A ⟶ G.X` (written with `algSpec`), a multiplier `c : A` with
  `ρ.affineMatrix A x *ᵥ v = c • v` (with `v` mapped to `Aⁿ` by
  `algebraMap k A`).
  *Proof.* Apply the stable-line hypothesis to the affine test, rewrite the
  point matrix as the affine matrix (`pointMatrix_eq_affineMatrix`), and
  transport along the algebra isomorphism
  `Corepresented.affineSectionsAlgEquiv A` between global sections of
  `Spec A` and `A`; the scalar maps agree by
  `UnipotentMatrixCriterion.scalarMap_affine`.

- `IsStableLine.isStableSubspace`: if `v` spans a stable line then `k ∙ v` is
  a stable subspace.
  *Proof.* For `w = a • v` and an affine point `x`, `IsStableLine.affine`
  gives `ρ(x)(a • v) = (a c) • v` over `A`. Applying a `k`-linear
  `ℓ : A → k` coordinatewise gives `(a · ℓ c) • v ∈ k ∙ v`, using
  `ℓ (t b) = t ℓ(b)` for `t ∈ k`.

- `isStableLine_of_isStableSubspace` (assuming `[IsAffineHom G.X.hom]`): if
  `k ∙ v` is a stable subspace then `v` spans a stable line.
  *Proof.* The case `v = 0` is immediate with multiplier `0`. Otherwise pick
  `i₀` with `v i₀ ≠ 0`, and form the one-column matrix `B` with column `v`
  and the one-row matrix `C` equal to `(v i₀)⁻¹` at `i₀` and `0` elsewhere.
  Then the columns of `B` lie in `k ∙ v` and `B C` is the identity on
  `k ∙ v`. The Library lemma `IsStableSubspace.isStableCoordinates` (which
  uses affineness of `G`) turns the stable subspace into the identity
  `ρ(g) B = B (C ρ(g) B)` on every scheme test `g : T ⟶ G.X`. The `1 × 1`
  matrix `C ρ(g) B` is the multiplier `c`, and `ρ(g) v = ρ(g) B 1 = B c = c v`.

- `isStableLine_iff_isStableSubspace`: the two previous results combined, for
  affine `G`.

- `IsStableLine.restrict`: a stable line for `ρ` is a stable line for
  `ρ.restrict f` along any homomorphism `f : H ⟶ G`, by
  `pointMatrix_restrict` (the point `g` of `H` is sent to the point
  `g ≫ f` of `G`).

- `IsStableLine.of_intertwines`: given representations `ρ` on `kⁿ` and `σ` on
  `kᵐ` and a matrix `B : Matrix n m k` with `ρ(x) B = B σ(x)` on every scheme
  test, a stable line `v` of `σ` gives the stable line `B v` of `ρ` with the
  same multiplier. *Proof.* The image of `B v` in `Γ(T, ⊤)ⁿ` is `B` (mapped
  by the scalar map) applied to the image of `v`; then rewrite with the
  intertwining identity.

- `IsStableSubspace.mulVec_pointMatrix_eq_zero` (assuming
  `[IsAffineHom G.X.hom]`): if `V` is a stable subspace, `φ : Matrix m n k`
  kills every vector of `V`, and `v ∈ V`, then `φ ρ(x) v = 0` on every scheme
  test `x : T ⟶ G.X` (with `φ` and `v` mapped by the scalar map).
  *Proof.* `exists_subspace_split_coordinates V` gives matrices `B`, `C` with
  the columns of `B` lying in `V` and `B C` the identity on `V`. The
  stable-coordinates identity gives `ρ(x) B = B (C ρ(x) B)`. Write `v` as
  `B (C v)`; since `φ B = 0`, the product vanishes.

## Provenance

Internal. These are elementary comparisons between the scheme-test
definition of a stable line in the Library's `IsTrigonalizable` and the
affine, linear-functional definition of a stable subspace. Milne (2017,
p.324) uses both points of view interchangeably ("G stabilizes a maximal
flag in V"); no separate literature locator is needed.
