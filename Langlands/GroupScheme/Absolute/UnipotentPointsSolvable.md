# Rational points of unipotent affine group schemes form a solvable group

This module proves a form of Kolchin's theorem for groups of points.
`isSolvable_points_of_isUnipotent` says the following. Let `k` be a field and
`G` a group scheme over `Spec k` with `IsAffineHom G.X.hom`,
`LocallyOfFiniteType G.X.hom` and `IsUnipotent G`. Then for every test scheme
`T` over `Spec k` the group of points `T ⟶ G.X` is solvable
(`Group.IsSolvable`).

## Literature

Milne, *Algebraic Groups* (2017), Proposition 14.3 and Theorem 14.5
(printed pp. 280–281) say that a unipotent algebraic group has a basis for
every finite-dimensional representation in which it acts through the
unitriangular group `U_n`, and so embeds in `U_n`. Proposition 14.21 (printed
p. 284) concludes that a unipotent algebraic group is nilpotent, and so
solvable. The Lean result is weaker in one respect and different in route:
- It proves only that every abstract group of points is solvable, not that the
  group scheme is nilpotent or solvable as an algebraic group.
- It does not construct a full unitriangular basis. It uses the fixed vectors
  one at a time, by induction on the size of a matrix representation, as in the
  proof of Milne's Corollary 14.2.

The hypothesis `IsUnipotent G` is the Library definition in
`Langlands.GroupScheme.Reductive.Basic`: every matrix representation of `G` on
a nonempty finite index type has a nonzero fixed vector in `k^n`. This is
Milne's definition 6.45/§14b. No algebraically closed field is needed.

## Lower-right blocks (section `Tail`)

For a commutative ring `S`, `tail M` is the lower-right `m × m` block
`M.submatrix Fin.succ Fin.succ` of an `(m+1) × (m+1)` matrix.
`firstBasisVector S m` is `Pi.single 0 1`, and `fixesFirstSubgroup S m` is the
subgroup of `GL (Fin (m+1)) S` of matrices `g` with `g *ᵥ e₀ = e₀`. Such a
matrix has first column `e₀`. So `tail_mul` gives
`tail (g * h) = tail g * tail h`, and `tailHom S m` is the resulting group
homomorphism `fixesFirstSubgroup S m →* GL (Fin m) S`.

`tailHom_ker_comm` shows that the kernel of `tailHom` is commutative. Its
elements have the block form `[[1, a], [0, 1]]`, and the claim is checked
entrywise by cases on `Fin.cases` for row and column indices.

`exists_mulVec_eq_firstBasisVector` says that over a field `K` every nonzero
`v : Fin (m+1) → K` is sent to `e₀` by some invertible matrix. It extends the
linear isomorphism `span {v} ≃ span {e₀}` to an automorphism of `K^(m+1)`
(`Submodule.exists_linearEquiv_restrict_eq`) and takes its matrix.

## The block representation (section `TailRepresentation`)

Let `ρ : MatrixRepresentation G (Fin (m+1))` fix `firstBasisVector R m` in the
sense of `IsFixedVector`. Then every point matrix lies in
`fixesFirstSubgroup` (`pointMatrix_mem_fixesFirstSubgroup`), which gives
`fixingPointMatrix ρ hρ T`. Composing with `tailHom` gives
`tailPointMatrix ρ hρ T : (T ⟶ G.X) →* GL (Fin m) Γ(T.left, ⊤)`. Point matrices
are natural in `T` (`pointMatrix_naturality`), and taking blocks commutes with
`Matrix.map`. So these maps are natural (`tailPoints_naturality`), and
`tailRepresentation ρ hρ` is the matrix representation `G ⟶ GL_m` constructed
from them by the Library's `homOfPoints`. The lemma
`tailRepresentation_pointMatrix` identifies its point matrices with the blocks.

## Change of basis (section `BasePoint`)

For `g : GL n R`, `basePoint g` is the `R`-point of `GL_n` with matrix `g`, and
`pointsEquiv_constantPoint_basePoint` shows that its constant point over `T`
has matrix `g` mapped along `scalarMap T`. The Library's
`MatrixRepresentation.conjugate` gives `ρ.conjugate (basePoint g)`, with point
matrices `g ρ(x) g⁻¹`. `isFixedVector_conjugate` shows that if `ρ` fixes `v`,
then the conjugate fixes `g *ᵥ v`. `conjugate_pointMatrix_eq_one_iff` says the
conjugation does not change which points act trivially.

## The induction (section `Kolchin`)

`exists_derivedSeries_le_ker` proves, by induction on `m`, that for every
`ρ : MatrixRepresentation G (Fin m)` and every `T` some term of the derived
series of `T ⟶ G.X` lies in the kernel of `ρ.pointMatrix T`.
- For `m = 0` all matrices are `1`.
- For `m + 1`, unipotence gives a nonzero fixed vector `v ∈ k^(m+1)`. Choose
  `g` with `g v = e₀`, so `ρ' := ρ.conjugate (basePoint g)` fixes `e₀`. The
  induction hypothesis for `tailRepresentation ρ'` gives `N` with the `N`-th
  derived subgroup acting trivially on the block. Those points therefore map
  under `fixingPointMatrix` into the commutative kernel of `tailHom`, so their
  commutators act trivially in `ρ'`, and hence in `ρ`. This gives `N + 1`.

`isSolvable_points_of_mono` applies this to a representation with `Mono
ρ.hom.hom`. There `ρ.pointMatrix T` is injective (`pointMatrix_injective`,
`Langlands.GroupScheme.MatrixRepresentationRationalPoints`), so a term of the
derived series is trivial.

## Main theorem

`isSolvable_points_of_isUnipotent` takes the closed immersion
`ρ : G ⟶ GL_N` from the published `affineLinearEmbeddingStatement` (affine
group schemes of finite type over a field have a faithful linear
representation; Milne 2017, 4.9). A closed immersion is a monomorphism, and
`Over.mono_of_mono_left` gives `Mono ρ.hom.hom`. The result then follows from
`isSolvable_points_of_mono`.
