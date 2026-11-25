# Stable lines: universal points, epimorphic restriction and coefficient matrices

This internal module connects stable lines of actual group-scheme representations, as defined
by `MatrixRepresentation.IsStableLine` and `IsTrigonalizable` in
[`Trigonalizable`](../Trigonalizable.md), with two other descriptions. The first is pullback
of global functions along scheme epimorphisms. The second is the coalgebra condition
`CoalgebraTrigonalizable.IsMatrixTrigonalizable` from
[`CoalgebraCriterion`](CoalgebraCriterion.md). The module is used by
[`SubgroupQuotientProof`](SubgroupQuotientProof.md). Every proof copies the matching published
proof for fixed vectors and unipotence and adds a multiplier `c`. Those proofs are
`isFixedVector_iff_universal` and `isFixedVector_restrict_iff` in
[`Reductive/UnipotentQuotient`](../Reductive/UnipotentQuotient.md), `IsUnipotent.of_iso` in
[`Rational/SplitUnipotentTransport`](../Rational/SplitUnipotentTransport.md),
`isFixedVector_iff` in
[`UnipotentMatrixCriterion/Coordinates`](../UnipotentMatrixCriterion/Coordinates.md), and
`corepresentedMatrixUnipotence` in
[`UnipotentMatrixCriterion/Criterion`](../UnipotentMatrixCriterion/Criterion.md).

## Algebra

`exists_mulVec_eq_smul_of_injective` works over commutative rings `A` and `A'` with an
injective ring map `φ : A →+* A'`. Let `M` be a square matrix over `A` and `s` a vector over
`A` with a unit coordinate `s i₀`. If `M.map φ *ᵥ (φ ∘ s) = c • (φ ∘ s)` for some `c : A'`,
then `M *ᵥ s = d • s` with `d = (M *ᵥ s) i₀ * (s i₀)⁻¹`. After applying `φ`, both sides become
`c * φ (s i)`.

## Representations over a base ring

Here `R : CommRingCat.{u}`, `G` and `H` are group schemes over `Spec R`, and `n` is a finite
index type with decidable equality.

- `MatrixRepresentation.isStableLine_iff_universal`: `ρ.IsStableLine v` holds exactly when some
  `c : Γ(G.X.left, ⊤)` satisfies `ρ(id) · v = c • v` at the universal point `𝟙 G.X`. For the
  converse, a point `g : T ⟶ G.X` factors as `g ≫ 𝟙`, so pulling the universal equation back
  along `g.left.appTop` gives the equation at `g` with multiplier `g.left.appTop c`. This uses
  `pointMatrix_naturality` and the published `scalarMap_naturality`.
- `MatrixRepresentation.isStableLine_restrict_iff`: let `q : H ⟶ G` be a homomorphism with
  `[Epi q.hom.hom.left]`, and let `v` have a unit coordinate `v i₀`. Then `v` spans a stable
  line of `ρ.restrict q` exactly when it spans one of `ρ`. For the forward direction, the
  equation at the universal point of `H` is the universal equation of `G` pulled back along
  `q.hom.hom.left.appTop`. This map is injective by the published
  `Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi`, so the algebra lemma above
  produces a multiplier on `G`. The converse composes points with `q`.

## Trigonalizability over a field

Here `k : Type u` is a field and `G`, `H`, `H'` are group schemes over `Spec k`.

- `IsTrigonalizable.of_epi`: if `H` is trigonalizable and `q : H ⟶ G` has
  `[Epi q.hom.hom.left]`, then `G` is trigonalizable. A nonzero vector over a field has a
  nonzero, hence invertible, coordinate.
- `IsTrigonalizable.of_flat_surjective`: the same conclusion for `q` with flat and surjective
  underlying scheme morphism. Mathlib's `Flat.epi_of_flat_of_surjective` supplies the
  epimorphism.
- `IsTrigonalizable.of_iso`: for an isomorphism `e : H ≅ H'`, `IsTrigonalizable H'` implies
  `IsTrigonalizable H`. Restrict along `e.inv`, then cancel `e.hom ≫ e.inv`.

## Corepresented groups

`TrigonalizableMatrixCriterion` takes `F : CommAlgCat.{u} R ⥤ GrpCat.{u}` with a
corepresentation `e` by `B : CommAlgCat.{u} R`, and the published universal coefficient matrix
`UnipotentMatrixCriterion.coefficientMatrix e ρ`.

- `isStableLine_iff`: for `ρ : MatrixRepresentation (Corepresented.groupScheme F e) n`,
  `ρ.IsStableLine v` holds exactly when there is `c : B` with
  `∑ j, v j • coefficientMatrix e ρ i j = v i • c` for every `i`. At the universal affine point,
  global functions are identified with `B` by the bijective map
  `(Scheme.ΓSpecIso (CommRingCat.of B)).inv`. Surjectivity of this map turns the
  global-function multiplier into an element of `B`, and injectivity transfers the equations.
- `isTrigonalizable_iff_isMatrixTrigonalizable k F B e`: with the coordinate bialgebra
  `AffineLinearEmbedding.bialgebra e`, `IsTrigonalizable (Corepresented.groupScheme F e)` holds
  exactly when `CoalgebraTrigonalizable.IsMatrixTrigonalizable k B`. The proof follows the
  published `corepresentedMatrixUnipotence`. A coefficient matrix gives the representation
  `Corepresented.LinearEmbedding.toGL`, whose universal matrix it is
  (`coefficientMatrix_toGL`). Conversely, the universal matrix of a representation, reindexed
  by `Fin (Fintype.card n)`, is a coefficient matrix, by `coefficientMatrix_comul` and
  `coefficientMatrix_counit`. Both directions then apply `isStableLine_iff`.

All declarations use one arbitrary universe `u`, matching the published files they copy, and
add no hypotheses beyond those stated above.
