# Fixed vectors and unipotence under quotient maps

This is a derived construction from the existing all-test
`MatrixRepresentation`, `IsFixedVector`, `fixedSubmodule` and `IsUnipotent`
definitions. Its entry definition,
`MatrixRepresentation.fixedSubmoduleRestrictEquiv`, identifies the actual fixed
modules before and after restriction along a group homomorphism whose underlying
scheme morphism is an epimorphism. The module also proves that the existing
representation-theoretic unipotence predicate descends along such homomorphisms,
in particular along flat surjections.

The construction is internal to the Library. It reuses
`Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi` from
`Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent`, and
Mathlib's `AlgebraicGeometry.Flat.epi_of_flat_of_surjective`. No external
structural assertion is a premise.

## Fixed-vector equations

Fix a commutative ring object `R : CommRingCat.{u}` at arbitrary universe `u`,
actual group schemes `G,H` over `Spec R`, and a finite index type `n : Type`
with decidable equality. The index has exactly the universe scope used in the
existing `MatrixRepresentation` interface. No field, affineness, smoothness or
connectedness hypothesis is imposed here; the empty index is allowed.

`scalarMap_naturality` says that, for every morphism `a : W ⟶ T` of test
schemes over `Spec R`, pullback along `a.left` takes the image of a coefficient
`c : R` in `Γ(T, ⊤)` to its image in `Γ(W, ⊤)`. Its proof unfolds the
structure-ring maps and uses the equation defining a morphism in `Over`.

`MatrixRepresentation.isFixedVector_iff_universal` tests fixedness at the
identity morphism `𝟙 G.X`, viewed as the universal `G`-valued point. In one
direction, specialize the defining all-test fixed-vector equation. In the other,
pull that equation back along each point `g : T ⟶ G.X`. Matrix naturality
identifies the resulting matrix with `ρ.pointMatrix T g`; scalar naturality
identifies every entry of the coefficient vector. Pullback commutes with the
finite sums and products of matrix multiplication, giving precisely the
defining fixed-vector equation on every scheme test.

`MatrixRepresentation.isFixedVector_restrict_iff` assumes a homomorphism
`q : H ⟶ G` with `Epi q.hom.hom.left` in the category of schemes. A vector
fixed by `ρ` is fixed by its restriction, by composition of test points. For
the converse, it suffices by the universal criterion to prove the equation at
`𝟙 G.X`. Pull each coordinate of that equation back along the underlying
scheme map of `q`. Representation and scalar naturality identify this with
the restricted fixed-vector equation at `𝟙 H.X`. Injectivity of pullback on
global sections along a scheme epimorphism reflects each coordinate equation,
which proves the claim. This argument never chooses a lift of a point on its
original test scheme.

## The actual fixed modules

`MatrixRepresentation.fixedSubmodule_restrict_eq` upgrades the preceding
equivalence for each coordinate vector to equality of the submodules of
`n → R` defined in `Reductive.Basic`.

`MatrixRepresentation.fixedSubmoduleRestrictEquiv` is the corresponding
`R`-linear equivalence from `(ρ.restrict q).fixedSubmodule` to
`ρ.fixedSubmodule`. Both its forward map and inverse are the identity on
underlying coordinate vectors. The fixed-vector equivalence supplies their
membership proofs; inverseness, additivity and scalar compatibility are
definitional. It is an equivalence of the existing fixed modules.

## Unipotence

Now let `k : Type u` be any field and let `q : H ⟶ G` be an actual
homomorphism over `Spec k`. `IsUnipotent.of_epi` assumes that the underlying
scheme map of `q` is epimorphic and that `H` satisfies the existing
`IsUnipotent` definition. For each representation `ρ` of `G` indexed by a
nonempty finite `n : Type`, restrict it to `H` and obtain a nonzero fixed
vector from unipotence of `H`. The same coordinate vector is nonzero and is
fixed by `G`, by `isFixedVector_restrict_iff`. This proves exactly the
Library's predicate `IsUnipotent G`, with its original all-test quantifiers.

`IsUnipotent.of_flat_surjective` replaces the scheme-epimorphism premise by
`Flat q.hom.hom.left` and `Surjective q.hom.hom.left`. Mathlib's scheme
epimorphism theorem supplies the required instance, so the preceding result
applies. No quasi-compactness, finite-presentation or exact-kernel assumption
is needed for this implication.

These theorems can supply the unipotence conclusion for a quotient map once
its flatness and surjectivity have been proved. They construct no quotient or
central subgroup, prove no comparison with geometric definitions of
unipotence, and do not prove the full `SemigroupOrderedProductStatement`.
