# Operator topology on scalar-extension similitudes of a general rational module

This module puts a topology on the published group `ScalarExtensionSimilitudes D V R ψ` and builds the topological-group interface for it. The module `V` is a general rational module with a compatible algebra action. It need not be the regular module of `D`. The group is defined in `Langlands.Shimura.PEL.ScalarExtension`. It is the subgroup of pairs `(g, c)` where `g` is a `D ⊗[ℚ] R`-linear automorphism of `R ⊗[ℚ] V` and `c` is a unit of `R`, such that `ψ_R(g x, g y) = c ψ_R(x, y)`. Here `ψ_R = ψ.baseChange R`, and `D ⊗[ℚ] R` acts through the published `scalarExtensionAlgebraModule`, with `(d ⊗ a)(r ⊗ x) = (a r) ⊗ (d x)`. This module defines no second tensor action, no discrete topology and no new group.

## Standing hypotheses

Throughout, the following hold:

- `D` is a ring with a rational algebra structure. No finiteness is assumed of `D`.
- `V` is a rational vector space with a `D`-module structure and `IsScalarTower ℚ D V`.
- `R` is a commutative ring with a rational algebra structure.
- `ψ` is an arbitrary rational bilinear form on `V`. No nondegeneracy, alternation or involution compatibility is used.

Further hypotheses are added only where stated below. The topology itself needs only `[TopologicalSpace R]`. Joint continuity, the topological-group instance and the basis comparison also need `[ContinuousAdd R] [ContinuousMul R]`. The joint continuity and the topological-group instance further assume `[Module.Finite ℚ V]`. The basis comparison instead takes an explicit finite rational basis of `V`.

## The topology

`scalarExtensionAlgebraModule_one_tmul_smul` is a supporting lemma: the tensor `1 ⊗ r` acts on `R ⊗[ℚ] V` as the scalar `r`. It is proved on pure tensors and extended by additivity.

`scalarExtensionSimilitudeCoordinates` sends a similitude to its forward operator, its inverse operator and its multiplier:

`g ↦ ((⇑g.val.1, ⇑g.val.1.symm), g.val.2)`,

with values in `((R ⊗[ℚ] V → R ⊗[ℚ] V) × (R ⊗[ℚ] V → R ⊗[ℚ] V)) × Rˣ`.

For a topological ring `R`, `scalarExtensionSimilitudesTopology` is the topology induced by this map. The tensor product `R ⊗[ℚ] V` carries its canonical `R`-module topology, `moduleTopology R (R ⊗[ℚ] V)`, for the left `R`-action. The two function spaces carry the pointwise (product) topology. The multiplier carries Mathlib's standard topology on `Rˣ`. This is the coarsest topology in which every evaluation of the forward operator, every evaluation of the inverse operator, and the multiplier are continuous. It is defined directly from the actual operators, not transported from any coordinate system. No topology on `ℚ` and no compatibility of `R` with the usual topology of `ℚ` is used. In particular, it is never assumed that `R` is a topological rational vector space.

## Named carrier

`ScalarExtensionSimilitudePoints D V R ψ` is a `def`-synonym for the underlying type of the subgroup. It carries the subgroup's group structure, and its `TopologicalSpace` instance is `scalarExtensionSimilitudesTopology`. Because the instance lives only on this named carrier, it cannot clash with other topologies on the raw subgroup type. `toSimilitudes` is the identity group isomorphism back to the subgroup, and `toSimilitudes_val` records that it leaves the underlying pair unchanged.

The interface on the named carrier consists of the following:

- `operator` is a group homomorphism to `(R ⊗[ℚ] V) ≃ₗ[R] (R ⊗[ℚ] V)`. It sends a point to its actual forward operator, viewed as an `R`-linear equivalence. This is valid by the supporting lemma above. The simp lemmas are `operator_apply` and `operator_symm_apply`.
- `multiplier` is the published `bilinearSimilitudes.multiplier` for `ψ.baseChange R`. Its simp lemma is `multiplier_apply : multiplier g = g.val.2`.
- The natural `MulAction` on `R ⊗[ℚ] V` is `g • y = g.val.1 y`, recorded as `smul_def`.
- `coordinates_injective` says a point is determined by its operator and multiplier coordinates.

## Continuity with a topology on R only

Assume `[TopologicalSpace R]`. The following results hold:

- `isInducing_coordinates` and `isEmbedding_coordinates`: the coordinate map is inducing, and it is a topological embedding.
- `continuous_iff`: a map `f` from any topological space into the points is continuous exactly when three conditions hold. Each `x ↦ (f x).val.1 y` and each `x ↦ (f x).val.1.symm y` is continuous for fixed `y`, and `x ↦ multiplier (f x)` is continuous.
- `continuous_apply` and `continuous_symm_apply` give continuity of evaluation at a fixed vector.
- `continuous_multiplier` gives continuity of the multiplier. `continuousMultiplier` packages the multiplier as a continuous group homomorphism to `Rˣ`.

## Joint action and topological group

Assume also `[ContinuousAdd R]`, `[ContinuousMul R]` and `[Module.Finite ℚ V]`. The following results hold:

- `continuous_action`: the map `(g, y) ↦ g.val.1 y` on `points × (R ⊗[ℚ] V)` is continuous.
- `continuous_symm_action`: the map `(g, y) ↦ g.val.1.symm y` is continuous.
- `continuousSMul`: the natural action is a `ContinuousSMul` for the module topology on `R ⊗[ℚ] V`.
- The instance `IsTopologicalGroup (ScalarExtensionSimilitudePoints D V R ψ)`: multiplication and inversion are continuous.

The joint continuity proofs use a private helper. Choose a finite rational basis `b` of `V`; its base change `b.baseChange R` is an `R`-basis of `R ⊗[ℚ] V`. Under the module topology, each coordinate functional of this basis is continuous, since it is `R`-linear. Also, `R ⊗[ℚ] V` has continuous addition and scalar multiplication. Any `R`-linear operator `F` satisfies `F y = Σ_i (coordinate_i y) • F(1 ⊗ b_i)`. So a family of operators whose values on the finitely many basis vectors vary continuously is jointly continuous in the operator and the vector. The helper is applied to the forward operators and to the inverse operators.

The topological-group property is then deduced through `continuous_iff`:

- For multiplication, `(g h) y = g (h y)` is continuous by joint continuity of the forward action. The inverse operator of a product satisfies `(g h)⁻¹ y = h⁻¹(g⁻¹ y)`, which is continuous by joint continuity of the inverse action. The multiplier is multiplicative and `Rˣ` has continuous multiplication.
- For inversion, the forward and inverse operator coordinates swap, and the units topology makes inversion on `Rˣ` continuous.

## Agreement with rational-basis matrix coordinates

Let `b` be a finite rational basis of `V`, indexed by a finite type with decidable equality. Then `matrixCoordinates b g` consists of three components:

- the matrix of the forward operator in the basis `b.baseChange R`;
- the matrix of the inverse operator in the same basis;
- the multiplier.

The simp lemmas `matrixCoordinates_fst_fst_apply` and `matrixCoordinates_fst_snd_apply` give the matrix entry at `(i, j)` as the `i`-th basis coordinate of `g(1 ⊗ b_j)`, respectively of `g⁻¹(1 ⊗ b_j)`. `matrixCoordinates_snd` identifies the third component with the multiplier. `toLin_matrixCoordinates_fst_fst` and `toLin_matrixCoordinates_fst_snd` show that the two matrices recover the actual forward and inverse `R`-linear operators.

Assume also `[ContinuousAdd R]` and `[ContinuousMul R]`. `isEmbedding_matrixCoordinates` proves that `matrixCoordinates b` is a topological embedding, where matrices carry the entrywise topology. So the topology defined by finite rational-basis matrix coordinates of both operator directions and the multiplier equals the operator topology. The proof has two steps:

- The matrix coordinates are continuous, because each entry is a continuous coordinate functional applied to a continuous evaluation.
- The map sending a matrix triple back to pointwise operator coordinates through `Matrix.toLin` is continuous, by the explicit finite-sum formula for `Matrix.toLin`. Composed with the matrix coordinates, it gives the operator coordinate map, which is an embedding. Mathlib's `IsEmbedding.of_comp` then gives the result.

## Finite adelic instances and levels

The intended coefficient rings are the existing Library rings `Langlands.Global.FiniteAdeles ℚ` and `Langlands.Global.PrimeToFiniteAdeles p`. They are used with their existing topologies, topological-ring instances and rational algebra structures, and with no further assumption.

- `FiniteAdelicScalarExtensionLevel D V ψ` is `CompactOpenLevel` of the finite adelic points. `PrimeToScalarExtensionLevel D V ψ p` is `CompactOpenLevel` of the points over the prime-to-`p` finite adeles.
- The `toSubgroup` accessor of each level views it as a subgroup of the original `ScalarExtensionSimilitudes` subgroup type.
- For `[Module.Finite ℚ V]`, `finiteAdelic_isTopologicalGroup` and `primeTo_isTopologicalGroup` record the topological-group instances for these two rings.

No existence of compact open subgroups, reductivity statement or coefficient-change functoriality is claimed.

## Provenance

This is an internal derived construction, not a literal theorem of a source. It supplies the standard topology of the group of `D ⊗ R`-linear similitudes of a finite rational PEL module over a topological coefficient ring, as used for the adelic points `G(𝔸^∞)` and `G(𝔸^{∞,p})` and their compact open levels. The motivation is Harris–Taylor (2001), Chapter III.1, pp. 90–92, and Kottwitz (1992), §5, pp. 390–391. Those texts take this topology for granted for the algebraic group `G`. The construction here uses only Mathlib's module, product, function, matrix and units topologies on top of the published algebraic group, and every continuity statement is proved in Lean.
