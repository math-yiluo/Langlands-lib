# The Levi morphism of a hyperbolic pair

Module `Langlands.GroupScheme.Quaternionic.LeviGroupScheme`, namespace
`Langlands.GroupScheme.Quaternionic.LeviScheme`.

## Setting

* `K` is a field and `D` a finite-dimensional `K`-algebra that is a division ring, with an
  involution of the first kind `σ`. `σ.baseChange R` is its extension to `R ⊗[K] D`.
* `GL₁(D)` is `FiniteAlgebraUnits.groupScheme (Module.finBasis K D)`, the group scheme whose
  points over a test `T` are the units of `Γ(T) ⊗[K] D`. This is
  `CentralSimpleUnits.groupScheme K D`.
* `O(H)` is `σ.isometryGroup (BinaryScheme.hyperbolicForm σ)`, the isometry group of the
  hyperbolic form `H = [[0, 1], [0, 0]]` on `D²`. `O(q)` is `σ.isometryGroup q` for
  `q : σ.QuadraticForms n`.
* `h : σ.IsHyperbolicPair q e f` is a hyperbolic pair. `HyperbolicScheme.isometryHom h :
  O(H) ⟶ O(q)` is the published extension of the hyperbolic plane spanned by `e, f`
  (module `HyperbolicGroupSchemeExtension`). On points it is
  `HyperbolicScheme.extendUnits h`, which sends a binary matrix `g` to
  `R g E + (1 - R E)`. Here `E` and `R` are the plane inclusion and its polar retraction.
* Matrices act on row vectors.

## Definitions

* `leviMatrix σ R : (R ⊗[K] D)ˣ →* (M₂(R ⊗[K] D))ˣ` is `BinaryAction.hyperbolicLevi` for
  `σ.baseChange R`, that is `a ↦ diag(a, σ(a⁻¹))`.
* `leviPoints σ T` applies `leviMatrix` to the points of `GL₁(D)` over a test scheme `T`,
  through `FiniteAlgebraUnits.pointsEquiv` and `HyperbolicScheme.matrixPointsEquiv (Fin 2) T`.
* `leviUnitHom σ : GL₁(D) ⟶ GL₁(M₂(D))` is `homOfPoints (leviPoints σ)`.
* `binaryLeviHom σ : GL₁(D) ⟶ O(H)` is the factorization of `leviUnitHom σ` through the
  closed subgroup `O(H)`.
* **`leviHom h : GL₁(D) ⟶ O(q)`** is `binaryLeviHom σ ≫ HyperbolicScheme.isometryHom h`,
  called the Levi morphism here: `e ↦ a e`, `f ↦ σ(a)⁻¹ f`, identity on `{e, f}^⊥` (the
  hyperbolic scaling morphism; see Provenance for its relation to Levi factors).

## Results

* `baseChange_map`: `σ.baseChange` commutes with every change of coefficients.
  `leviMatrix_naturality` follows from it.
* `leviMatrix_isometry`: `L H ᵗL^σ = H` for `L = diag(a, σ(a⁻¹))`, over every coefficient
  algebra. The only nonzero entry is `a · σ(σ(a⁻¹)) = a a⁻¹ = 1`.
* `leviUnitHom_points`, `leviUnitHom_range_le`: the matrix formula on every test scheme, and
  membership in `O(H)`. The isometry defect is `0` by `leviMatrix_isometry`, and `0` lies in
  the alternating subspace (`σ.mem_range_isometryGroupι_iff`).
* `binaryLeviHom_comp : binaryLeviHom σ ≫ σ.isometryGroupι _ = leviUnitHom σ`.
* `leviHom_points`: for every test `T` and point `x` of `GL₁(D)`, the matrix of
  `leviHom h (x)` is `HyperbolicScheme.extendUnits h _ (leviMatrix σ _ x)`.
* **`isometryRationalMatrix_leviHom`**: for `a ∈ Dˣ`, the rational matrix
  (`isometryRationalMatrix`, module `EichlerDynamic`) of the image under `leviHom h` of the
  rational point `(FiniteAlgebraUnits.rationalPointsEquiv _).symm a` is the Levi element
  `levi σ q _ a` of `HyperbolicLevi`.

  Proof. Take the affine test `Spec K` with coefficient algebra `K`. By
  `pointsEquiv_affine` (an instance of the Library's
  `Corepresented.pointsEquiv_eq_affinePointsEquiv`), the coordinates over the test differ
  from the affine coordinates by the section isomorphism `φ : K ≅ Γ(Spec K)`. The
  naturality of `TensorMatrix.equiv`, `leviMatrix` and `extendUnits` moves `φ` outside, and
  `φ` is cancelled by its inverse. This identifies the matrix over `K ⊗ D` with
  `extendUnits h K (leviMatrix σ K (1 ⊗ a))`. By `leviMatrix_of_val` this is the scalar
  extension of `diag(a, σ(a⁻¹))`. By `value_scalarMatrix` the split extension commutes with
  scalar extension, and `Algebra.TensorProduct.lid` removes the scalars
  (`lid_eq_map_equiv`, `scalarMatrix_map_lid`). The result is
  `h.planeUnitsHom (diag(a, σ(a⁻¹)))`. `planeUnitsHom_hyperbolicLevi` identifies this with
  `levi σ q _ a` by comparing the actions on `e`, on `f` and on `{e, f}^⊥`
  (`IsHyperbolic.matrix_ext`, `IsHyperbolicPair.vecMul_planeUnitsHom`).

## Provenance

Internal (Task 5398). `leviHom h` is the hyperbolic scaling morphism `a ↦ ℓ(a)`:
`e ↦ a e`, `f ↦ σ(a)⁻¹ f`, extended by the identity on the orthogonal complement `{e, f}^⊥`.
"Levi morphism" is the name used here for this explicitly defined morphism. The module
constructs it and its point comparisons only. It does not identify its image with an entire
Levi factor and does not construct a parabolic subgroup. In general the image is only the
`GL₁(D)` component of such a Levi factor, which also contains the isometries of
`{e, f}^⊥`. For example, for `K = D = ℝ`, `σ = id` and `q = xy + z² + w²`, with `e, f` the
first two coordinate vectors, the image consists of the matrices `diag(a, a⁻¹, 1, 1)`. The
standard Levi factor also contains `diag(1, 1, -1, -1)`. The module assumes only a hyperbolic
pair, not nondegeneracy or Witt index one.

It is assembled from the published binary Levi matrix (`BinaryAction.hyperbolicLevi`) and the
published plane extension (`HyperbolicScheme.isometryHom`).
