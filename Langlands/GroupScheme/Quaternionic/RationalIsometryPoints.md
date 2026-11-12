# Rational points of the isometry group

Module `Langlands.GroupScheme.Quaternionic.RationalIsometryPoints`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.Eichler`.

## Setting

* `σ` is an involution of the first kind of a finite-dimensional division `K`-algebra `D`.
* `q` is a Tits `σ`-quadratic form on `D^n`, with representative `Q = Quotient.out q`.
* The Library's isometry group scheme `σ.isometryGroup q` is the closed subgroup of the unit
  group scheme of `M_n(D)` cut out by the condition `u Q ᵗu^σ - Q ∈ R ⊗ {X - ᵗX^σ}` on
  `R`-points. It is the scheme `Corepresented.cutGroupScheme` of the family
  `IsometryCut.isometryFamily`.

## Results

* `lid_mem_baseChange_iff`: for a `K`-subspace `M` of a `K`-algebra `A`, an element
  `y ∈ K ⊗[K] A` lies in `M.baseChange K` iff `lid y ∈ M`. Here
  `lid : K ⊗[K] A ≃ A` is `Algebra.TensorProduct.lid`.
* The reused `IsometryCut.lid_baseChange` from `IsometryRowAction`: `lid (τ_K y) = τ (lid y)` for an involution `τ` and its base change `τ_K`.
* The reused `IsometryCut.lid_defect` from `IsometryRowAction`: `lid` sends the isometry defect `y (1 ⊗ Q) τ_K(y) - 1 ⊗ Q` to
  `lid(y) Q τ(lid y) - Q`.
* `map_lid_mem_rationalIsometryGroup_iff`: a unit `y` of `K ⊗[K] M_n(D)` satisfies the
  defining condition of `O(q)` over `K` iff its image under `lid` lies in
  `rationalIsometryGroup σ q`.
* `isometryFamilyEquiv σ q`: the group isomorphism, induced by `lid`, from the `K`-valued
  isometry family to `rationalIsometryGroup σ q`.
* **`isometryGroupRationalPointsEquiv σ q : rationalPoints (σ.isometryGroup q) ≃*
  rationalIsometryGroup σ q`**: the `K`-points of `O(q)` are exactly the rational
  isometries. It is the composite of three isomorphisms:
  * the Library's comparison of rational points with affine `K`-points,
    `GaloisPointComparison.rationalCoeffEquiv`;
  * the corepresentation of the cut subgroup scheme, `Corepresented.affinePointsEquiv`;
  * `isometryFamilyEquiv`.

## Provenance

Internal: a direct identification of the rational points of the Library's group scheme
`σ.isometryGroup q` with the explicit subgroup from `RationalIsometry`. It uses the
Library's corepresentation of cut-out subgroup schemes. It is used in Task 5398 to transfer
explicit rational computations (Eichler transformations, hyperbolic scalings) to rational
points of `O(q)`.
