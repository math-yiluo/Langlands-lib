# The diagonal torus of the special linear group and its Lie weights

Helper module for the proof of
`Langlands.GroupScheme.SpecialLinearSimplyConnectedPinningStatement`. Author: Worker 61
(Task 5703). It defines a rank-`n` diagonal torus of the Library's group scheme
`SpecialLinear.groupScheme (Fin (n + 1)) R`, which is `SL_{n+1}`. It also computes the torus
weights on the Lie algebra in the matrix coordinates `lieMatrix` of
`Reductive.SpecialLinearLieMatrix`. All declarations are in namespace
`Langlands.GroupScheme.SpecialLinear.FinSucc`. The layout follows the Library's
`SymplecticMatrix.Torus`.

The torus is parametrized by `τ : ULift (Fin n) → Aˣ`. Its point is the diagonal matrix
`diag(τ_0, …, τ_{n-1}, (τ_0 ⋯ τ_{n-1})⁻¹)`.

## Weights of the diagonal entries

- `weightCoord n p : Fin n → ℤ` is the weight of the `p`-th diagonal entry in coordinates:
  `(weightCoord n p)_c = [p = c.castSucc] - [p = last]`. So `p = a.castSucc` has weight
  `e_a` (`weightCoord_castSucc`), and the last index has weight `(-1, …, -1)`
  (`weightCoord_last`). `weightCoord_apply` unfolds the definition.
- `sum_weightCoord`: for each `c`, the sum over `p` of `(weightCoord n p)_c` is `0`.
- `weightCoord_injective`: distinct indices have distinct weights.
- `torusEntry τ p = ∏_c τ_c ^ (weightCoord n p)_c` is the `p`-th diagonal entry. Lemmas:
  - `torusEntry_mul` and `torusEntry_one`: the entry is multiplicative in `τ`.
  - `prod_torusEntry`: the product of all entries is `1`. This uses `sum_weightCoord` and
    the auxiliary `prod_zpow_eq_zpow_sum`.
  - `map_torusEntry`: compatibility with monoid homomorphisms `A →* B`.
  - `torusEntry_castSucc`: `torusEntry τ a.castSucc = τ_a`.
  - `torusEntry_mulSingle`: at `τ = Pi.mulSingle c U`, the entry is
    `U ^ (weightCoord n p)_c`.
  - `prod_zpow_weightCoord_sub`: the monomial of `weightCoord n p - weightCoord n q` is
    `torusEntry τ p * (torusEntry τ q)⁻¹`.
- `torusMatrix τ : Matrix.SpecialLinearGroup (Fin (n + 1)) A` is the diagonal matrix of the
  entries. Its determinant is `1` by `prod_torusEntry`. Lemmas: `coe_torusMatrix`,
  `toGL_torusMatrix` (the image in `GL_{n+1}` is `Matrix.diagonal` of the entries) and
  `map_torusMatrix` (compatibility with ring homomorphisms).
- `torusMatrixHom n A` is `torusMatrix` as a monoid homomorphism `(ULift (Fin n) → Aˣ) →* SL_{n+1}(A)`,
  with `torusMatrixHom_apply`.

## The torus

- `torusPoints n R T` sends points of the split torus `splitTorus (Spec R) (ULift (Fin n))`
  over a test scheme `T` to points of `SL_{n+1}`, through `torusMatrixHom` on global
  sections. `pointsEquiv_torusPoints` computes it, and `torusPoints_naturality` shows it is
  natural in `T`.
- `diagonalTorus n R : (splitTorus.commGroupScheme (Spec R) (ULift (Fin n))).toGrp ⟶ groupScheme (Fin (n + 1)) R`
  is built from these points by the Library's `homOfPoints`. `pointsEquiv_diagonalTorus`
  states that it sends `τ` to `torusMatrix τ` on points over every test scheme.
- `mono_diagonalTorus_hom`: the diagonal torus is a monomorphism. The first `n` diagonal
  entries of `torusMatrix τ` recover `τ` (`torusEntry_castSucc`).
- `units_map_pointsEquiv_eq_torusCoords`: the coordinates of an affine point of the split
  torus agree with the Library's `GeneralLinear.torusCoords`.
- `affinePointsEquiv_diagonalTorus_inclusion`: an affine point `t` of the torus, mapped to
  `GL_{n+1}` through `SL_{n+1}`, is the diagonal matrix `GeneralLinear.diagonalTorusUnits` of
  the entries `torusEntry (torusCoords t) p`.

## Over a field

Let `k` be a field and `𝔻` the split torus `splitTorus.commGroupScheme (Spec k) (ULift (Fin n))`.

- `isAffineHom_groupScheme_of`, `smooth_groupScheme_of`, `connectedSpace_groupScheme_of`:
  the Library's `isAffineHom_groupScheme`, `smooth_groupScheme` and
  `connectedSpace_groupScheme` (for `SL_{n+1}` over `k`), restated as instances for the base
  `CommRingCat.of k`. `isAffineHom_diagonalTorusSource` does the same for `𝔻`.
- `isSplitTorus_diagonalTorus n k`: `𝔻` is a split torus.
- `isClosedSubgroup_diagonalTorus n k`: the diagonal torus is a closed subgroup. A
  monomorphism from a torus is a closed subgroup (`IsTorus.isClosedSubgroup_of_mono`).
- `isSplitSubtorus_diagonalTorus n k`: the two facts together.
- `characterValue_eq_prod`: a character `χ` of `𝔻` takes the value `∏_c t_c ^ χ_c` at an
  affine point with coordinates `t`. Here `χ_c` are the coordinates
  `GeneralLinear.characterCoordEquiv (Fin n) k χ` of the Library's
  `Reductive.GeneralLinearRoots`.
- `mem_weightSpace_diagonalTorus_iff`: a Lie algebra element `X` lies in the Library's
  `weightSpace (diagonalTorus n k) χ` if and only if, for every `k`-algebra `A`, every affine
  point `t` and all `p, q`,
  `torusEntry t p · X_{pq} · (torusEntry t q)⁻¹ = χ(t) · X_{pq}` in `A`, where `X_{pq}` is
  the entry `lieMatrix X p q`. Proof: transport the weight space to `GL_{n+1}` with
  `lieKernelHomLinear_mem_weightSpace_iff` and use the Library's adjoint action of `GL` in
  dual-number coordinates.
- `mem_weightSpace_diagonalTorus_iff_support`: `X` lies in the weight space of `χ` if and only
  if every nonzero entry `X_{pq}` satisfies `χ = weightCoord n p - weightCoord n q` in
  coordinates.
  - Forward direction: evaluate at the Laurent-polynomial point
    `Pi.mulSingle c T` over `k[T, T⁻¹]` and compare exponents of `T`
    (`GeneralLinear.exponent_eq_of_C_mul_T`).
  - Backward direction: `prod_zpow_weightCoord_sub`.

## Provenance

The diagonal maximal torus of `SL_{n+1}` and its weights `ε_p - ε_q` on the Lie algebra are
standard. The coordinates `τ ↦ diag(τ_0, …, τ_{n-1}, (∏ τ_c)⁻¹)` are a choice made for this
project. The proofs follow the Library's `SymplecticMatrix.Torus` and
`Reductive.GeneralLinearRoots`.
