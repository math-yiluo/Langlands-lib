# The base change of `SU(D, h)` to a splitting field, in any degree

Lean module: `Langlands.GroupScheme.Quaternionic.DegreeSplittingIso`
(namespace `Langlands.GroupScheme.Quaternionic.DegreeSplitting`).

Setting: `D` a central division algebra, finite-dimensional over a field `K`, with an
involution of the first kind `σ`; `H ∈ M_n(D)` for a nonempty finite index type `n`;
`e : L ⊗[K] D ≃ₐ[L] M_κ(L)` a matrix chart over a field extension `L`, for a finite index
type `κ`; `Φ = matrixChartR e R` the matrix chart of `DegreeSplittingMatrix`; and
`C = splitGram e σ H` the split Gram matrix. Let `P : M_{(Fin k ⊕ Fin k) × (n × κ)}(L)` and
`P' : M_{(n × κ) × (Fin k ⊕ Fin k)}(L)` be rectangular matrices.

This internal module identifies the base change of `σ.symplecticGroup H` to `L` with the
split symplectic group `SymplecticMatrix.groupScheme (Fin k)`, given `P P' = 1`, `P' P = 1` and
`P C Pᵀ = J`. It generalises the sections `Darboux` and `Scheme` of the Library module
`Quaternionic.SymplecticReductive`, which treat `κ = Fin 2`. The definitions and proofs are
the same, with `Fin 2` replaced by `κ`. The points machinery (`unitPoint`,
`unitPoint_unitary`, `exists_unitPoint_eq`, `unitPoint_naturality`) and the matrix lemmas
`card_eq_of_mul_eq_one` and `det_mul_mul_of_mul_eq_one` are used from that Library module.

## Darboux matrices

For a commutative ring `R` with compatible `K`- and `L`-algebra structures:

* `map_mul_map_eq_one`, `map_mul_map_eq_one'`, `map_darboux`: the relations `P P' = 1`,
  `P' P = 1` and `P C Pᵀ = J` survive mapping the entries into `R`.
* `darbouxMatrix e P P' R u = P Φ(u) P'` (entries of `P`, `P'` mapped into `R`).
  `darbouxMatrix_one` and `darbouxMatrix_mul`: it is multiplicative (using `P P' = 1`,
  `P' P = 1`). `darbouxMatrix_injective`: it is injective, since `P' (P Φ(u) P') P = Φ(u)`.
  `darbouxMatrix_naturality`: it is natural in `L`-algebra maps `R → R'`.
* `darbouxMatrix_mem_iff`: `P Φ(u) P'` is symplectic exactly when
  `u (1 ⊗ H) τ_R(u) = 1 ⊗ H`, for `τ = σ.matrix n`. This combines the Library's
  `SymplecticMatrix.mul_mul_mem_symplecticGroup_iff` with `mul_mul_baseChange_eq_iff`.
* `exists_darbouxMatrix_eq`: every symplectic matrix `g` is `P Φ(w) P'` for a unit `w` that is
  unitary for `H` and has reduced norm one. The unit is `Φ⁻¹(P' g P)`, with inverse
  `Φ⁻¹(P' g⁻¹ P)`. Its reduced norm is `det (P' g P) = det g = 1`, by
  `reducedNorm_eq_det_matrixChartR`, `det_mul_mul_of_mul_eq_one` (the two index types have
  the same size by `card_eq_of_mul_eq_one`) and Mathlib's `SymplecticGroup.det_eq_one`.

## The isomorphism of group schemes

Assume `P P' = 1`, `P' P = 1` and `P C Pᵀ = J`. For a scheme `T` over `Spec L`, let `R` be
`restrictedSections K L T`, the global sections with their `K`- and `L`-algebra structures.

* `splitPointsHom`: the group homomorphism `x ↦ P Φ(unitPoint x) P'` from points of
  `σ.baseChangeSymplecticGroup H` to `Sp_{2k}(R)` (`splitPointsHom_apply`).
* `splitPointsHom_bijective`: it is bijective. Injectivity: `darbouxMatrix` is injective, and
  points are determined by their units, since the inclusions `unitaryGroupι` and
  `symplecticGroupι` are monomorphisms and `FiniteAlgebraUnits.pointsEquiv` and
  `GroupScheme.baseChangePointsEquiv` are bijections. Surjectivity: `exists_darbouxMatrix_eq`
  and `exists_unitPoint_eq`.
* `splitPointsEquiv` is the resulting multiplicative equivalence (`splitPointsEquiv_apply`).
  `splitPointsEquiv_naturality`: it is natural in `T`.
* `splittingIso : σ.baseChangeSymplecticGroup H ≅ SymplecticMatrix.groupScheme (Fin k) L` is
  obtained from the Library's `isoOfPointModels`.
* `pointsEquiv_splittingIso_hom`: on points, the splitting isomorphism is `x ↦ P Φ(x) P'`.
  Precisely, `SymplecticMatrix.pointsEquiv` of `x ≫ splittingIso.hom` equals
  `splitPointsEquiv T x`.

## Provenance

Over a splitting field, `SU(D, h)` becomes the symplectic group of the split alternating
form (Tits 1966, Table II, type `C_n`). The proofs are adapted from the Library's
`Quaternionic.SymplecticReductive`, with `Fin 2` replaced by a general finite index type.
