# Contracting cocharacters of quaternionic symplectic groups

Module `Langlands.GroupScheme.Quaternionic.SymplecticCocharacter`.

Setting as in `SymplecticPoints`: `K` a field, `D` a finite-dimensional central division
`K`-algebra, `σ : FirstKindInvolution K D`, `n` a nonempty finite index type. Weights and the
weighted cocharacter come from `FiniteAlgebraWeightedDynamic`.

## Results

- `tensorMatrixEquiv_val_eq`: the matrix of a point over `R ⊗ D` is the coefficient comparison
  of its unit in `R ⊗ M_n(D)` (by definition).
- `tensorMatrixEquiv_constPoint_swapUnit`: the constant point of the transposition matrix has
  the transposition matrix on every test.
- `ambientCocharacter K D w`: the weighted cocharacter `t ↦ diag(t^{w i})` of the unit group of
  `M_n(D)`, with the canonical basis.
- `ambientCocharacter_pairWeight_reducedNorm`: for the weight `pairWeight a b`
  (`1` at `a`, `-1` at `b`), the reduced norm of every value is `1`. On each test the value
  equals `μ (π μ π⁻¹)⁻¹`, where `μ` has weight `indicatorWeight a` and `π` is the constant
  transposition point (`weightMatrix_pairWeight`). The reduced norm is a homomorphism to the
  commutative group of points of `𝔾_m`, so it kills this commutator. No reduced norm is
  computed.
- `FirstKindInvolution.matrix_weightMatrix`, `weightMatrix_mul_mul_weightMatrix`,
  `weightMatrix_isometry`: the weighted diagonal is fixed by the conjugate transpose of any
  involution of the first kind (its entries are central scalars). It preserves every Gram
  matrix `G` with `G i j ≠ 0 → w i + w j = 0`.
- `FirstKindInvolution.ambientCocharacter_mem_range_unitaryGroupι`: hence, for `H₀` with
  `H₀ i j ≠ 0 → w i + w j = 0`, every value of the cocharacter lies in the unitary group of
  `H₀`. The proof translates the isometry equation through `isometry_iff_coefficientEquiv`.
- **`FirstKindInvolution.symplecticCocharacter σ H₀ a b hH`**: under
  `hH : ∀ i j, H₀ i j ≠ 0 → pairWeight a b i + pairWeight a b j = 0`, the cocharacter with
  weight `pairWeight a b` factors through `σ.symplecticGroup H₀`. It is constructed with the
  published `IsRepresentedBy.liftOfLE`, and `symplecticCocharacter_comp` identifies its
  composite with `symplecticAmbientι H₀` with `ambientCocharacter K D (pairWeight a b)`.

For the standard Gram matrices `gramTwo D` and `gramThree c` of `StandardGenerationTwo/Three`,
the hypothesis `hH` holds with `(a, b) = (0, 1)` and with `(a, b) = (1, 0)`.

## Provenance

Internal. These are the cocharacters `t ↦ diag(t, t⁻¹[, 1])` acting by `t` on a hyperbolic
vector `e`, by `t⁻¹` on its partner `f` and trivially on the complement, as in the route
suggested by the task. Everything is derived from the published unit, unitary and symplectic
group schemes. The reduced-norm argument via a commutator replaces a computation of the reduced
norm.
