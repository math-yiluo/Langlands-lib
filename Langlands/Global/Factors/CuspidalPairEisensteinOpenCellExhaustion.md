# One-place decomposition and exhaustion for the partial open-cell integrals

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellExhaustion`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellExhaustion`.

The module contains the measure-theoretic part of the unramified factorization of the
open-cell integral of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md): the space
`M(𝔸) = M_((t+1)×(r+1))(𝔸)` of adelic matrices is exhausted by the sets `U_A` of matrices
integral outside finite sets `A` of finite places (`integralOutside F r t A` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md)), and
adding one place `v` to `A` decomposes `U_(A ∪ {v})` into the translates of `U_A` by the
classes of `M(F_v) / M(𝒪_v)`. All measures are left invariant measures on `M(𝔸)` for its
Borel σ-algebra; no product decomposition of a measure is used.

## Content

- `localAdele v x`: the adele with component `x ∈ F_v` at the finite place `v` and `0` at all
  other places (also at the archimedean places); `finiteProjection_localAdele`,
  `finiteProjection_localAdele_of_ne`, `localAdele_add`.
- `localMatrix v y`: the adelic matrix with entries `localAdele v (y i j)`, for a local matrix
  `y`; `localMatrix_add`.
- `matrixComponent v Y`: the matrix of components at `v` of an adelic matrix `Y`;
  `matrixComponent_localMatrix`, `matrixComponent_localMatrix_of_ne`, `matrixComponent_add`,
  `matrixComponent_sub`, `continuous_matrixComponent`.
- `mem_integralOutside_iff`, `integralOutside_mono`, `isClosed_integralOutside`,
  `measurableSet_integralOutside`.
- `mem_adicCompletionIntegers_iff_canonical`: the integers of the completion `F_v` are the
  integers of the canonical valuation of the `p`-adic field `CompletionPadic.padicField v`.
- `LocalQuotient r t v`: the quotient `M_((t+1)×(r+1))(F_v) / Shahidi.integralMatrices`, the
  index type of the sum in `Shahidi.UnramifiedOpenCellSumStatement`;
  `mem_integralMatrices_iff`, `isOpen_integralMatrices`, and the instance
  `countable_localQuotient` (the quotient is discrete because the lattice is open, and
  separable because `F_v` is, by `finiteCompletion_separableSpace`).
- `cell A v y`: the translate of `U_A` by `localMatrix v (Quotient.out y)`;
  `iUnion_cell` (for `v ∉ A` the cells cover `U_(A ∪ {v})`, which is
  `integralOutside F r t (Finset.cons v A hv)`), `pairwise_disjoint_cell`, `cell_eq_preimage`,
  `measurableSet_cell`, and `setIntegral_cell` (the integral over a cell is the integral over
  `U_A` of the translated function, by invariance of the measure).
- **`setIntegral_cons_eq_mul`** (one-place step). For `v ∉ A`, a function `f` integrable on
  `U_(A ∪ {v})`, numbers `c(y)` with `∑_y c(y) = L` and
  `f(localMatrix v (Quotient.out y) + Z) = c(y) f(Z)` for every class `y` and every `Z ∈ U_A`:
  `∫_(U_(A ∪ {v})) f = L ∫_(U_A) f`.
- `exists_mem_integralOutside`: every adelic matrix lies in some `U_A` (restricted product).
- **`integral_eq_hasProd_mul_setIntegral`** (exhaustion). Let `f` be integrable on `M(𝔸)`, let
  `c_v` be numbers indexed by the finite places `v ∉ S` with `∏_v c_v = p` (as `HasProd`), and
  suppose that for every finite `A ⊇ S` and `v ∉ A` the integral over `U_(A ∪ {v})` is `c_v`
  times the integral over `U_A`. Then `∫ f = p · ∫_(U_S) f`.

## Proofs

- `iUnion_cell`: a matrix `Y ∈ U_(A ∪ {v})` lies in the cell of the class of its component
  `Y_v`: `Y - localMatrix v (Quotient.out [Y_v])` has integral component at `v`, because the
  representative differs from `Y_v` by an integral matrix, and the same components as `Y`
  elsewhere. Conversely, translating by a matrix supported at `v` does not change components
  away from `v`.
- `pairwise_disjoint_cell`: if two translates meet, the components at `v` of the
  representatives differ by an integral matrix, so the classes agree.
- `setIntegral_cons_eq_mul`: countable additivity of the integral over the disjoint
  measurable cells (`hasSum_integral_iUnion`), `setIntegral_cell` on each cell and the
  factorization hypothesis give the sum `∑_y c(y) ∫_(U_A) f`; uniqueness of sums gives
  `L ∫_(U_A) f`.
- `integral_eq_hasProd_mul_setIntegral`: for finite sets `B` of places outside `S`, induction
  on `B` with the step hypothesis gives `∫_(U_(S ∪ B)) f = (∏_(v ∈ B) c_v) ∫_(U_S) f`. The sets
  `U_(S ∪ B)` increase with `B` and cover `M(𝔸)` (`exists_mem_integralOutside`), so the left
  side tends to `∫ f` (`tendsto_setIntegral_of_monotone`), while the right side tends to
  `p ∫_(U_S) f`.

## Provenance

The decomposition is the measure-theoretic content of the step "for `Re s` large the
coefficient is `∏_v W_v(e_v)`" in the proof of Shahidi (1981), Theorem 5.1, pp. 351–352
(`shahidi-1981-certain-l`), for the unipotent radical `U'(𝔸)`: Shahidi writes the integral
over `U'(𝔸)` as a product of local integrals over `U'(F_v)`. Here the local integral at an
unramified place is replaced by the sum over `M(F_v) / M(𝒪_v)` of the integrand on the
translated cells, so that no local Haar measure has to be normalized; the formulation is
internal.
