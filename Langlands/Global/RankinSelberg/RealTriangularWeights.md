# Normalized diagonal weights for real matrix integrals

`RealTriangularWeightsStatement` and its proof `realTriangularWeights` record the two cancellations in rank `n = r + 1`. Let `d` be a full real diagonal, `u` upper unipotent, `k` orthogonal, and let `χᵢ : ℝˣ → ℂ` be the inducing functions (the identities are algebraic and do not require these functions to be characters). The two products are:

- the row Jacobian times the normalized inducing factor at `d` times `|det(diag(d) u k)|^(s+r/2)`, which is `∏ᵢ χᵢ(dᵢ)|dᵢ|^s`;
- the column Jacobian times the normalized inducing factor at `d⁻¹` times `|det((diag(d⁻¹) u k)⁻ᵀ)|^(s+r/2)`, which is `∏ᵢ χᵢ(dᵢ⁻¹)|dᵢ|^s`.

`realNormalizedAbs_det_triangular` computes the positive absolute determinant as `∏ᵢ |dᵢ|`. On the dual side, inverse transpose and diagonal inversion cancel, giving the same product. The two Jacobians have exponents `−(r−i)` and `−i`, respectively, at index `i = 0, …, r`. The normalized inducing factor contributes `r/2−i` in the first product and `−(r/2−i)` in the second. Lean expands positive-base powers using real logarithms, then adds the exponents with the shift `s+r/2` in each case. No assumption on the signs of `dᵢ` is used.

These identities are internal calculations for the diagonal reduction of Jacquet (2009), §4.7, pp. 30–31. The proof follows the Library's complex triangular weight calculations with the real normalization `‖x‖^[ℝ:ℝ] = |x|`. This module proves the change-of-variables weights, not the equality of the primal and Fourier-dual matrix integrals or their continuation.
