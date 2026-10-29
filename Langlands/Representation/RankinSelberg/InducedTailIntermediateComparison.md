# Product integration and weights for the intermediate tail comparison

Supporting work by Worker 318 for the intermediate-rank calculation
in JPSS section 9.3, printed 456–457. These are derived elementary integration
and weight identities. They do not establish the quotient measure formula,
produce localized Whittaker coefficients or prove the final span inclusion.

A measure positive on nonempty open sets and finite on compact sets assigns
each nonempty compact open set a finite positive measure. The real volume is
therefore strictly positive. The product of the two localization volumes,
multiplied by any positive real chart normalization, is again strictly positive.
These hypotheses are stated directly; no lower-triangular Haar measure is
constructed or silently normalized here.

On the product of a small quotient space and the two localization parameter
spaces, an integrable complex function of the quotient variable times both
finite-volume measurable indicators is integrable. The proof uses
`Integrable.mul_prod` twice after establishing integrability of the constant
indicators. `integral_prod_mul` and `integral_indicator_const` evaluate its
actual Bochner integral as the original integral times the two real volumes.
A separate identity retains an explicit nonnegative extended-real scaling of
the product measure. The Bochner integral identities are totalized identities;
the preceding integrability theorem supplies the absolute-convergence claim
when its hypotheses hold.

Simultaneous row and column reindexing preserves the determinant and therefore
the actual determinant weight, including the explicit rank casts.
The determinant of the actual lower-block matrix is the product of its diagonal
block determinants, by the determinant formula for a block triangular matrix.
When the lower-triangular block has determinant norm one, the full test matrix
has the same spectral determinant weight as the leading block.

Finally, write the leading rank as `B`, the test rank as `B+d`, and the full
rank as `B+d+c`. The extension factor is
`|det g|^((d+c)/2)`, the full integral contributes
`|det g|^(s-c/2)`, and the proposed quotient density contributes
`|det g|^(-d)`. Their product is `|det g|^(s-d/2)`, exactly the tail weight.
The Lean proof compares real and complex powers of the positive determinant
norm, combines complex exponents, and checks the exponent equality by ring
arithmetic. This proves the cancellation for the stated density; it supplies
no evidence for the density's measure-theoretic change-of-variables law.

Provenance is internal derivation from Mathlib product integration and the
published actual lower-block matrix construction. The motivating source is
the registered `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
