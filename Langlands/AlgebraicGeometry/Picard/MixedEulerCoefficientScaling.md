# Tensor additivity and power scaling of mixed Euler coefficients

This internal module defines `MixedEulerCoefficientTensorAdditive` for the canonical mixed Euler coefficient of actual line bundles and proves it on a Noetherian separated integral scheme proper over any field in universe `u`. The dimension is bounded above by `d + 1`, and the mixed coefficient is taken at index `d` in truncation `d + 1`. Neither line bundle needs to be ample.

The proof compares an arbitrary coefficient line bundle with the structure sheaf on a nonempty affine open where it is trivial. The four kernels and cokernels of the coherent graph projections have support dimension strictly below `d + 1`. The top coherent Euler twist theorem makes their `d`-th forward differences unchanged by a second line-bundle twist. Exact coherent Euler additivity, both before and after tensoring, therefore makes the `d`-th difference of the tensor-additivity error vanish. Evaluation of the actual mixed Euler polynomials and the rational polynomial difference comparison identify their coefficients at `d`.

Induction on the exponent then proves that tensor power `n` of the coefficient line bundle multiplies its mixed coefficient by `n`, including `n = 0`. The ambient dimension bound is positive; this module asserts no tensor additivity formula for the separately defined dimension-zero mixed coefficient.

All assertions are derived from the Library's actual coherent graph, support bounds, tensor exactness, coherent Euler additivity and rational polynomial comparison, together with the internal top-twist result. No new literature theorem, geometric trace formula or unconditional Rosati positivity theorem is asserted.
