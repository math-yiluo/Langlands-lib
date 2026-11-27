# Joint evaluation on affine analytic spaces

Let \(K\) be a complete nonarchimedean field with nontrivial norm, let \(P\) be a finite polynomial presentation of a commutative \(K\)-algebra \(A\), and let \(T\) be a topological space. For a finite set of indices, choose elements \(a_i\) of \(A\) and continuous coefficients \(c_i\colon T\to K\). At \((t,x)\) the map evaluates \(\sum_i c_i(t)a_i\) at the seminorm of \(x\). Its domain is `T × Space K P` with the product topology.

The proof compares this evaluation with the one obtained by fixing the coefficients at the limiting parameter. The seminorm triangle inequality bounds the difference by the sum of the scalar-norm differences multiplied by the individual seminorm values of the fixed elements. Continuity of each fixed-element evaluation and of the scalar norms makes this bound tend to zero.

`continuous_pointSeminorm_sum` uses the actual affine point model by multiplicative seminorms that extend the base norm. This model is described in Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*, Remark 3.4.2 (1990). The finite-sum estimate is a derived property of the model.

The corresponding bundled map is `finiteCoefficientEvaluation`.
