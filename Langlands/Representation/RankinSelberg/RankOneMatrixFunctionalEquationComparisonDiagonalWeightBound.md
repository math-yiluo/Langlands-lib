# Bounded diagonal weights and a determinant power

This source-free real-variable lemma bounds the inverse upper-Borel modulus times the inverse-coordinate monomial that occurs in a unipotent slice-volume estimate. For positive coordinates `x i` bounded above by any fixed real number `rho`, multiplying that weight by one fixed nonnegative integral power of `prod i, x i` gives a uniform nonnegative finite bound.

`diagonalWeightDegree n e` is the number of strictly upper-diagonal pairs plus the sum of the supplied natural exponents `e i`. Its value depends only on the rank and those exponents. The bound holds for every `n`, including zero, and every real box bound; if that box contains no positive tuple, the quantified assertion is vacuous.

The proof sets `R = max 1 rho` and `D = prod i, x i`. The identity `D / x i = prod j != i, x j` bounds each `x i` inverse times `D` by `R^(n+1)`. Each inverse root ratio times `D` is then bounded by `R^(n+2)`. Multiplying these bounds over upper roots and the monomial factors gives the displayed determinant degree and a concrete finite constant. No asymptotic expansion, representation, Haar change of variables, or Whittaker convergence premise enters this lemma.
