# Determinants to first order at filtered depths

Bushnell and Kutzko use the high-depth comparison of the trace and determinant characters in *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`, printed p. 132 (PDF p. 144). The comparison here gives an integral bound on the determinant's higher-degree terms.

For an endomorphism `x` of chain depth `k ≥ 0` and a chain of period `e`, every term of degree `j ≥ 2` in `det(1+x)` has uniformizer order at least `d` if `e(d−1) < 2k`. In a splitting basis, a nonzero matrix entry in row `i` and column `l` has its uniformizer order bounded by the depth and the difference of the two basis vectors' indices. A permutation term in a principal minor uses the same row and column indices. Summing the entry inequalities cancels the index differences, giving `e ord(term) ≥ j k`. Zero terms already satisfy the integral bound. Sums of these signed terms remain integral after multiplication by `π^(−d)`.

Mathlib's determinant expansion gives constant term `1`, linear term `trace(x)`, and higher coefficients given by principal minors. Applying the bound to the higher coefficients at `1` shows that `π^(−d)(det(1+x)−1−trace(x))` lies in the integer ring.
