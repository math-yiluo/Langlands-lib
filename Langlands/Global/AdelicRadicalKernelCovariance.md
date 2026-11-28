# Compact radical kernels and left covariance

Module `Langlands.Global.AdelicRadicalKernelCovariance`.

Let \(P_J=M_JU_J\) be a standard parabolic in a compatible family over a number
field, with adelic maps \(\iota\) for the Levi and \(\iota_U\) for the radical.
The kernel `radicalKernel J β g k` on \(M_J(\mathbb A)\) integrates
\(\beta(g^{-1}\iota_U(u)\iota(m)k)\) against Haar measure on \(U_J(\mathbb A)\).
This is the radical integral in the Iwasawa formula of Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.1.13, printed p. 18.

`radicalKernelCc` bundles this kernel as a compactly supported continuous
function when \(\beta\) is compactly supported and continuous. Joint continuity
restricts to fixed \(g,k\). The support bound of
`exists_compact_radicalKernel_support` applies to their singleton sets, and
the same bound for compact sets gives `exists_compact_tsupport_radicalKernelCc`
by closure inside the common compact set.

The two covariance theorems change variables on \(U_J(\mathbb A)\).
`radicalKernel_mul_radical` uses left invariance of Haar measure to remove a
radical factor multiplying \(g\) on the left. `radicalKernel_mul_levi` gives
\[
K_{\beta}(\iota(x)g,k,m) = \delta_{P_J}(x)\,K_{\beta}(g,k,x^{-1}m).
\]
The conjugation formula `integral_conj_parabolicModulus` contributes
\(\delta_{P_J}(x)\). The remaining Levi factors combine by the homomorphism
property of \(\iota\).

`isAdelicTestFunction_radicalKernel` assumes
`LeviRadicalAverageTestFunctionStatement`. It applies the normalized averaging
statement to the two-sided translate \(z\mapsto\beta(g^{-1}zk)\), which is a
test function by `isAdelicTestFunction_comp_mul_mul`.
`exists_integral_adelicRangeMap_eq_normalized` compares the Haar measure
used in `radicalKernel` to the normalized measure of the represented radical.
The resulting constant scalar multiplication preserves continuity, smooth
archimedean slices, compact support and the two finite-level invariances.

The Iwasawa formula is in the registered source
`moeglin-waldspurger-1995-spectral-decomposition` (collection SHA-256
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`),
chapter file `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, printed
p. 18.
