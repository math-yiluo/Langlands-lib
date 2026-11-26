# Nonvanishing of the reflected partial integral

`UnequalDualPartial.partialDualWhittakerIntegral_ne_zero_above_of_ordinary`
starts with two fixed cuspidal vectors spherical outside \(S\). Assume their
ordinary partial Whittaker integral has a nonzero value on every right
half-plane. The theorem gives a nonzero value of their dual partial Whittaker
integral on every right half-plane, with the dual functions and the block Weyl
element in the standard unequal-rank unfolding.

Take an ordinary nonzero value to the right of the convergence bounds for
unfolding and the partial Euler product, and to the right of the sum of the
two Satake bounds. For each unramified place the norm of every product
\(\alpha\beta q_v^{-s}\) is bounded by \(q_v^{A+B-\operatorname{Re}s}<1\),
where \(A,B\) are the Satake bounds. The local logarithm of the pair Euler
factor gives its value as a complex exponential, so each factor is nonzero.
Summability of the deviations from one then gives a nonzero infinite product.
The ordinary Euler factorization and unfolding yield one nonzero value of the
entire unequal-rank cuspidal integral \(I\).

The reflected function \(s\mapsto I(1-s)\) is entire and has a nonzero value.
Its zeros are discrete, so it has a nonzero value beyond any prescribed bound
and in the right half-plane for absolute convergence of the dual Whittaker
integral. The global functional equation and dual unfolding identify this
value with the full dual Whittaker integral for the same vectors. The
one-place cell argument in `UnequalDualPartialNonvanishing` transfers
nonvanishing to the partial dual integral.

The global analytic input is Cogdell's Theorem 2.1, printed p. 207, in
`cogdell-2004-analytic-theory-gln`. The proof of Theorem 4.1 on printed
pp. 219–220 uses the global functional equation and the ordinary and dual
Euler products. The implication between nonvanishing statements above is
derived from those identities.
