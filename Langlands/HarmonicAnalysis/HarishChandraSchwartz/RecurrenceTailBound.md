# Recovering a right-finite function from a uniformly bounded tail

Let `F` be a complex-valued function on a group `G` and let `a ∈ G`. Suppose a
polynomial of degree at most `N` annihilates `F` under right translation by
`a`, each coefficient has norm at most `B`, and the constant coefficient has
norm at least `α > 0`. For every `m ∈ G` and natural number `r`, the module
proves the backward estimate

`‖F(m)‖ ≤ ((N + 1) * (α⁻¹ * B))^r ∑_{i=0}^{r*N} ‖F(m * a^(r+i))‖`.

The proof uses the explicit inverse `q = -p(0)^(-1) divX(p)` of `X` modulo
`p`. Its degree is at most `N`, and every coefficient has norm at most
`α^(-1)*B`. Multiplying the modular inverse identity shows
`q(T)^r T^r F = F`. The existing product coefficient bound controls `q^r`
by `((N+1)*(α^(-1)*B))^r`. Expanding the recovery identity at `m` and applying
the triangle inequality and coefficient bound gives the estimate. The same
derivation first proves the modular recovery identity for any complex module
and linear endomorphism.

This is an internal quantitative adapter for the finite exponent polynomial
argument used in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), VI.2.1 and VI.2.3, printed
pp.297–300, source `waldspurger-2003-plancherel`. It does not establish an
actual orbit recurrence, an actual uniform constant-term threshold, or the
principal positive decay theorem.
