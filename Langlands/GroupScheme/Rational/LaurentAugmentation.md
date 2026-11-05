# Pointed Laurent functions and nonconstant coefficients

This internal algebraic construction supports the pointed split-torus
domination argument. It applies to the monoid algebra `k[M]` for any
commutative ring `k` and additive commutative monoid `M`; a finite-rank
split torus is the case of a free abelian character group.

`augmentation` is the canonical bialgebra counit, or evaluation of every
character at one. Its kernel `space` consists of functions vanishing at
the identity. `delta m` is the pointed monomial `X^m - 1`.

The linear equivalence `equivalence` takes a pointed function to its
coefficients at nonzero characters. Its inverse sums these coefficients
against the pointed monomials. The coefficient at zero is determined by
the condition that the total coefficient sum vanishes. Consequently
`basis` is the ordinary module basis indexed by the nonzero characters.

In prime characteristic `p`, `delta_pow` proves
`(X^m - 1)^(p^r) = X^((p^r)m) - 1`, and `pow_mem_space` proves that
the kernel is preserved by Frobenius.

The motivation is Springer, *Linear Algebraic Groups*, second edition
(1998), §14.3, particularly 14.3.4(b), printed p.244, and the proof of
14.3.8(i), printed pp.245–246. The full Laurent algebra in the printed
14.3.4(b) has a constant-term obstruction to the asserted Frobenius
freeness: the nonzero operator `T - 1` kills the constant function one
when `T(f) = f^p`. The present construction instead uses functions
vanishing at the identity, as supplied by a pointed pullback of additive
functions. This file proves the ordinary coefficient basis and its
Frobenius identity. It does not claim skew-polynomial freeness, the
classification of elementary unipotent groups, or the splitness
criterion itself.
