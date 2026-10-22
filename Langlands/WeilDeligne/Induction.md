# Finite-index induction of Weil–Deligne pairs

Worker 17 authored this construction. The subgroup is an actual finite-index
subgroup `S ≤ G`; the source pair uses the restriction of the ambient norm
character. The carrier is the actual equivariant-function model used by
`FiniteRepresentation.induce`.

Since the group acts by right translation, induced monodromy is
`N_ind(f)(g) = nu(g) N(f(g))`. The factor is `nu(g)`, with positive exponent.
`Induction.action_monodromy` derives `r(s)N = nu(s)Nr(s)` from the specified
inverse-action covariance. This proves that weighted monodromy preserves
`f(s*g) = r(s)f(g)`. Its powers have the exact formula
`N_ind^n(f)(g) = nu(g)^n N^n(f(g))`, so the original nilpotence exponent works.
Right translation then proves
`r_ind(h) N_ind r_ind(h)^-1 = nu(h) N_ind`.
These are proofs in the constructor; callers supply no new certificates.

`induceMap` applies a pair morphism pointwise. Linearity and its original
monodromy square prove compatibility with weighted monodromy.
`induceFunctor`, `induceEquiv`, and `induceClass` prove the functor and quotient
obligations. `rank_induce` gives subgroup index times source rank.

The source normalization is Tate, *Number theoretic background*, Corvallis
Part II, printed page 20, §§4.1.1–4.1.2: the pair relation is
`r(w) N r(w)^-1 = nu(w) N`. Printed pages 9–10, §2.1, give induction for
finite-index Weil subgroups. Source ID `tate-1979-number-theoretic-background`,
retained Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The weighted function formula is derived here from those covariance and induction
conventions; it is not claimed as a verbatim formula from Tate.

This is an algebraic construction over an arbitrary field and specified norm.
This algebraic module asserts no continuity or open-inertia condition. The usual complex
topology, the actual local Weil subgroup and norm compatibility, and preservation
of additional predicates remain separate from these intrinsic certificates.
No semisimplification or decomposition is chosen or assumed.
