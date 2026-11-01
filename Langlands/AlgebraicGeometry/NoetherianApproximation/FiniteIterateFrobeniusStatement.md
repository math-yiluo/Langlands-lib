# Finite iterates of Frobenius

`FiniteIterateFrobeniusStatement` asserts that, for every commutative ring
`R` of finite type over the integers, every natural number `n`, and every
exponential characteristic `p` of `R`, the ring endomorphism
`iterateFrobenius R p n` is finite. Here finiteness means that its target
is a finitely generated module over its source through that endomorphism.
The map sends `x` to `x^(p^n)`.

Mathlib's exponential characteristic also permits `p = 1` in
characteristic zero. In that case the endomorphism is the identity.
The assertion requires neither a domain nor a reduced ring, and includes
`n = 0`.

This is an internal auxiliary statement for finite normalization of
finite type integer domains. Its provenance is the elementary integral
and finite type criterion for a finite ring map: each `x` satisfies the
monic polynomial `X^(p^n) - C x` through the Frobenius iterate, while the
integer algebra map factors through that iterate. This file states the
result and does not assert a normalization theorem.
