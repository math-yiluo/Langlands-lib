# Tools for normalization at a closed fibre

`ClosedFiberNormalizationToolsStatement.{u,v}` is the conjunction of two
auxiliary assertions, with rings in arbitrary universes.

1. Let `f : R →+* S` be a homomorphism of integral domains, with `R`
   noetherian. If `r` is a nonunit of `R`, `f r ≠ 0`, and the kernel of `f`
   is contained in the principal ideal `(r)`, then `f` is injective.
2. Let `S` be a finite type algebra over a commutative ring `R`, and let
   `q` be a prime ideal of `S`. Suppose `J` is an ideal of `S` for which
   `S / J` is a finite `R`-module. If `J` is contained in the extension to
   `S` of the contraction of `q` to `R`, then `S` is quasi-finite over `R`
   at `q`, in the sense of `Algebra.QuasiFiniteAt`.

These are internal algebraic deductions used in the finite normalization
task. For the first assertion, dividing a kernel element by `r` yields
another kernel element, since `S` is a domain and `f r` is nonzero.
Iteration places the kernel in every power of `(r)`, whose intersection
is zero by the Krull intersection theorem for a proper ideal of a
noetherian domain (`Ideal.iInf_pow_eq_bot_of_isDomain`).

For the second assertion, `S / ((q.under R).map (algebraMap R S))` is a
quotient of the finite module `S / J`. It is therefore finite, hence
quasi-finite, over `R`. The quotient criterion for weak quasi-finiteness
at `q`, followed by the finite type criterion, gives the assertion.

This file states the two tools. It does not assert finite normalization
or the existence of a polynomial normalization chart.
