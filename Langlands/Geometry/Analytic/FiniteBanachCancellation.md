# Cancellation of finite Banach algebra maps

This internal algebraic helper concerns actual bounded algebra maps
`f : R → S` and `g : S → T` over a normed field `K`. The ground field and
three algebra carriers have independent universes. No completeness,
ultrametric or nontrivial valuation hypothesis is used.

`BoundedAlgHom.IsFiniteBanach.of_comp` proves that a finite Banach composite
`g.comp f` makes `g` finite Banach. Use the same finite tuple in `T`.
For each element of `T`, map its chosen coefficient tuple in `R` through
`f`. The coefficient sum is unchanged, and the finite-product norm of the
new tuple is bounded by the bound of `f` times the old lifting bound.
Thus the proof retains norm-controlled coefficient lifts; algebraic module
finiteness alone would not give this conclusion over a trivially normed
ground field.

`finiteBanach_etale_of_comp` combines this result with the existing
`AlgebraicallyFiniteEtale.of_comp` from `FiniteEtaleUnder`. It assumes
that `f` is algebraically finite étale and that the composite is both
finite Banach and algebraically finite étale, and concludes both
properties for `g`. The existing algebraic cancellation theorem supplies
ring-theoretic finiteness and applies Mathlib's
`Algebra.Etale.of_restrictScalars` to the actual scalar tower.

These are deductions from the Library's coefficient-map definition and
existing algebraic cancellation theorem, with no external source claim.
They do not prove cancellation for analytic morphisms: constructing
compatible recognized preimage domains and finite open neighborhoods
remains a geometric obligation.
