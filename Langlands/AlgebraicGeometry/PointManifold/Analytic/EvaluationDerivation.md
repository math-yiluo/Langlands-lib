# Derivations obtained by differentiating actual point families

Author: Worker 115.

Let `k` be any nontrivially normed field, `B` a commutative `k`-algebra,
`E` a normed `k`-space, and `q : E → (B →ₐ[k] k)` a family. Fix `t v : E`
and assume every evaluation `x ↦ q x b` differentiable at `t`.
`pointAlgebra (q t)` lets `B` act on the value field through this point.
`evaluationDerivation q t v h` is the actual derivation `B → k` sending
`b` to `fderiv k (fun x => q x b) t v` for this action. Its additivity and
coefficient linearity follow from the derivative rules for addition and
constant scalar multiplication. The derivative product rule is its Leibniz
rule. `evaluationDerivation_apply` records the defining formula.

For a `k`-algebra map `φ : A →ₐ[k] B` that is formally unramified,
`evaluationDerivation_eq_zero_of_unramified` shows that if this tangent kills
every `φ a`, it kills every `b`. The proof makes `B` an `A`-algebra through
`φ`, gives `k` the compatible `A`-action through `q t ∘ φ`, and regards the
derivation as an `A`-linear derivation by the Leibniz rule and vanishing on
`φ`. Formal unramifiedness makes `Ω[B/A]` trivial. The universal equivalence
between linear maps out of that module and derivations makes every relative
derivation zero.

This is an internal construction for Task 5259, derived from Mathlib's
Frechet derivative rules, derivations, Kahler differentials and formal
unramifiedness. It needs neither completeness nor finite dimension nor
analytic regularity; those conditions enter its affine-chart application.
