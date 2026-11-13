# Epsilon products of a global functional equation with trivial L-functions

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the global functional equation of a product of Hecke L-functions is
used after all local L-factors have cancelled: what remains is that the product of the local
epsilon factors over the exceptional places is `1`. This unit proves that deduction for the
published package `RelativeWeilEngine.HasGlobalEquation`. It is elementary complex analysis
(the identity theorem for meromorphic functions) and has no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. `MeromorphicEq f g` is the published
equality of all punctured germs.

## Results

- `meromorphicEq_const_of_eqOn_open`: a meromorphic function on `ℂ` that equals a constant `c` on
  a nonempty open set has the punctured germ of `c` at every point. Proof: `f - c` has meromorphic
  order `⊤` at a point of the open set, hence everywhere on the connected plane (Mathlib's
  `meromorphicOrderAt_eq_top_of_isPreconnected`).
- `MeromorphicEq.comp_one_sub`: equality of punctured germs is preserved by `s ↦ 1 - s`, which maps
  punctured neighbourhoods of `z` into punctured neighbourhoods of `1 - z`.
- `prod_epsilon_eq_one_of_hasGlobalEquation`: let `HasGlobalEquation l d e A Ad Ae B` hold, where
  every local factor `l z s` and dual factor `d z s` that is nonzero equals `1`, and `A`, `Ad`,
  `Ae` have the punctured germs of `1`. Then `∏_{z ∈ B} e z s₀ = 1` at every point `s₀` where this
  product is continuous. Proof: on the right half-plane where the Euler products `Λ`, `Λd`
  converge to nonzero values, every factor is nonzero (`ne_zero_of_hasProd`), hence `1`; so `Λ` and
  `Λd` are `1` there, hence have the germ of `1` everywhere by the first item. The functional equation `Λ(s) A(s) = Ae(s) ∏ e(s) Λd(1 - s) Ad(1 - s)` then gives that
  `∏_{z ∈ B} e z` has the punctured germ of `1` at `s₀`; continuity at `s₀` gives the value.
