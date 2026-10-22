# Degree-two inflation injectivity under subgroup H1 vanishing

Author: Worker 138.

`Langlands.Cohomology.h2InflationInjectivity` proves exactly the published
proposition `Langlands.Cohomology.H2InflationInjectivity.{u}`. For every common
universe `u`, commutative ring `k`, group `G`, representation `A`, and normal
subgroup `S`, vanishing of `H¹(S,A)` implies injectivity of the actual Mathlib
map `(groupCohomology.HInfRes A S 2).f` from `H²(G/S,A^S)` to `H²(G,A)`.
There are no finiteness or trivial-action assumptions. The coefficient
cochains use Mathlib's inhomogeneous differential

`(d₁₂ A b)(g,h) = A.ρ g (b h) - b (g*h) + b g`.

The proof uses arbitrary, possibly unnormalized cocycles. It proves the
injectivity part of the parent inflation–restriction theorem; it does not
assert exactness at the middle term.

## Implemented proof

Since inflation is a linear map, it suffices to show its kernel is zero.
`h2_inflation_injective` uses `H2_induction_on` to represent a class by an
actual two-cocycle `c` of the quotient representation `A.quotientToInvariants S`.
Compatibility of `H2π` with the cohomology map turns the vanishing of its
inflation into a primitive `b : G → A` satisfying

`A.ρ g (b h) - b (g*h) + b g = c(gS,hS)`

in `A`. The following helpers descend this primitive.

1. `h1_cocycle_principal` uses `Subsingleton` to set every `H1π` class equal
to zero. `H1π_eq_zero_iff` then expresses a one-cocycle as `g ↦ A.ρ g a - a`.
2. `h2_primitive_restriction` first obtains `b(1) = c(1,1)` by evaluating
at `(1,1)`. The value `c(1,1)` is `S`-invariant. Restricting the primitive
equation to `S × S` shows that `s ↦ b(s) - b(1)` is an `S`-one-cocycle.
3. `h2_adjust_primitive` applies H1 vanishing to this one-cocycle, obtaining
`a : A`. Subtracting `g ↦ A.ρ g a - a` from `b` leaves its differential
unchanged and makes `b(s) = c(1,1)` for every `s : S`.
4. `h2_primitive_invariant` evaluates the adjusted equation at `(g,s)`.
The two-cocycle identity at the identity gives `c(gS,1) = g·c(1,1)`,
so `b(gs) = b(g)`. Normality turns this into `b(sg) = b(g)` as well.
Evaluating at `(s,g)` and using `c(1,gS) = c(1,1)` then gives
`A.ρ s (b g) = b g`.
5. `h2_inflated_boundary_descends` uses these two conclusions to define a
cochain on `G/S` with values in `A^S` by quotient lifting. Quotient induction
in both arguments reduces its differential to the original primitive
equation. Thus `c` is a quotient coboundary.

`H2π_eq_zero_iff` now kills the original quotient class, establishing
injectivity. The final theorem introduces precisely the published target's
parameters and applies `h2_inflation_injective`.

## Provenance

The statement is the injectivity part of Jean-Pierre Serre, *Local Fields*
(1979), Chapter VII, section 6, Proposition 5, specialized to degree two,
printed pages 117–118 / PDF pages 123–124. Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The published statement pair supplies its source correspondence. Serre uses
dimension shifting; the present direct primitive-descent proof and its
supporting lemmas are an internal derivation by Worker 138 using Mathlib's
low-degree cocycle and quotient APIs.
