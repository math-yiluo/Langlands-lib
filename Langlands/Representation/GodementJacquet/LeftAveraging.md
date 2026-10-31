# Left averaging inside full-matrix integrals

Module `Langlands.Representation.GodementJacquet.LeftAveraging`.

## `Langlands.GodementJacquet.leftAverage_integral`

Let `G` be a group with a measurable multiplication and inversion, and let `μ`
be an s-finite left-invariant measure on `G`. Let `Ω ⊆ G` be measurable with
`μ Ω < ∞`, and let `a, W : G → ℂ` satisfy `a (x * g) = a g` for every `x ∈ Ω`
and every `g`. If `g ↦ a g * W g` is `μ`-integrable, then

* `g ↦ a g * ∫_{x ∈ Ω} W (x * g) dμ(x)` is `μ`-integrable, and
* `∫ a g * (∫_{x ∈ Ω} W (x * g) dμ(x)) dμ(g) = μ(Ω) * ∫ a g * W g dμ(g)`,

where `μ(Ω)` is the real number `μ.real Ω`, viewed in `ℂ`.

This is the Fubini computation behind left compact averaging of Whittaker
functions (Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3)*,
Ann. of Math. 109 (1979), equations (3.1.3)-(3.1.4), there with Ω a compact
open subgroup and `a = Φ · |det|^s`). The statement here is internal and
generic: it uses no property of `GL_n`.

## Proof

Write `ν = μ|_Ω`, a finite measure. The product `1 ⊗ (a W)` is integrable for
`ν × μ`. On `ν × μ`-almost every `(x, y)` we have `x ∈ Ω`, so left invariance of
`a` gives `a y = a (x⁻¹ * y)`; hence `1 ⊗ (a W)` agrees almost everywhere with
`H(x, y) = a (x⁻¹ * y) * W y`. The shear `(x, g) ↦ (x, x * g)` preserves `ν × μ`
(`measurePreserving_prod_mul`, using left invariance of `μ`), and
`F = H ∘ shear` is `F(x, g) = a g * W (x * g)`. Therefore `F` is integrable,
its fiberwise integral in `x` is the averaged integrand (giving integrability by
`Integrable.integral_prod_right`), and

`∫∫ F = ∫ H = ∫ 1 ⊗ (a W) = ν(G) * ∫ a W = μ(Ω) * ∫ a W`

by Fubini (`integral_prod_symm`), the change of variables along the shear,
almost-everywhere equality and `integral_prod_mul`.
