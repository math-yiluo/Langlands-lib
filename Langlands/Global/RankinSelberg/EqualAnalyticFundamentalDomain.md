# Central translation of fundamental domains and a fibration formula

Module `Langlands.Global.RankinSelberg.EqualAnalyticFundamentalDomain`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Setting: a group `G` with a left-invariant measure `μ`, a countable subgroup `Γ`, and a
measurable fundamental domain `s` for the left action of `Γ`.

## Central translation

- `isFundamentalDomain_preimage_mul_left`: if `b` is central, `{x | b x ∈ s}` is again a
  fundamental domain. This is Mathlib's `IsFundamentalDomain.preimage_of_equiv` applied to
  `x ↦ b x`, which commutes with the action because `b` is central.
- `measure_inter_preimage_mul_left`, `setLIntegral_comp_mul_left`,
  `setIntegral_comp_mul_left`: for central `b`, a `Γ`-invariant set `T` and a `Γ`-invariant
  function `f`, `μ(s ∩ b⁻¹T) = μ(s ∩ T)` and `∫_s f(b x) = ∫_s f(x)` (lower Lebesgue and
  Bochner). Proof: left invariance of `μ` moves the integral to the translated domain, and
  integrals of invariant functions over two fundamental domains agree
  (`IsFundamentalDomain.setLIntegral_eq`, `measure_set_eq`, `setIntegral_eq`).

## Fibration over a central family

Let `ζ : A → G` be measurable with central values, `ν` an s-finite measure on `A`, `t ⊆ A`, and
`S ⊆ G` a measurable `Γ`-invariant set with `ν(t ∩ {a | ζ(a)⁻¹ g ∈ S}) = 1` for every `g`.

- `lintegral_eq_lintegral_fibration`: for every measurable `Γ`-invariant `f ≥ 0`,
  `∫_s f dμ = ∫_(s ∩ S) ∫_t f(ζ(a) g) dν(a) dμ(g)`.
- `quotientMeasure_eq_map_fibration`: the quotient measure of `s` on `Γ \ G` (Library
  `LeftCosetSpace.quotientMeasure`) is the image of `μ|_(s ∩ S) ⊗ ν|_t` under
  `(g, a) ↦ Γ ζ(a) g`.

Proof of the first: Tonelli (`lintegral_lintegral_swap`) exchanges the integrals. For fixed
`a`, central translation by `b = ζ(a)` turns `∫_s 1_S(g) f(b g)` into `∫_s 1_S(b⁻¹ g) f(g)`.
Exchanging back gives `∫_s f(g) ν(t ∩ {a | ζ(a)⁻¹ g ∈ S}) dμ(g) = ∫_s f`. The second follows
from the first applied to indicators of preimages of measurable sets of `Γ \ G`.

## Provenance

The fibration of `Γ \ G` over a central subgroup is classical (e.g. the measure decomposition
behind Cogdell 2004, §2.3, printed p.209, for the integral over
`Z_n(𝔸) GL_n(F) \ GL_n(𝔸)`). The abstract formulation and its proof are internal.
`inv_mul_comm_of_central` is an auxiliary algebraic identity.
