# Absolute convergence of intertwining integrals from that of Eisenstein series

This module proves the implication

`intertwiningAbsoluteConvergence_of_eisenstein :
  EisensteinAbsoluteConvergenceStatement.{u} → IntertwiningAbsoluteConvergenceStatement.{u}`.

Both propositions are published, in `Langlands.Global.AdelicEisensteinConvergenceStatement` and
`Langlands.Global.AdelicIntertwiningConvergenceStatement`. The Eisenstein proposition is the
module's only premise, and the module does not prove it. That proof is the target of Task 5490
(`1832dcb1-0d24-4d4b-b194-f272613d96c9`). So this module does not establish the convergence of
intertwining integrals unconditionally. It reduces that convergence to the Eisenstein statement,
with the same constant `R`.

The module also defines `AdelicGroupPoints.intertwiningRationalCoset`, the class map
`δ ↦ P(F) w⁻¹ δ` from rational points of a subgroup functor of `G` to `P(F) \ G(F)`. The
reduction uses it.

## Provenance

The route is the one in Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*
(1995), II.1.6, proof of (i) (printed p. 88). They bound the integral of `|φ_λ(w⁻¹ u g)|` over
`(U'(k) ∩ wU(k)w⁻¹) \ U'(𝔸)` by
`∫_{U'(k) \ U'(𝔸)} ∑_{γ ∈ P(k) \ G(k)} |φ_λ(γ u g)| du`. Here `U'(k) \ U'(𝔸)` is compact. The
series converges uniformly on compact sets by II.1.5. The Lean proof follows this route in a
pointwise form, as an internal deduction from the published definitions. It does not integrate
the series. Instead it builds an integrable function on the quotient that dominates the
integrand. The analytic input is used as stated in `EisensteinAbsoluteConvergenceStatement`: a
summable majorant of the Eisenstein terms that is uniform for `g` in a compact set and `s` in a
compact parameter set.

The three P(F)-invariance lemmas in the first section restate, under new names, the argument of
the Task 5490 staged candidate `9eafa10a-e0b0-441f-8ae8-5446db618f7a`
(`Langlands/Global/AdelicEisensteinRationalCosets.lean`, lemmas
`map_rational_mem_parabolicQuotientSubgroup`, `IsIwasawaCompact.parameterTwist_rational_mul`,
`IsIwasawaCompact.eisensteinTerm_eq_of_representative`). That candidate is unpublished, so it
cannot be imported. The new names avoid a clash once both are published.

## Rational translations (`section Rational`)

Notation: `p : P → G` is a parabolic with geometric unipotent radical `iU` and rational Levi `l`.
`K` satisfies `hK : IsIwasawaCompact p K`, and `φ` is left invariant under
`parabolicQuotientSubgroup F p iU l`, which is `U(𝔸) M(F)`.

- `map_rational_mem_parabolicQuotientSubgroup_of_levi`: the image of a rational point of `P` lies
  in `U(𝔸) M(F)`. The rational Levi gives a unipotent radical `U'` with `M × U' ≅ P`. The point
  splits as `m u'` with `m ∈ M(F)` and `u' ∈ U'(F)`. Since `iU` is the greatest smooth connected
  unipotent normal subgroup, `u'` lies in `U(F)`. Naturality of the principal-point map then sends
  both factors into `U(𝔸) M(F)`.
- `IsIwasawaCompact.parameterTwist_map_rational_mul`: `φ_λ(x g) = φ_λ(g)` for every rational
  point `x` of `P`. Here `φ_λ = hK.parameterTwist φ λ`. `φ` is invariant by the previous item, and
  the height power is invariant by the Library lemma `IsIwasawaCompact.height_rational_mul`.
- `IsIwasawaCompact.eisensteinTerm_mk`: the Eisenstein term at the coset `P(F) ρ₀` equals
  `φ_λ(ρ₀ g)` for every representative `ρ₀ ∈ G(F)`. The chosen representative differs from `ρ₀`
  by a rational point of `P`, so the previous item applies.

## The class map (`section RationalCoset`)

This section has one definition and the lemma it needs. `S` is any subgroup functor of `G`, and
`w` is a rational point of `G`, with adelic image `innerAdelicPoint F G w`.

- `inv_innerAdelicPoint_mul_mem_rationalSubgroup`: for a rational point `δ` of `S`, the product
  `(innerAdelicPoint F G w)⁻¹ δ` is a rational point of `G`. The point `innerAdelicPoint F G w` is
  the principal image of `w` (Library lemma `innerAdelicPoint_eq_rational`). The point `δ` is the
  principal image of a rational point of `S`. The rational subgroup of `G(𝔸)` is closed under
  products and inverses.
- `intertwiningRationalCoset F p w δ` (definition): the coset
  `P(F) (innerAdelicPoint F G w)⁻¹ δ` in `ParabolicRationalCosets F p`, which is `P(F) \ G(F)`. It
  is `Quotient.mk` applied to the rational point of the previous item. For `S` the image of `V`,
  this is the map `δ ↦ P(F) w⁻¹ δ` of Mœglin–Waldspurger II.1.6 (i). The reduction below uses it
  as the map `cls`.

## The injectivity step (`mul_inv_mem_intertwiningRationalSubgroup`)

Setting: the hypotheses of the Weyl conjugation `(w, c)`, as in
`Langlands.Global.conj_mem_parabolicUnipotentImage` (module
`Langlands.Global.AdelicIntertwiningRadicalIntersection`). Write `W = innerAdelicPoint F G w`.

Statement: let `δ, δ'` be rational points of `V`, and suppose
`(W⁻¹ δ') (W⁻¹ δ)⁻¹ ∈ P(𝔸)`. Then `δ' δ⁻¹` lies in
`intertwiningRationalSubgroup F p iU (iV ≫ q) W`, which is `V(F) ∩ W U(𝔸) W⁻¹`.

Proof: the element `(W⁻¹ δ') (W⁻¹ δ)⁻¹` equals `W⁻¹ (δ' δ⁻¹) W`. The result
`conj_mem_parabolicUnipotentImage` (`w⁻¹ V w ∩ P ⊆ U`) puts it in `U(𝔸)`.

Consequence: the map `δ ↦ P(F) W⁻¹ δ` from `V(F)` to `P(F) \ G(F)` has its fibres in single
cosets of `V(F) ∩ W U(𝔸) W⁻¹`.

## A compact fundamental set (`AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range`)

Let `V` be smooth, connected and unipotent, and `j : V → G`. Then the image of `V(𝔸)` in `G(𝔸)`
contains a compact `Ω` that meets every coset `V(F) v`: for each `v` there is
`ρ₀ ∈ V(F)` with `ρ₀ v ∈ Ω`. The proof takes the compact set of the Library theorem
`AdelicGroupPoints.exists_isCompact_rational_mul_mem_of_split`, which uses the published theorems
`perfectFieldUnipotentSplit` and `splitUnipotentAffineTorsorStatement`. It then transports that
set along the continuous surjection `adelicRangeMap` onto the image.

## The reduction (`intertwiningAbsoluteConvergence_of_eisenstein`)

All hypotheses of `IntertwiningAbsoluteConvergenceStatement` are kept, and the universe is the
same.

1. The Eisenstein statement, applied to the same `F, G, P, …, φ`, supplies `R`. The same `R` is
   used. Fix a compact `C ⊆ G(𝔸)`, coordinates `e`, and a compact `Λ` of regular parameters.
2. Take `Ω` as in the previous section for `V = range (iV ≫ q)`. The Eisenstein statement, at
   the compact set `Ω · C ⊆ G(𝔸)`, gives a summable `b_E` on `P(F) \ G(F)`. It satisfies
   `‖eisensteinTerm φ (e s) h c‖ ≤ b_E c` for all `h ∈ Ω · C`, all cosets `c` and all `s ∈ Λ`.
3. Let `cls(δ) = P(F) W⁻¹ δ` for `δ ∈ V(F)`. This is
   `intertwiningRationalCoset F p w δ` from the section on the class map. Its fibres lie in
   cosets of `Γw = V(F) ∩ W U(𝔸) W⁻¹` by the injectivity step. The set `P(F) \ G(F)` is
   countable because `G(F)` is discrete in the second-countable group `G(𝔸)`.
4. The measure `normalizedHaarMeasure` on `V(𝔸)` is left invariant and finite on the compact `Ω`.
   Its normalizing constant is the inverse of a nonzero mass, so it is finite. Then
   `LeftCosetSpace.exists_integrable_majorant_of_cover` (module
   `Langlands.Global.LeftCosetImageMajorant`) gives `b` on `Γw \ V(𝔸)`, integrable for
   `intertwiningMeasure`, with `b_E (cls δ) ≤ b (Γw δ ω)` for all `δ ∈ V(F)` and `ω ∈ Ω`.
5. For a class `x` with representative `v`, choose `ρ₀ ∈ V(F)` with `ρ₀ v ∈ Ω`. Put
   `δ = ρ₀⁻¹` and `ω = ρ₀ v`, so that `x = Γw δ ω`. By `eisensteinTerm_mk`, the Eisenstein term
   at `cls δ` and the point `ω g ∈ Ω · C` is `φ_λ(W⁻¹ ρ₀⁻¹ ρ₀ v g)`, which is
   `φ_λ(W⁻¹ v g)`. This is the intertwining integrand at `x`. So for `g ∈ C` and `s ∈ Λ`,
   `‖intertwiningIntegrand … (e s) g x‖ ≤ b_E (cls δ) ≤ b x`.

This module uses no hypothesis that the target statement lacks. It needs no positivity of `φ`
and no Gindikin–Karpelevich computation.
