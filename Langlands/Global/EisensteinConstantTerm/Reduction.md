# The constant-term formula from absolute convergence and the geometric lemma

Module `Langlands.Global.EisensteinConstantTerm.Reduction`. It proves the published target
`Langlands.Global.EisensteinConstantTermStatement` (module `AdelicEisensteinConstantTermStatement`;
Bernstein–Lapid Lemma 6.10 (6.17), Mœglin–Waldspurger II.1.7) from two named premises:

- `Langlands.Global.EisensteinAbsoluteConvergenceStatement` (published, module
  `AdelicEisensteinConvergenceStatement`; proved by `Langlands.Global.eisensteinAbsoluteConvergence`
  in `AdelicEisensteinConvergenceProof`);
- `Langlands.Global.GeometricLemmaUnfoldingStatement` (module
  `EisensteinConstantTerm.GeometricLemmaUnfoldingStatement`).

## Declarations

- `EisensteinConstantTermReductionStatement : Prop`, defined as
  `EisensteinAbsoluteConvergenceStatement.{u} → GeometricLemmaUnfoldingStatement.{u} →
  EisensteinConstantTermStatement.{u}`.
- `eisensteinConstantTermReductionStatement_proof : EisensteinConstantTermReductionStatement.{u}`,
  which is the theorem `eisensteinConstantTerm_of_convergence_of_unfolding`.
- Helpers in namespace `Langlands.Global.EisensteinConstantTerm`:
  - `exists_isCompact_mul_mem`: if `Γ \ H` is compact and `H` locally compact, there is a
    compact `C` with every `v = δ v₀`, `δ ∈ Γ`, `v₀ ∈ C`. Proof: cover the quotient by the
    images of the interiors of compact neighbourhoods, which are open, and take a finite
    subcover.
  - `subgroupConstantTerm_mul_invariant`: a factor `m` that is left invariant under the adelic
    points of `range j` comes out of `subgroupConstantTerm F j` (`integral_mul_const`).

None of the target's hypotheses is dropped, and the universe `u` is retained. The premises are
used at the same universe.

## The proof

Fix the data of the target. Let `R₀` be the constant of `EisensteinAbsoluteConvergenceStatement`
for `φ`. Fix `λ` with `r.IsRegularParameter hA hT R₀ λ` and `g ∈ G(𝔸)`, and put
`Φ = φ_λ = hK.parameterTwist φ λ`.

1. Properties of `Φ`:
   - `Φ` is continuous: `φ` is continuous by `IsAdelicSmoothFunction`, and the height is
     continuous (`continuous_parameterTwist`).
   - `Φ` is left invariant under `P(F)`, by `rationalImage_le_parabolicQuotientSubgroup` and
     `heightPower_rational_mul`. The Levi hypothesis there is `r.isCompatible.levi`.
   - `Φ` is left invariant under `U(𝔸)`, because `φ` is left invariant under
     `parabolicQuotientSubgroup` and by `heightPower_unipotent_mul`.
2. `V` is normal in `Q` (`IsUnipotentRadical.isNormal`), and `V(F) \ V(𝔸)` is compact. This is
   the Library's `compactSpace_rationalQuotient_range_unipotent`; `V` is smooth, connected and
   unipotent.
3. The bound:
   - `exists_complexParameterEquiv` gives coordinates `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`.
   - `exists_isCompact_mul_mem` gives a compact `C_V ⊆ V(𝔸)` meeting every class of
     `V(F) \ V(𝔸)`.
   - The convergence premise, applied to the compact set `C_V g` and the compact parameter set
     `{e⁻¹ λ}`, gives a summable `b` with `‖hK.eisensteinTerm φ λ x c‖ ≤ b c` for `x ∈ C_V g`.
   - Since the series of `‖Φ(c̄ x)‖` is left `G(F)`-invariant (`tsum_out_mul_left`),
     `∑'_c ‖Φ(c̄ v g)‖ₑ ≤ ofReal(∑' b) =: B₀` for every `v ∈ V(𝔸)`.
4. Apply `constantTerm_series_eq` (module `Core`) with `Q'_i = rationalImage F (g' i ≫ q)`.
   - The hypothesis on `Q'_i` is `(hdat i).rationalImage_right`.
   - `R i y` is `∫ C_{U'_i}Φ(w_i⁻¹ x̄ y)` for `intertwiningMeasure`, and `Int i y` is the
     integrability of that integrand.
   - The identification `hB` is the premise `GeometricLemmaUnfoldingStatement` applied to
     `h = Φ`, with the hypotheses `hG`, `r.isCompatible.parabolic`, `hU`, `hq`, `hV`, `hP' i`,
     `hU' i`, `hQ' i`, `hV' i` and `hdat i`.
5. Twist matching. The target's integrand is
   `(hK' i).parameterTwist (C_{U'_i} φ) (parameterRestrict (f i) λ) (w_i⁻¹ x̄ γ_c g)`. It equals
   `C_{U'_i}Φ(w_i⁻¹ x̄ γ_c g)`:
   - `heightPower_restrict` gives `m_{P'_i}^{λ ∘ f_i} = m_P^λ`;
   - `subgroupConstantTerm_mul_invariant`, with `m_P^λ` left invariant under `U'_i(𝔸)`
     (`heightPower_unipotent_mul` for `iU' i ≫ f i`; `U'_i` is unipotent), gives
     `C_{U'_i}(φ m_P^λ) = (C_{U'_i}φ) m_P^λ`.

   Hence `intertwiningIntegral` is `R i`. The three conclusions of the core theorem are then
   conclusions 1–3 of the target. `hK.eisensteinSeries φ λ` is by definition
   `x ↦ ∑'_c Φ(c̄ x)`.

## What is not proved here

Neither premise is proved here. The convergence premise is used only through one bound: summability,
over `P(F) \ G(F)`, of `sup_{v ∈ C_V} |φ_λ(γ v g)|` for one `λ`. The geometric-lemma premise is
used only for `h = φ_λ`. The statement `EisensteinConstantTermStatement` itself is not claimed
unconditionally. That needs proofs of both premises.

## Provenance

The route is the proof of BL Lemma 6.10 (J. Bernstein and E. Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal pp. 208–209, PDF pages 22–23),
which BL call a straightforward generalization of Mœglin–Waldspurger II.1.7 (registered as
`moeglin-waldspurger-1995-spectral-decomposition`, printed pp. 91–93). The identification with
the intertwining integral is the premise `GeometricLemmaUnfoldingStatement`. Conclusions 1 and 2 come from the bound on `|φ_λ|`,
as in MW II.1.7 (4).
