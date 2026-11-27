# Intertwining operators are invariant under parameters of an ambient parabolic

Module `Langlands.Global.AdelicIntertwiningParameterShift`, namespace
`Langlands.Global.AdelicGroupPoints`. It is a helper module for the proof
`Langlands.Global.intertwiningElementaryChain` and has no statement of its own.

## Setting

`F` is a number field and all group schemes are over `Spec F`. Closed subgroups `p : P → G`,
`q : Q → G` and `pL : L → G` with a subgroup `K` of `G(𝔸)` that is Iwasawa
(`IsIwasawaCompact`) for all three. `P` and `Q` lie in `L` through `eP : P → L` and `eQ : Q → L`
with `eP ≫ pL = p` and `eQ ≫ pL = q`. The pair `(w, c)` presents a Weyl conjugation from `P` to
`Q` (`IsWeylConjugation p l q l' w c`), `l' : M' → Q` is a rational Levi subgroup with retraction
`π'`, and `w = y ≫ pL` for a rational point `y` of `L`. For `ν ∈ X^*(L) ⊗ ℂ`, `ν|_P` denotes
`parameterRestrict eP ν`.

## Declarations

* `IsIwasawaCompact.heightPower_add'` and `IsIwasawaCompact.heightPower_neg_mul_self`:
  `m_P(g)^{s+t} = m_P(g)^s m_P(g)^t` and `m_P(g)^{-s} m_P(g)^s = 1`, from the definition of
  `heightPower` as the exponential of a linear form in the parameter.
* `weylParameter_parameterRestrict`: `weylParameter l c π' (ν|_P) = ν|_Q`. In `L`, the identity
  `c ≫ l ≫ eP = l' ≫ eQ ≫ Int(y)⁻¹` follows from `IsWeylConjugation.comp_eq` after cancelling the
  monomorphism `pL` (`innerIso_hom_comp`). Characters of `L` are invariant under inner
  automorphisms (`DominantMultiple.innerIso_hom_comp_character`), so for `χ ∈ X^*(L)` the
  characters `χ ∘ eP ∘ l ∘ c ∘ π'` and `χ ∘ eQ` of `Q` have the same restriction to `M'`; they
  are equal because restriction `X^*(Q) → X^*(M')` is injective
  (`IsRationalLeviSubgroup.characterRestrict_bijective`).
* `IsIwasawaCompact.heightPower_parameterRestrict`: `m_P(g)^{ν|_P} = m_L(g)^ν`, the published
  `IsIwasawaCompact.heightPower_restrict`.
* `innerAdelicPoint_comp`: the adelic point of `y ≫ pL` is the image under `pL` of the principal
  adelic point of `y`.
* `IsIwasawaCompact.intertwiningOperator_add_parameterRestrict`: if the unipotent radical `V` of
  `Q` is unipotent (`IsUnipotent V`), then for all `ψ`, `μ ∈ X^*(P) ⊗ ℂ`, `ν ∈ X^*(L) ⊗ ℂ` and
  `g`, `M(w, μ + ν|_P)ψ(g) = M(w, μ)ψ(g)` for the operator
  `hK.intertwiningOperator hQ iU l iV c π' w`. No regularity of `μ` is assumed.

## Proof of the invariance

The operator is `m_Q(g)^{-wμ} · ∫ ψ_μ(w⁻¹ v g) dv` (`IsIwasawaCompact.intertwiningOperator`).

1. *Integrand.* The twist at `μ + ν|_P` is the twist at `μ` times `m_P(h)^{ν|_P} = m_L(h)^ν`
   (`heightPower_add'`, `heightPower_parameterRestrict`). For `h = w⁻¹ v g` with `v ∈ V(𝔸)`, the
   representative `v` is the image of a point of `V(𝔸)` in `L(𝔸)` via `iV ≫ eQ`, and `w⁻¹` is a
   rational point of `L` (`innerAdelicPoint_comp`). The height of `L` is left invariant under
   unipotent points and rational points (`IsIwasawaCompact.heightPower_unipotent_mul`,
   `IsIwasawaCompact.heightPower_rational_mul`), so `m_L(w⁻¹ v g)^ν = m_L(g)^ν`. By
   `integral_const_mul` the integral at `μ + ν|_P` is `m_L(g)^ν` times the integral at `μ`.
2. *Normalization.* By `weylParameter_parameterRestrict`, the transported parameter of
   `μ + ν|_P` is `wμ + ν|_Q`, so the normalizing factor is
   `m_Q(g)^{-wμ} · m_Q(g)^{-ν|_Q} = m_Q(g)^{-wμ} · m_L(g)^{-ν}`.
3. The factors `m_L(g)^{-ν}` and `m_L(g)^ν` cancel (`heightPower_neg_mul_self`).

## Provenance

Derived. This is the computation behind the rank-one dependence in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024),
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §8.6, pp. 225–226:
"if `w` is an elementary symmetry `s_α` … `M(w, λ)` depends only on `⟨λ, α^∨⟩`". Here it is
the invariance of the defining integral under characters of the ambient parabolic `L`, written for
the Library's `IsIwasawaCompact.intertwiningOperator`.
