# Restriction of the intertwining operator to the target Levi subgroup

Module `Langlands.Global.AdelicIntertwiningLeviRestriction` studies the Library's operator
`M(w, λ)φ = IsIwasawaCompact.intertwiningOperator hK hK' iU l iV c π' w φ λ` on the translates of
its argument by points of the target Levi subgroup `M'(𝔸)`.
Throughout, `p : P → G` and `q : Q → G` are parabolics with geometric unipotent radicals `iU`, `iV`
and rational Levi subgroups `l : M → P`, `l' : M' → Q`, `(w, c)` is a Weyl conjugation, and
`l' ≫ π' = 𝟙`. The integrals are over `(V(F) ∩ w U(𝔸) w⁻¹) \ V(𝔸)` with
`intertwiningMeasure`. Write `F₀(x, r) = φ(c(x) · w⁻¹ v_r g) m_P(w⁻¹ v_r g)^λ` for a Levi point
`x`, where `v_r = Quotient.out r` and `c(x)` stands for `p(l(c(x)))`.

## Results

- `parameterPower_neg`, `parameterPower_ne_zero`, `continuous_parameterPower_univ`,
  `map_comp_eq_map_map`: elementary facts on `parameterPower` and on point maps of composites.
- `IsIwasawaCompact.intertwiningOperator_levi_mul` (Bernstein–Lapid (6.5)): assuming
  `IntertwiningStabilizerModulusStatement`, for `x ∈ M'(𝔸)` and `g ∈ G(𝔸)`,
  `x^{-ρ_Q} · M(w, λ)φ(q(l'(x)) g) = c(x)^{-ρ_P} · m_Q(g)^{-wλ} · ∫ F₀(x, r) dr`.
- `IsIwasawaCompact.leviIntegrand_mk`: `F₀(x, ·)` can be evaluated at any representative of a
  class, because `φ` and `m_P^λ` are left invariant under `U(𝔸)` and `c(x)` normalizes `U(𝔸)`.
- `IsIwasawaCompact.continuous_leviIntegrand`: `(t, r) ↦ F₀(κ(t), r)` is jointly continuous for
  every continuous `κ : X → M'(𝔸)`. The map `id × mk : X × V(𝔸) → X × quotient` is an open
  quotient map, and the lifted function is continuous by the previous item.
- `IsIwasawaCompact.lintegral_leviIntegrand`: assuming
  `IntertwiningStabilizerModulusStatement`, `∫⁻ ‖F₀(x, ·)‖` is
  `‖(c(x)^λ · x^{ρ_Q} c(x)^{-ρ_P})⁻¹‖` times `∫⁻ ‖integrand of M(w, λ)φ at q(l'(x)) g‖`.
- `IsIwasawaCompact.integrable_leviIntegrand_prod`: assuming
  `IntertwiningStabilizerModulusStatement`, let `ϑ` be a continuous compactly supported weight on
  `M'(F_∞)`, let `ν` be an s-finite measure on `M'(F_∞)` that is finite on compact sets, and let
  `bd` be a real function on the quotient that is integrable for `intertwiningMeasure` and
  dominates the norm of the intertwining integrand at every point `q(l'(m)) g` with
  `m ∈ tsupport ϑ`. Then `(m, r) ↦ ϑ(m) F₀(m, r)` is integrable for `ν × intertwiningMeasure`.
  The integrability of `bd` is essential: a bounded majorant does not suffice, because the
  quotient can have infinite mass. For `GL₂` over `ℚ` with `P = Q` the upper Borel subgroup and
  `w` the nontrivial Weyl element, the quotient is the additive adeles, and for `φ = 1`, `λ = 0`
  the integrand is identically `1`.

## Proofs

Restriction formula. The Library theorem `IsIwasawaCompact.intertwiningOperator_normalized_levi`
(module `AdelicIntertwiningNormalizedLevi`) gives the formula under the hypothesis that the Haar
factor `intertwiningLeviHaarFactor` at `x`, multiplied by `c(x)^{ρ_P}`, equals `x^{ρ_Q}`. That
factor is `t = mulEquivHaarChar α / mulEquivHaarChar αH` for the conjugation `α` of `V(𝔸)` by
`q(l'(x))` and its restriction `αH` to the closed stabilizer. The hypothesis
`IntertwiningStabilizerModulusStatement` identifies `t = x^{ρ_Q} c(x)^{-ρ_P}`, so the required
identity follows from `c(x)^{-ρ_P} c(x)^{ρ_P} = 1`. The point `c(x)` of `P(𝔸)` is written as
`(c ≫ l)(x)` or as `l(c(x))` (`map_comp_eq_map_map`), and the constant `c(x)^{-ρ_P}` is moved out
of the integral.

Mass identity. The third conclusion of `intertwiningIntegralConjugation` (module
`AdelicIntertwiningClosedQuotient`), applied to `α`, compares the lower
integrals of the moved and the original integrands with the factor `t⁻¹`. Dividing by `‖c(x)^λ‖`
gives the identity.

Product integrability. The integrand is continuous, which gives measurability. By Tonelli
(`lintegral_prod`, which uses that `ν` and `intertwiningMeasure` are s-finite) and the mass
identity, its lower integral is at most `∫⁻ ‖ϑ(m) h₁(m)‖ dν · ∫⁻ ‖bd‖`, where
`h₁(m) = (c(m)^λ m^{ρ_Q} c(m)^{-ρ_P})⁻¹` is continuous. For `m` outside `tsupport ϑ` the inner
integral vanishes; for `m` in it the domination by `bd` bounds the mass identity's right-hand side.
The first factor is finite because `ϑ h₁` is continuous with compact support and `ν` is finite on
compact sets. The second factor is finite because `bd` is integrable for `intertwiningMeasure`.

## Sources and provenance

The restriction formula is Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), (6.5), p. 201, in the Library's normalization. The other
results are internal measure-theoretic tools for the uniform center ideal.
