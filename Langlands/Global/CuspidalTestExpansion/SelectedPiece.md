# The selected Bruhat piece is the constant term of the selected intertwining integral

Module `Langlands.Global.CuspidalTestExpansion.SelectedPiece`
(namespace `Langlands.Global.StandardParabolicFamily`).

## Statement

`selectedPiece_constantTerm`: let `pc : StandardBruhatPiece fam I J I₁ J₁ n'` and
`pcQ : StandardBruhatPiece fam I Q I₂ Q₂ n` be Bruhat pieces with `n = n'`, `J = J₁`, `I = I₂`,
`Q = Q₂` and `J ≤ Q`. Assume `GeometricLemmaUnfoldingStatement`, Iwasawa subgroups `K` for
`P_I` and for the sources of both pieces, `0 < N`, `φ` continuous and left invariant under
`U_I(𝔸) M_I(F)`, and a summable nonnegative majorant `‖φ_λ(γ_c g)‖ ≤ b c · H(g)^d` (`d ≥ 0`)
of the Eisenstein terms over `P_I(F) \ G(F)`.
Then for every `y`

`C_J(M(n)φ)(y) = Pint(y)`,

where `M(n)φ = hK.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n φ λ` is the
intertwining integral over `(U_Q(F) ∩ n U_I(𝔸) n⁻¹) \ U_Q(𝔸)` (Bernstein–Lapid's
`[M(w, λ)φ]_{wλ}` for `w = [n]`), `C_J` is the constant term along `U_J`, and `Pint` is the
integral of the piece `pc` (over `(U_J(F) ∩ n U_{I₁}(𝔸) n⁻¹) \ U_J(𝔸)` of
`(C_{I₁} φ)_{λ|}(n⁻¹ v y)`). Since `pc` has full target (`J₁ = J`), the series of translates of
`Pint` over `P_{J₁}(F) \ P_J(F)` has the single term `Pint` (`fullPiece_series`). In words: the
constant term of `M(n)φ` along `P_J ⊆ P_Q` is the term indexed by `n` of the constant term
formula (Bernstein–Lapid, *Meromorphic continuation of Eisenstein series* (2024), (6.17)) along
`P_J`.
It identifies that term with the subtracted term in the scalar form of (6.20)
(`ConvergentCuspidalTestExpansionStatement`).

## Proof

After `subst`, put `Φ = φ_λ` and `w = n`.

1. `M(n)φ = stabilizerIntegral (fam.p I) (fam.p Q) (fam.iU Q) w Φ`: `pieceIntegral_properties`
   for `pcQ` gives this for the integral of `pcQ`, whose source is `P_I` itself. There
   `C_{U_I} φ = φ`, since `φ` is left `U_I(𝔸)`-invariant and the normalized measure on
   `U_I(F) \ U_I(𝔸)` is a probability measure; the integral of `pcQ` is then `M(n)φ`
   (`intertwiningIntegral_eq_of_range_eq_of_twist`, `parameterTwist_restrict_of_comp_eq`).
2. `Pint = stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) w Φ` by `pieceIntegral_properties`
   for `pc`.
3. `U_J(F) ⊆ (U_J(F) ∩ wP_I(F)w⁻¹) U_Q(F)`: a rational point `δ` of `U_J` lies in `P_Q(F)`, and
   `pcQ.geometry.rationalImage_right` (with `Q₂ = Q`) gives
   `P_Q(F) = (P_Q(F) ∩ wP_I(F)w⁻¹) U_Q(F)`; write `δ = a v` (`exists_mul_of_mem_sup`). Then
   `v ∈ U_Q(F) ⊆ U_J(F)`, so `a = δ v⁻¹ ∈ U_J(F) ∩ wP_I(F)w⁻¹`.
4. `subgroupConstantTerm_stabilizerIntegral_of_le` with `U_Q ≤ U_J` (`radical_le_of_le`),
   `U_Q` normalized by `U_J` (`radical_isNormalizedBy_of_le`), compact rational quotients
   (`compactSpace_radicalRationalQuotient`), `w` rational (`innerAdelicPoint_eq_rational`) and
   the integrability of both stabilizer integrands (`eisensteinUnfoldingGlobalMajorant`,
   `eisensteinStabilizerContinuity`) concludes.
