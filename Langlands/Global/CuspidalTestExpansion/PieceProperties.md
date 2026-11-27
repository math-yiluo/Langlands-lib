# Continuity, bounds and invariance of the integral of a Bruhat piece

Module `Langlands.Global.CuspidalTestExpansion.PieceProperties`
(namespace `Langlands.Global.StandardParabolicFamily`).

A Bruhat piece `pc : StandardBruhatPiece fam I J I₁ J₁ n` consists of the parabolics
`P_{I₁} ⊆ P_I` (`pc.source`) and `P_{J₁} ⊆ P_J` (`pc.target`) of the geometric lemma for the
rational point `n` (`pc.geometry : IsGeometricLemmaDatum`). Its integral is the intertwining
integral

`Pint(y) = ∫_{(U_{J₁}(F) ∩ n U_{I₁}(𝔸) n⁻¹) \ U_{J₁}(𝔸)} (C_{I₁} φ)_{λ|}(n⁻¹ v y) dv`.

It is not itself the term indexed by `n` in the constant term formula
`EisensteinConstantTermStatement` (Bernstein–Lapid, *Meromorphic continuation of Eisenstein
series* (2024), (6.17)): that term is the series of its translates over the target rational
cosets,

`S_n(y) = ∑_{γ ∈ P_{J₁}(F) \ P_J(F)} Pint(γ y)`.

For a full target (`J₁ = J`) the series has a single term and `S_n = Pint`
(`fullPiece_series`, module `Langlands.Global.CuspidalTestExpansion.FullPiece`).

## Declarations

- Instances `instClosedSourcePiece`, `instClosedSourceRadicalPiece`,
  `instClosedTargetRadicalPiece`: the composites `pc.source.inclusion ≫ fam.p I`,
  `fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I` and `fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J`
  are closed immersions (they equal `fam.p I₁`, resp. the radical embeddings).
- `parameterTwist_isLeftInvariant`: for `φ` left invariant under
  `parabolicQuotientSubgroup` (`U_I(𝔸) M_I(F)`), the twist `φ_λ` is left invariant under `U_I(𝔸)`
  and under `P_I(F)`.
- `pieceIntegral_properties`: assume `GeometricLemmaUnfoldingStatement`, `φ` continuous and left
  `U_I(𝔸) M_I(F)`-invariant, `0 < N`, and a summable nonnegative majorant
  `‖φ_λ(γ_c g)‖ ≤ b c · H(g)^d` (`d ≥ 0`) of the Eisenstein terms over `P_I(F) \ G(F)` (as
  supplied by `eisensteinGlobalMajorant`). Then (1) the integrand of `Pint` is integrable at every argument;
  (2) `Pint = stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) n φ_λ`; (3) `Pint` is continuous;
  (4) `‖Pint y‖ ≤ C · H(y)^d` for some `C ≥ 0`; (5) `Pint` is left invariant under `P_{J₁}(F)`.
- `pieceIntegral_radical_invariant`: if the constant term `C_{I₁} φ` is left invariant under
  `U_{I₁}(𝔸)`, then `Pint` is left invariant under `U_{J₁}(𝔸)`.

## Proofs

`pieceIntegral_properties`: `eisensteinUnfoldingGlobalMajorant` gives an integrable majorant `B`
of the stabilizer integrand with the weight `H(g)^d`; `eisensteinStabilizerContinuity` then gives
integrability and continuity of the stabilizer integral. `bruhatIntertwiningIdentification`
(which uses `GeometricLemmaUnfoldingStatement` and the datum `pc.geometry`) gives (1) and (2).
(3) and (4) follow from (2), the bound by `∫ B` coming from `norm_integral_le_of_norm_le`. (5)
is `stabilizerIntegral_isLeftInvariantUnder` together with
`pc.geometry.rationalImage_right`, which identifies `(P_J(F) ∩ nP_I(F)n⁻¹) U_J(F)` with
`P_{J₁}(F)`.

`pieceIntegral_radical_invariant` is `IsIwasawaCompact.intertwiningIntegral_adelicPoints_mul`,
after replacing the radical of `pc.source.inclusion ≫ fam.p I` by that of `fam.p I₁`
(`subgroupConstantTerm_eq_of_range_eq`).
