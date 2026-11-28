# Orbital integrals of cusp forms on `GL_n(F)` vanish off the elliptic set

The module `Langlands.BaseChange.CuspFormOrbitalVanishing` proves
`CuspFormOrbitalVanishingStatement` (module `Langlands.BaseChange.CuspFormOrbitalVanishingStatement`)
by the theorem

```lean
theorem cuspFormOrbitalVanishing : CuspFormOrbitalVanishingStatement.{u}
```

Let `F` be a nonarchimedean local field of characteristic zero and let `0 < n`. For every Haar
measure `μF` on `GL_n(F)` and every Schwartz–Bruhat function `f` on `GL_n(F)` with
`HasVanishingConstantTerms f`, the orbital integral `∫ f(x⁻¹ γ x) dνγ(x)` vanishes at every
regular semisimple `γ` that is not regular elliptic. This holds for every right Haar measure
`μγ` on the centralizer and every quotient measure `νγ` compatible with `μF` and `μγ`.

The proof uses neither the descent formula of Henniart–Lemaire II.4.5 (1) nor any
normalization of measures. It conjugates `γ` into a two-block Levi subgroup and applies the
general criterion `TraceFormula.twistedOrbitalIntegral_eq_zero_of_unipotent` (module
`Langlands.TraceFormula.UnipotentOrbitalVanishing`) with the unipotent radical of the
corresponding parabolic subgroup. The proof works for the measures given in the statement, so
no Haar uniqueness or rescaling is needed. It does not use the hypothesis `CharZero F`. Of the
local field structure it uses only that `F` is Hausdorff and that `GL_n(F)` is locally compact,
σ-compact and has a compact open subgroup.

## Steps

1. *A two-block Levi subgroup.* The Library's
   `exists_twoBlock_of_regularSemisimple_of_not_regularElliptic` (module
   `Langlands.BaseChange.RegularSemisimpleLevi`) gives `0 < k < n`, `g ∈ GL_n(F)` and `m` in the
   Levi subgroup of the two-block shape `B = ProductLeviChamber.twoBlock n k`, with
   `g⁻¹ γ g = δ := B.leviEmbedding F m`. The two blocks of `m` have coprime characteristic
   polynomials.
2. *Conjugation.* With `θ` the identity, the Library's `twistedOrbitalIntegral_map_conj` and
   `isCompatible_map_twistedConj` (module `Langlands.BaseChange.TwistedOrbitalConjugation`)
   identify the orbital integral at `γ` for `νγ` with the orbital integral at `δ` for the
   transported quotient measure. That measure is compatible with `μF` and with the image `μK`
   of `μγ` under conjugation (`twistedCentralizerConj`). The image `μK` is a Haar measure
   (Mathlib's `ContinuousMulEquiv.isHaarMeasure_map`) and is right-invariant
   (`isMulRightInvariant_map_continuousMulEquiv`, proved in this module).
3. *Vanishing at `δ`* (`orbitalIntegral_eq_zero_of_twoBlock`). The criterion of
   `UnipotentOrbitalVanishing` is applied with `U = B.unipotentSubgroup F` (closed:
   `isClosed_unipotentSubgroup`), a Haar measure `μU` on `U`, and a compact open subgroup of
   `GL_n(F)` (`LocalFieldTopology.generalLinear_compactOpen`). Its hypotheses are checked as
   follows.
   - *`H` normalizes `U`.* The centralizer of `δ` lies in the Levi subgroup
     (`glCentralizer_le_leviSubgroup`, module `Langlands.BaseChange.LeviNormDescent`), and the
     Levi subgroup normalizes `U` (`leviSubgroup_le_normalizer_unipotentSubgroup`, module
     `Langlands.Group.GL.OppositeBlocks`).
   - *Compactness of `H ∩ U C`* (`exists_isCompact_glCentralizer_mem_unipotent_mul`). Let
     `t = u c` with `t` in the centralizer, `u ∈ U` and `c ∈ C`. Then `t` is block diagonal,
     `c = u⁻¹ t` lies in the parabolic subgroup `P`, and `t` is the Levi part of `c`: its image
     under the Library's continuous Levi projection `leviProjection` followed by
     `leviEmbedding`. So `t` lies in the image of the compact set `C ∩ P` (`P` is closed:
     `isClosed_parabolic`).
   - *Properness of `u ↦ u⁻¹ δ u`* (`exists_isCompact_unipotent_conj_mem`). We have
     `u⁻¹ δ u = δ Ψ(u)` with `Ψ(u) = δ⁻¹ u⁻¹ δ u`. By `BlockShape.twistContinuousMulEquiv`
     (module `Langlands.Group.GL.TwoBlockUnipotent`), `Ψ` is a topological group automorphism
     of `U`, so `u ∈ Ψ⁻¹(U ∩ δ⁻¹ C)`, which is compact.
   - *Integrals along `U`* (`integral_unipotent_conj_eq_zero`). For every `x`,
     `∫_U f(x⁻¹ u⁻¹ δ u x) dμU(u) = ∫_U f(x⁻¹ δ Ψ(u) x) dμU(u) = ∫_U f(x⁻¹ δ v x) d(Ψ_* μU)(v)`
     (Mathlib's `integral_map_equiv`). The image `Ψ_* μU` is a Haar measure on `U`. The last
     integral is `0` by `HasVanishingConstantTerms f`, applied to the two-block shape (which has
     two blocks), this Haar measure, and the elements `x⁻¹ δ` and `x`.
   - The Schwartz–Bruhat function `f` is continuous with compact support
     (`SchwartzBruhat.continuous`, `SchwartzBruhat.hasCompactSupport`).

## Inputs

- Library: `exists_twoBlock_of_regularSemisimple_of_not_regularElliptic`
  (`Langlands.BaseChange.RegularSemisimpleLevi`); `glCentralizer_le_leviSubgroup`
  (`Langlands.BaseChange.LeviNormDescent`); `leviSubgroup_le_normalizer_unipotentSubgroup`
  (`Langlands.Group.GL.OppositeBlocks`); `twistedOrbitalIntegral_map_conj`,
  `isCompatible_map_twistedConj`, `twistedCentralizerConj`
  (`Langlands.BaseChange.TwistedOrbitalConjugation`); the block-shape API of
  `Langlands.Group.GL.Blocks` (`mem_unipotentSubgroup_iff`, `leviProjection`,
  `leviInParabolic`, `leviProjection_section`, `leviEmbeddingContinuous`,
  `leviProjectionContinuous`, `isClosed_parabolic`, `isClosed_unipotentSubgroup`);
  `ProductLeviChamber.twoBlock` (`Langlands.Group.GL.TwoBlockShape`); the topological facts
  `LocalFieldTopology.t2Space`, `generalLinear_t2Space`, `generalLinear_locallyCompactSpace`,
  `generalLinear_totallyDisconnectedSpace`, `generalLinear_sigmaCompactSpace`,
  `generalLinear_compactOpen` (`Langlands.Group.GL.LocalFieldTopology`).
- Modules proved alongside: `Langlands.TraceFormula.UnipotentOrbitalVanishing` (the vanishing
  criterion) and `Langlands.Group.GL.TwoBlockUnipotent` (the automorphism `Ψ`).
- Mathlib: `ContinuousMulEquiv.isHaarMeasure_map`, `integral_map_equiv`, `Measure.haar`.

## Sources

Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en caractéristique
non nulle*, Mém. SMF 124 (2011), II.4.5, printed pp. 86–88 (PDF page = printed page + 8). There
the ordinary case `E = F`, `σ = id` of the descent formula (1) (p. 88, after formula (3))
expresses the orbital integral at an element of a Levi subgroup through the constant term,
which vanishes for a function with vanishing constant terms. This module does not use the
descent formula. It uses only the integrals along the unipotent radical over the orbit, through
the criterion of `UnipotentOrbitalVanishing`. II.4.10
(printed p. 93) defines elliptic functions, whose orbital integrals vanish off the elliptic set.
