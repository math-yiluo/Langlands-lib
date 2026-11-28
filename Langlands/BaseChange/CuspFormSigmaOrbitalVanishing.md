# σ-orbital integrals of cusp forms vanish off the σ-elliptic set

The module `Langlands.BaseChange.CuspFormSigmaOrbitalVanishing` proves
`CuspFormSigmaOrbitalVanishingStatement.{u, v}` (module
`Langlands.BaseChange.CuspFormOrbitalVanishingStatement`) by the theorem
`cuspFormSigmaOrbitalVanishing`, at both universe parameters.

## Statement

For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of degree `l` with generator `σ` and its module topology, and `0 < n`: for every Haar
measure `μE` on `GL_n(E)` and every Schwartz–Bruhat function `φ` on `GL_n(E)` with
`HasVanishingConstantTerms φ`, `SigmaOrbitalIntegralsVanishOffElliptic σ l μE φ` holds: the
σ-orbital integral `∫ φ(x⁻¹ δ x^σ) dνδ(x)` is `0` at every σ-regular `δ` that is not σ-elliptic,
for every right Haar measure `μδ` on the σ-centralizer and every quotient measure `νδ` compatible
with `μE` and `μδ`.

## Proof

The proof does not use the descent formula of Henniart–Lemaire II.4.5 (1). It moves `δ` into a
two-block Levi subgroup and integrates only along the unipotent radical. Write
`θ = (entrywiseAut σ n).toMonoidHom`; `sigmaOrbitalIntegral σ n δ` is
`twistedOrbitalIntegral θ δ`.

1. *Topology.* `GL_n(E)` is Hausdorff, locally compact and second countable
   (`generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite`,
   `generalLinear_secondCountableTopology_of_finite`), `E` is Hausdorff
   (`finiteAlgebra_t2Space`), and `θ` is continuous (`continuous_entrywiseAut_of_isModuleTopology`).
   `σ ^ l = 1` by `IsCyclicAlgebra.pow_eq_one`.
2. *A two-block Levi.* `δ` is associated with a regular semisimple `γ ∈ GL_n(F)`, which is not
   regular elliptic since `δ` is not σ-elliptic. By
   `exists_twoBlock_of_regularSemisimple_of_not_regularElliptic` (module
   `Langlands.BaseChange.RegularSemisimpleLevi`) there are `0 < k < n`, `g ∈ GL_n(F)` and `m` in
   the Levi of `B = twoBlock n k` with `g⁻¹ γ g = leviEmbedding m`. Then `δ` is associated with
   `leviEmbedding m` (`IsNormAssociated.twistedConj`), which is regular semisimple
   (`isRegularSemisimple_conj_iff`).
3. *A σ-conjugate in `M(E)`.* `regularLeviNormRepresentative` (module
   `Langlands.BaseChange.RegularLeviNormRepresentative`) gives `x ∈ GL_n(E)` and `d` with
   `δ' = x⁻¹ δ θ(x) = leviEmbedding d` and `N(d_i) = m_i` blockwise. Hence
   `N(δ') = leviEmbedding m` (`cyclicNorm_leviEmbedding`, `baseChange_leviEmbedding`), and
   `sigmaCentralizer_le_leviSubgroup_of_regularNorm` gives that the σ-centralizer of `δ'` lies in
   the block diagonal subgroup `M(E)`.
4. *Transport to `δ'`.* Push `μδ` forward along `twistedCentralizerConj θ δ x`; the image is a
   right-invariant Haar measure (`ContinuousMulEquiv.isHaarMeasure_map`,
   `isMulRightInvariant_map`). `isCompatible_map_twistedConj` makes the image of `νδ` under
   `twistedOrbitQuotientConj θ δ x` compatible with `μE` and that measure, and
   `twistedOrbitalIntegral_map_conj` (module `Langlands.BaseChange.TwistedOrbitalConjugation`)
   says the σ-orbital integral at `δ` with `νδ` equals the one at `δ'` with the transported
   quotient measure.
5. *Vanishing at `δ'`.* `leviTwistedFibreData B σ δ'` (module
   `Langlands.BaseChange.LeviTwistedFibre`; `B` has two blocks) is a `TwistedFibreData` with fibre
   the unipotent radical `B.unipotentSubgroup E`, and its twisted conjugation is surjective
   (`leviTwistedFibreData_twist_surjective`, using that `E` is a finite `F`-module). The function
   `φ` is continuous (`SchwartzBruhat.continuous`), and since `B` has two blocks,
   `HasVanishingConstantTerms φ` gives `∫_U φ(y u z) dμ(u) = 0` for every Haar measure `μ` on the
   radical and all `y, z`. `TwistedFibreData.twistedOrbitalIntegral_eq_zero` (module
   `Langlands.TraceFormula.TwistedOrbitalFibreVanishing`) gives that the σ-orbital integral at `δ'`
   is `0`, for any Haar measure on `GL_n(E)`, right Haar measure on the σ-centralizer and
   compatible quotient measure. No Haar measure is normalized and no scaling argument is needed.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en caractéristique
  non nulle*, Mém. SMF 124 (2011): II.4.5 formula (1), printed pp. 86–88 (descent of σ-orbital
  integrals to a Levi subgroup, from which the vanishing for functions with vanishing constant
  terms follows), and II.5.14, Proposition 2 (2) and its proof, printed pp. 115–116 (the
  reduction of a σ-regular, non-σ-elliptic `δ` to a proper Levi subgroup). The statement's
  Markdown records the route through the descent formula; the proof here replaces the descent
  formula by the fibre argument of `TwistedFibreData.twistedOrbitalIntegral_eq_zero`.
