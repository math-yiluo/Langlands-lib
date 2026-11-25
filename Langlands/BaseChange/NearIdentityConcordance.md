# Matching through a descent subgroup

`Langlands.BaseChange.NearIdentityConcordance`. Namespace `Langlands.BaseChange`.

The core of the matching of test functions near the identity for cyclic base change: a criterion
for concordance (`AreConcordant`) of two test functions supported near `1`, by an equality of their
averages over a compact open subgroup.

## Statements

The facts on regular semisimple elements used here,
`Langlands.JacquetLanglands.IsRegularSemisimple.baseChange` and `isRegularSemisimple_conj_iff`,
are in `Langlands.BaseChange.Norm`.

- `ConcordAt.of_twistedConj (hσ : σ ^ l = 1) (t) (h : ConcordAt σ l μF μE φ f
  (twistedConj (entrywiseAut σ n) t δ) γ) : ConcordAt σ l μF μE φ f δ γ` (`μE` left invariant).
- `twistedOrbitalIntegral_eq_zero_of_forall θ δ ν (hf : ∀ x, f (x⁻¹ * δ * θ x) = 0)`:
  `twistedOrbitalIntegral θ δ ν f = 0`.
- `areConcordant_of_integral_eq`. Hypotheses: `F` a nonarchimedean local field
  (`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`), `E` a field
  with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`,
  `σ : E ≃ₐ[F] E` with `IsCyclicAlgebra σ l`; Borel σ-algebras on `GL_n(F)`, `GL_n(E)` and Haar
  measures `μF`, `μE`; `K : Subgroup (GeneralLinear n E)` open, compact, with
  `IsTwistedDescentSubgroup F σ l K`; `φ : SchwartzBruhat (GeneralLinear n E)`,
  `f : SchwartzBruhat (GeneralLinear n F)` with
  - `∀ g, φ g ≠ 0 → ∃ κ ∈ K, ∃ u, baseChange F E n u ∈ K ∧ g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ`,
  - `∀ γ, f γ ≠ 0 → ∃ u, baseChange F E n u ∈ K ∧ γ = u ^ l`,
  - `∀ u, baseChange F E n u ∈ K →
    ∫ κ in K.comap (baseChange F E n), f (κ⁻¹ * u ^ l * κ) ∂μF =
    ∫ κ in K, φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) ∂μE`.

  Conclusion: `AreConcordant σ l μF μE φ f`.

## Proof

- *Vanishing off norms.* If `f (y⁻¹ γ y) ≠ 0` then `y⁻¹ γ y = u^l`, the norm of `baseChange u`
  (`isNorm_pow`), so `γ` is a norm (`isNorm_conj_iff`); the orbit function vanishes.
- *Concordance at `(δ, γ)`*, `γ` regular semisimple and associated with `δ`.
  - If `γ` is not conjugate to some `u^l`, `u ∈ K ∩ GL_n(F)`, both orbit functions vanish: for `f`
    by its support; for `φ`, `φ(g⁻¹ δ g^σ) ≠ 0` gives `g⁻¹ δ g^σ = κ⁻¹ u κ^σ`, taking norms
    `δ` is associated with `u^l`, and part (1b) of the norm lemma (`cyclicNormLemma`) makes `γ`
    conjugate to `u^l`.
  - Otherwise `γ = y u^l y⁻¹`; by `concordAt_of_conj_of_cyclicNorm_eq` it suffices to treat
    `γ = u^l` and `δ'` with `N(δ') = u^l`; by part (2) of the norm lemma `δ'` is σ-conjugate to
    `baseChange u`, and `ConcordAt.of_twistedConj` reduces to `δ = baseChange u`.
  - At `δ = baseChange u`: the association of measures is through the identity
    (`normConjugator_on_sigmaCentralizer`, with the commutativity of the centralizer
    `commute_of_commute_baseChange`); the σ-centralizer of `baseChange u` is the image of the
    centralizer of `u^l` (`IsTwistedDescentSubgroup.sigmaCentralizer_eq`); the orbit function of `φ`
    is supported in `GL_n(F) · K` (rigidity of σ-conjugacy) and has compact support modulo the
    centralizer (`continuous_hasCompactSupport_cyclicTwistedOrbitFunction`). Then
    `IsCompatible.integral_descend_eq_of_compactOpen` applies on both sides (with `j = baseChange`
    on `GL_n(E)` and `j = id`, `K ∩ GL_n(F)` on `GL_n(F)`), with the same factor
    `μF(K ∩ GL_n(F))⁻¹`, and the two averages agree pointwise: for `w = h⁻¹ u h ∈ K` by hypothesis,
    and otherwise both vanish (σ-stability of `K` on the `φ` side; the descent of `l`-th roots on the
    `f` side).

## Declarations, in order

`ConcordAt.of_twistedConj`,
`twistedOrbitalIntegral_eq_zero_of_forall`; private `concordAt_baseChange`;
`areConcordant_of_integral_eq`.

## Literature

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.5, p. 17: the definition of associated
  measures and of concordant functions (`ConcordAt`, `AreConcordant`); §I.2.2, pp. 11–12: the norm
  lemma used for the reductions.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), Chapter 1, §3: Proposition 3.1, p. 20, and the proof of Lemma 3.4, pp. 22–25,
  for `δ₀ = 1` (then the σ-centralizer `M` of `δ₀` is `G(F)` and no descent to `M` is needed).

## Source and licence

Port of `UpperTheory.ConvolutionTheory.Loc.nearCore` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>)
at commit `f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`, file
`src/Development/AutomorphicArithmetic/Foundations/Convolution/TwistedLocalOrbits/NearCore.lean`
lines 27–29, 56–84 and 145–294 (with the matching part of `NearDown.lean`, lines 278–364, which
repeats it). The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- The conclusion `Match σ μE μk φ f` (integrals against chosen normalizing functions) is replaced by
  the Library's `AreConcordant σ l μF μE φ f` (integrals against compatible quotient measures, for
  every pair of associated right Haar measures).
- The ball `ball n r` with `r` below the valuation of `[E : k]` is replaced by any compact open
  `K` with `IsTwistedDescentSubgroup F σ l K`; the radius enters only in proving that the spectral
  congruence subgroups are such (`isTwistedDescentSubgroup_normCongruence`).
- The source's Galois hypotheses become `IsCyclicAlgebra σ l` with `E` a field; `normInj` and
  `conjDesc` become parts (2) and (1b) of the Library's `cyclicNormLemma`; `twOrbConj`, `haarConj`
  and the transport of measures are the Library's `ConcordAt.of_twistedConj` (new, built on
  `twistedOrbitalIntegral_twistedQuotientConj`) and `concordAt_of_conj_of_cyclicNorm_eq`;
  `haarComm` (inversion invariance on the centralizer) is not needed; `orbProper` is the Library's
  `continuous_hasCompactSupport_cyclicTwistedOrbitFunction` and
  `hasCompactSupport_regularSemisimpleOrbitFunction`.
- `quotDesc` is `IsCompatible.integral_descend_eq_of_compactOpen`.
