# The twisted induced character formula from van Dijk's formula and local descent

Module `Langlands.BaseChange.TwistedInducedCharacterFormulaReduction`.

`TwistedInducedCharacterFormulaReductionStatement.{u, v, uW}` is the implication

`TwistedVanDijkStatement.{u, v, uW} → TwistedLocalDescentStatement.{u, v} →
TwistedInducedCharacterFormulaStatement.{u, v, uW}`,

and `twistedInducedCharacterFormulaReduction` proves it. The two premises are stated, without
proof, in `Langlands.BaseChange.TwistedVanDijkStatement` and
`Langlands.BaseChange.TwistedLocalDescentStatement`. This is the derivation of
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique
non nulle* (2011), II.4.5, formula (3) (printed p. 88), from formula (2), at the level of
local character values near one σ-regular point.

## Helper results

- `exists_isHaarMeasure_eq_one`: in a topological group with its Borel σ-algebra, a compact
  set with nonempty interior has mass one for the Haar measure `Measure.haarMeasure` normalized
  on it. `exists_isHaarMeasure_isProbabilityMeasure`: a compact group has a Haar probability
  measure.
- `hasLocalValue_twistedDistribution_of_eq_smul`: if `μ = r • μ₀`, a local value of the
  twisted distribution for `μ₀` is one for `μ`; both the integrated action and the Haar
  integral scale by `r`.
- `hasTwistedCharacterValue_of_hasLocalValue`: in a second countable, Hausdorff, locally
  compact, totally disconnected group, a local value of the twisted distribution for one Haar
  measure is a twisted character value (`HasTwistedCharacterValue`, which quantifies over all
  Haar measures). Every Haar measure is a multiple of the given one
  (`Measure.isMulLeftInvariant_eq_smul`).
- `leviTensorIntertwiner_comp`: the intertwining relation
  `(A₁ ⊗ ⋯ ⊗ A_r) ∘ (P₁ ⊗ ⋯ ⊗ P_r)(g) = (P₁ ⊗ ⋯ ⊗ P_r)(leviAut σ B g) ∘ (A₁ ⊗ ⋯ ⊗ A_r)` of
  `leviTensorIntertwiner σ B A`, in the form used by
  `Langlands.BaseChange.TwistedCharacter.Saturation`.

## Proof of the reduction

Take the data of the target. The groups `K = GL_n(𝒪_E)`, `M(𝒪_E)` and `U ∩ K` are compact and
open in `G`, `M = B.Levi E` and `U = B.unipotentSubgroup E` (the valuation ring of `E` is
compact and open, `GeneralLinearGroup.isCompact_integralSubgroup`,
`GeneralLinearGroup.isOpen_integralSubgroup`, and `U` is closed in `G`). This gives Haar
measures `μG`, `μM`, `μU` of volume one on them and the Haar probability measure `μK` on the
compact group `K`, the normalizations of the two premises.

1. For each `j`, the Levi value `b j` at `d j` and
   `HasTwistedCharacterValue.exists_saturation` give an open window `Ω j ∋ d j` such that the
   Levi twisted distribution (for `μM` and `A₁ ⊗ ⋯ ⊗ A_r`) equals `b j ∫ · dμM` on every test
   function supported in the `leviAut σ B`-twisted conjugacy saturation of `Ω j`.
2. `TwistedLocalDescentStatement`, applied to these windows, gives an open `U₀ ∋ δ`.
3. Let `φ` be supported in `U₀`, and let `ψ j` be the test functions it provides. Their sum
   `∑ j, ψ j` has the values of the twisted constant term, so `TwistedVanDijkStatement` gives
   `Θ^G(φ) = Θ^M(∑ j, ψ j) = ∑ j, Θ^M(ψ j)` by linearity.
4. By the choice of `Ω j`, `Θ^M(ψ j) = b j ∫ ψ j dμM = b j |D_{G/M,σ}(d j)|_F^{-1/2} ∫ φ dμG`.
   The blockwise cyclic norms of `d j` are the blocks of `m j`, so
   `cyclicNorm σ l (leviEmbedding (d j)) = baseChange (leviEmbedding (m j))`
   (`cyclicNorm_leviEmbedding`, `baseChange_leviEmbedding`), and
   `twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm` gives
   `D_{G/M,σ}(d j) = D_{G/M}(m j)`. Hence `Θ^M(ψ j) = relativeDiscriminantWeight B (m j) · b j ·
   ∫ φ dμG`.
5. Summing, `Θ^G(φ) = (∑ j, relativeDiscriminantWeight B (m j) * b j) ∫ φ dμG` for every `φ`
   supported in `U₀`: a local value for `μG`. Since `GL_n(E)` is second countable,
   `hasTwistedCharacterValue_of_hasLocalValue` turns it into the twisted character value of the
   target.

An empty Levi class system gives the empty sum, the value zero. The irreducibility
hypothesis of the target is not used.
