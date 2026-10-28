# Same-model scalar Fourier cutoff for the early JPSS Lemma 5.5: proof

Author: Worker 875.

The closing theorem `Langlands.RankinSelberg.rankOneExtensionScalarCutoff.{uF,uV}`
proves exactly the published closed proposition
[`RankOneExtensionScalarCutoffStatement.{uF,uV}`](RankOneExtensionScalarCutoffStatement.md).
It has no binders and no extra hypotheses. The two universes stay independent.
The statement pair and the modules it imports are not changed. The theorem uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Write `T := F.canonicalTopologicalData` and `π_T := T.uniformizer`. As in the
statement, write `B(m,x,a)` for `rankOneExtensionEmbeddedLowerBlock t k m x a`
and `S(u)` for `rankOneExtensionSmearingUnipotent t k u`.

## Published inputs used by name

- `Langlands.RankinSelberg.Smearing.exists_coefficient_average`
  (module `UnequalRankSmearingAverage`, by Workers 180 and 582). It is called
  directly and none of its code is adapted. It produces one coefficient `f₁`
  in the same `coefficientModel π ℓ`, with integrability and the averaging
  formula at every group element.
- `Langlands.HarmonicAnalysis.scalarFourierClosure`. Its second conjunct shows
  that the plus-sign Fourier transform of a Schwartz–Bruhat function is again
  Schwartz–Bruhat. The self-duality identity `ν.property` is used together
  with it.
- The principal-unit API of `Langlands.HarmonicAnalysis.Conductor`:
  `principalUnits`, `principalUnits_antitone`,
  `mem_principalUnits_iff_div_mem_integers`, `exists_principalUnits_subset`
  and `exists_multiplicativeTrivialAt`. The last one says that every continuous
  quasicharacter is trivial on some principal-unit subgroup.
- `T.valuationShell_compact_closed`, `T.normalizedAbs_eq_one_iff_discreteValuation`,
  `T.fieldT2` and the first conjunct of `padicLatticeGeometry`, which gives
  total disconnectedness.
- `Hecke.TestFunction.characteristic` and `Hecke.TestFunction.pullback`.
- `Langlands.Whittaker.modelMap_surjective`,
  `Langlands.Whittaker.standardCharacter_apply`, and the continuity
  certificates `GeneralLinear.rankInclusionContinuous` and
  `GeneralLinear.reindexContinuous`.

## Internal helpers (namespace `ScalarCutoffProof`)

These are internal lemmas about the concrete matrices. They are derived here
and are not stated in the source.

- `scalarBlockHom t` is the monoid homomorphism `a ↦ [I, 0; 0, a]` into the
  cell-coordinate matrices. `scalarDiagonal t k a` is the scalar diagonal
  `D(a)`. It is the image of the unit `[I, 0; 0, a]` under the published
  reindexing by `rankOneExtensionCellCoordinates t`, followed by the published
  rank inclusion with trailing rank `k + 1`. So `D(a)` has `a` at the scalar
  coordinate `t + 1` and `1` elsewhere on the diagonal. `scalarDiagonal_one`
  says `D(1) = 1`.
- `lowerBlock_eq_mul` and `embeddedLowerBlock_eq_mul` give the factorization
  `B(m,x,a) = B(m,x,1) * D(a)`. It follows from block multiplication,
  `[m, 0; x, 1] [I, 0; 0, a] = [m, 0; x, a]`, and from the fact that
  reindexing and rank inclusion are group homomorphisms.
- `embeddedLowerBlock_trailing_row` says that the first trailing row of
  `B(m,x,a)` is the standard basis row. `embeddedLowerBlock_scalar_column` says
  that the scalar column is `a` times the standard basis column. Both are
  computed with the published `blockSum` and `rankOneExtensionLowerBlock_apply`
  lemmas.
- `embeddedLowerBlock_mul_smearing` proves
  `B(m,x,a) * S(u) = S(a * u) * B(m,x,a)`. Since `S(c)` is the transvection
  `I + c E_(s,f)`, where `s` is the scalar index and `f` the first trailing
  index, the two sides are compared entrywise with Mathlib's
  `mul_transvection_apply_*` and `transvection_mul_apply_*` lemmas, using the
  row and column lemmas above.
- `smearing_mem_upperUnipotent` shows `S(c) ∈ upperUnipotent`.
  `standardCharacter_smearing` shows that the standard character takes the
  value `ψ(c)` at `S(c)`. In the sum `∑ i, g (i.castSucc) (i.succ)` only the
  superdiagonal entry at `i = t + 1` is nonzero, and that entry equals `c`.
- `cutoffSet T n` is the set
  `{x | T.discreteValuation x = 1 ∧ (x - 1) / π_T ^ n ∈ T.Integers}`.
  `mem_cutoffSet_iff` says that a unit lies in it exactly when it lies in
  `T.principalUnits n`. `cutoffSet_isOpen` proves that the set is open: the
  valuation-one sphere is open by Mathlib's `Valuation.isOpen_sphere`, after
  transport through the order isomorphism of the value group with `ℤᵐ⁰`, and
  the integers are open. `cutoffSet_isCompact_isClosed` proves that the set
  is closed and is contained in the compact shell `T.valuationShell 0`.
  `one_mem_cutoffSet`, `zero_not_mem_cutoffSet` and
  `exists_unit_of_mem_cutoffSet` give the remaining membership facts.

## Implemented proof of the main theorem

The proof installs the statement's topology, valuative relation, local-field
certificate and Borel structure with `let` and `have`. It adds the Prop-valued
instances `T2Space F.Carrier` and `TotallyDisconnectedSpace F.Carrier` that
`scalarFourierClosure` needs. These are proofs of Prop-valued classes, so they
do not change any data in the statement.

1. **A carrier vector and an open subgroup.** By `modelMap_surjective`,
   `f₂ = modelMap π ℓ v` for some `v`. Smoothness of `π` gives an open
   subgroup `K` that fixes `v`.
2. **Continuity.** `D` is continuous as a map from `F.Carrierˣ`, by
   `Units.continuous_iff` and Mathlib's `Continuous.matrix_fromBlocks`, then
   composition with the published reindexing and rank-inclusion continuous
   homomorphisms. `S` is continuous because each entry is a constant plus
   either `u` or `0`, and `S(u)⁻¹ = S(-u)`.
3. **The level.** `exists_multiplicativeTrivialAt` gives `n₀` such that `χ` is
   trivial on `principalUnits n₀`. The set `{a | D(a) ∈ K}` is a neighborhood
   of `1` in `F.Carrierˣ`, since `D(1) = 1`. So is `Units.val ⁻¹' O`. Then
   `exists_principalUnits_subset` gives `n₁` and `n₂` for these two sets. With
   `n := n₀ + n₁ + n₂`, antitonicity places `principalUnits n` inside all
   three sets.
4. **The cutoff.** `U := cutoffSet T n`. It is compact and open, contains `1`
   and not `0`. Every `y ∈ U` is a unit in `principalUnits n`, so `U ⊆ O`.
   Every `y ∈ U` has discrete valuation `1`, so its normalized absolute value
   is `1`. Every unit `a ∈ U` satisfies `χ(a) = 1` and `D(a) ∈ K`.
5. **The Schwartz–Bruhat pair.** `Φ` is the characteristic function of the
   compact clopen set `U`. Hence `Φ 0 = 0`, `Φ a = 1 = χ(a)⁻¹` for units
   `a ∈ U`, and `Φ a = 0` for units outside `U`. Let
   `Φneg := Φ ∘ (x ↦ -x)`, by `Hecke.TestFunction.pullback` along negation.
   Scalar Fourier closure gives a Schwartz–Bruhat `κ` with
   `κ = fourierTransform ψ ν.val Φneg` pointwise. Self-duality of `ν.val`
   gives, for every `b`,
   `fourierIntegral ψ ν.val κ b = Φneg(-b) = Φ b`.
   This is conclusion 3, with the plus sign
   `fourierIntegral ψ μ κ b = ∫ x, ψ(x * b) κ(x) dμ`.
6. **The smeared coefficient.** `exists_coefficient_average` with
   `μ = ν.val.measure`, the continuous map `S` and the weight `κ` gives `f₁` in
   the same coefficient model, together with conclusion 4 at every `h`.
7. **Conclusion 5.** By `embeddedLowerBlock_mul_smearing`, Whittaker
   covariance of `f₂` and `standardCharacter_smearing`,
   `κ(u) f₂(B(m,x,a) S(u)) = ψ(u * a) κ(u) f₂(B(m,x,a))`.
   Integrating and using `integral_mul_const` gives
   `f₁(B(m,x,a)) = fourierIntegral ψ ν.val κ a * f₂(B(m,x,a)) = Φ(a) f₂(B(m,x,a))`.
8. **Conclusion 6.** For a unit `a ∈ U`,
   `f₂(B(m,x,a)) = ℓ(π(B(m,x,1) D(a)) v) = ℓ(π(B(m,x,1)) v) = f₂(B(m,x,1))`,
   because `D(a) ∈ K` fixes `v`. This holds uniformly in `m` and `x`.
9. **Conclusion 7.** On `U`, conclusions 5 and 6 and `Φ a = χ(a)⁻¹` give
   `f₁(B(m,x,a)) = χ(a)⁻¹ f₂(B(m,x,1))`. Off `U`, conclusion 5 and `Φ a = 0`
   give `f₁(B(m,x,a)) = 0`.

## Relation to the source

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
as `jpss-1983-rankin-selberg`. The proof of Lemma (5.5) is on printed pages
426–427 (PDF pages 61–62), which were rendered and read for this proof. No
erratum was found for these pages.

The source takes `φ₁ ∈ 𝒮(F)` with `φ̂₁(a) = σ₂⁻¹(a)` if `|a - 1| < ε` and `0`
otherwise. It sets `W(g) = ∫ φ₁(u) W₂(g S(u)) du`, and the display at the top
of page 427 gives `W(B(m,x,a)) = W₂(B(m,x,a)) φ̂₁(a)`. In the Lean proof `κ` is
`φ₁`, `Φ` is `φ̂₁`, `f₂` is `W₂` and `f₁` is `W`. The neighborhood
`|a - 1| < ε` becomes the principal-unit set `U` from step 4, which lies inside
the given `O`. For `ε ≤ 1` the source's disc is also a set of this form.

**Fourier sign.** The source derives
`W₂(B(m,x,a) S(u)) = ψ(a u) W₂(B(m,x,a))`, so its `φ̂₁` is the transform
`∫ φ₁(u) ψ(a u) du` with the plus sign. That is the published
`fourierIntegral`. Step 7 proves the same covariance with `ψ(u * a)`. The proof
therefore needs a `κ` whose plus-sign transform is `Φ`. Self-duality inverts
the plus-sign transform only up to the reflection `x ↦ -x`, so step 5 applies
the transform to `Φneg` rather than to `Φ`.

**`B(1)` versus `B(a)`.** Both printed formula (9) on page 426 and the display
at the top of page 427 keep `a` inside `W₂(B(m,x,a))`. Conclusions 6 and 7
replace it by `W₂(B(m,x,1))`. This is the statement's derived uniform
smoothness refinement, not a transcription of (9). The source uses it only
implicitly, when it passes from (8) and (9) to
`Ψ(s, W, W_f; 0) = Ψ(s, W₂, W₁; 1)`. The proof obtains the refinement by
shrinking `U` for the given `f₂` (step 3, set `{a | D(a) ∈ K}`), using the
factorization `B(m,x,a) = B(m,x,1) D(a)` (step 8). An arbitrary preassigned
neighborhood would not do. The choice depends on `f₂`, `χ` and `O`, as the
statement allows.

The proof uses no Jacquet functional, quotient measure, multiplicative Haar
normalization, zeta integral, Laurent span or later L-multiplicativity
result.
