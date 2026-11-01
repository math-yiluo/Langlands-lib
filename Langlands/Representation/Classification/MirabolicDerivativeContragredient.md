# Contragredient maps from highest-derivative pairings

Author: Worker 1166.

This internal helper pair belongs to task
`0b3bf4c1-9878-444f-899e-ba29d7679c29`, the proof of
`Langlands.Classification.CuspidalProductMirabolicSupportShift` (BZ77 Lemma
4.7(b), mirabolic form). It formalizes steps 3 to 5 of the source proof (BZ77
§4.8, printed pp. 455–456), for an arbitrary representation `π` of `GL_(N+1)`:

- if `π' ≃ |det| π̃` and `W` embeds in `π|P`, then `W` and `π'|P` have a
  `|det|`-covariant pairing that is nondegenerate in `W`;
- if moreover `k > 0` is the level of `W` and `σ` is an irreducible
  subrepresentation of the highest derivative `W^(k)`, then there is a nonzero
  intertwiner from the order-`k` derivative `π'^(k)` to the smooth contragredient
  `σ̃`. The published BZ77 Proposition 3.8 supplies the pairing of derivatives.

The module does not prove the task target, and uses nothing about cuspidal
products. All declarations are in the namespace
`Langlands.Classification.MirabolicDerivativeContragredient`. The pair introduces
one definition (`pairingContragredientHom`), no proposition definitions, no
axioms, no theorem-valued premises and no `set_option`. Every result is proved
from published Library results only.

Throughout the `GL`/mirabolic sections, `p` is a prime, `F : PadicField p` and
`T : F.TopologicalData`. Every topology on `F` or on a group `GL_n(F)` is the
supplied one: `T.topology` and `T.generalLinearTopologicalGroup n`, introduced
by `letI` inside each statement. `P = P_(N+1)` is
`GeneralLinear.mirabolic N F.Carrier`, and `π|P` is
`(Derivative.generalLinearRestriction T N).obj π`.

## Contragredient maps

This section holds for any topological group `G` and smooth complex
representations.

- `pairingContragredientHom γ ι` (definition). Let `X` and `Y` be smooth
  representations, and let `γ` be an invariant pairing of `X` and `Y`, i.e. an
  element of `InvariantBilinear.forms X Y (fun _ => 1)`:
  `γ (X g x) (Y g y) = γ x y`. Let `ι : σ → X` be an intertwiner. Then
  `pairingContragredientHom γ ι : Y ⟶ σ̃` sends `y` to the functional
  `v ↦ γ (ι v) y`. This map into the algebraic dual of `σ` is equivariant for
  the contragredient action `(g ℓ)(v) = ℓ (σ g⁻¹ v)`: by invariance of `γ` at
  `g` and since `ι` intertwines,
  `γ (ι v) (Y g y) = γ (X g⁻¹ (ι v)) y = γ (ι (σ g⁻¹ v)) y`. Since `Y` is smooth,
  the image consists of smooth functionals, and the published `smoothLift`
  restricts the codomain to the smooth contragredient
  `σ̃ = SmoothRep.contragredient σ`. (The construction is the one in the
  published proof of `smoothInvariantPairingDuality`.)
- `pairingContragredientHom_apply` (by `rfl`): the functional at `y` takes `v`
  to `γ (ι v) y`.
- `pairingContragredientHom_ne_zero`: the map is nonzero if `γ` is
  nondegenerate in `X` (`∀ x, (∀ y, γ x y = 0) → x = 0`), `ι` is injective and
  `σ` has a vector `v₀ ≠ 0`. Indeed `ι v₀ ≠ 0`, so `γ (ι v₀) y ≠ 0` for some
  `y`, and the functional at `y` is nonzero at `v₀`.

The universes: `X` has carrier universe `uW`; `Y` and `σ` share one carrier
universe `uV`, because `Y ⟶ σ̃` is a morphism in one category of smooth
representations (the carrier of `σ̃` is in the universe of `σ`).

## Derivative of a restriction

- `mirabolicRankCast_restriction`: for `h : a = b`, the mirabolic rank transport
  `mirabolicRankCast T h` of `X|P_(a+1)` is the restriction to `P_(b+1)` of the
  `GL` rank transport `generalLinearRankCast T h'` of `X`. Proof: `subst h`,
  then `rfl`.
- `mirabolicDerivativeOfOrder_restriction`: for `0 < k ≤ N + 1` and a
  representation `X` of `GL_(N+1)`,
  `(mirabolicDerivativeOfOrder T ψ N k hk).obj (X|P) =
  (generalLinearDerivative T ψ (N + 1) k hk.2).obj X`, an equality of objects
  of `SmoothRep (GL_(N+1-k))`. Both sides are published definitions: the
  mirabolic derivative of order `k` is `mirabolicRankCast` followed by
  `mirabolicDerivative T ψ (N + 1 - k) (k - 1)` (`Derivative.Homogeneity`), and
  by the published `generalLinearDerivative_of_pos` the `GL` derivative is
  `generalLinearRankCast` followed by restriction to `P` and the same
  `mirabolicDerivative` (`Derivative.Iteration`). The previous lemma commutes
  the two rank transports with the restriction.

So the derivative `π'^(k)` of the target is literally the derivative of the
restriction `π'|P` used by the pairing statement, with the Library's
determinant-normalized functors `Φ⁻`, `Ψ⁻` on both sides.

## The determinant pairing

`exists_determinant_pairing π π' Φ W f hf`. The data: representations `π`, `π'`
of `GL_(N+1)`; a linear equivalence of representations
`Φ : π' ≃ |det|^1 ⊗ π̃`, where `π̃` is the smooth contragredient
`smoothContragredient π` and `|det|^1 ⊗ −` is the twist by the character
`T.determinantPowerCharacter (N + 1) 1`; a representation `W` of `P` and an
intertwiner `f : W ⟶ π|P` with injective underlying map. The conclusion: there
is a form
`β ∈ InvariantBilinear.forms W (π'|P) (fun g => |det g.val|)`, i.e.
`β (W g w) (π' g y) = |det g| · β w y` for `g ∈ P`, with `|det|` the real
number `T.determinantNorm (N + 1) g.val`, such that `β` is nondegenerate in
`W`: `∀ w, (∀ y, β w y = 0) → w = 0`.

Proof. Put `β w y = ⟨Φ y, f w⟩`, the published smooth dual pairing
`smoothDualPairing π`. The intertwining property of `Φ` gives
`Φ (π' g y) = |det g|^1 · π̃ g (Φ y)`, and the published
`smoothDualPairing_invariant` gives `⟨π̃ g ℓ, π g v⟩ = ⟨ℓ, v⟩`; with
`f (W g w) = π g (f w)` this is the covariance. The factor `|det g|^1` is
rewritten as `|det g|` by `coe_realPowerCharacter` and `Real.rpow_one`. For
nondegeneracy, let `β w y = 0` for all `y`. As `Φ` is surjective, every smooth
functional on `π` vanishes at `f w`. Smooth functionals separate the vectors of
a smooth representation of `GL_(N+1)(F)` (the published
`smoothBidual_injective_of_compact_cofinal`, with the cofinal compact open
subgroups `compactOpen_cofinal F T (N + 1)`), so `f w = 0`, and `w = 0` since
`f` is injective.

## The contragredient map from the derivative

- `exists_ne_zero_of_isIrreducible`: an irreducible representation has a
  nonzero vector (else `⊥ = ⊤` in its lattice of subrepresentations, which is
  excluded by irreducibility).
- `exists_derivative_hom_contragredient ψ π' W β hβ k hk hlevel σ hσ`. The data:
  a nontrivial unitary additive character `ψ`; a representation `π'` of
  `GL_(N+1)`; a representation `W` of `P` with a form `β` as above (covariance
  `|det|`, nondegenerate in `W`); `k` with `0 < k ≤ N + 1` and
  `Derivative.level T ψ W = k`; an irreducible subrepresentation `σ` of
  `W^(k) = (mirabolicDerivativeOfOrder T ψ N k hk).obj W` (that is,
  `IsIrreducibleSubrepresentation`: `σ` irreducible with an injective
  intertwiner `ι : σ → W^(k)`). The conclusion: there is a morphism
  `q : (generalLinearDerivative T ψ (N + 1) k hk.2).obj π' ⟶ σ̃` with
  `SmoothRep.hom q ≠ 0`.

Proof. The published `level_eq_iff` turns `level W = k` into: `W^(k)` is
nontrivial, and no `j` with `k < j ≤ N + 1` has a nonzero derivative. Via the
published `hasNonzeroDerivative_iff` and `not_nontrivial_iff_subsingleton`
these are the hypotheses `Nontrivial W^(k)` and `Subsingleton W^(j)` of the
published BZ77 Proposition 3.8, `Derivative.mirabolicHighestDerivativePairing F
T` (with `A = W`, `B = π'|P`, the form `β`). It gives an invariant pairing `γ`
(covariance `1`) of `W^(k)` and `(π'|P)^(k)`, nondegenerate in `W^(k)`. Rewrite
the goal with `mirabolicDerivativeOfOrder_restriction`, so that the source of
`q` is `(π'|P)^(k)`, and take `q = pairingContragredientHom γ ι`. It is nonzero
by `pairingContragredientHom_ne_zero`, since `σ` has a nonzero vector.

## Normalizations

- `|det|` is the Library's `T.determinantNorm n = T.normalizedAbsUnits ∘ det`,
  and `T.determinantPowerCharacter n s` is its real power `|det|^s`
  (`Classification.SupercuspidalTwist`). The twist by `|det|^1` is the source's
  `ν`.
- The source calls a form with `χ(g) B(π₁(g) ξ₁, π₂(g) ξ₂) = B(ξ₁, ξ₂)` a
  `χ`-pairing (BZ77 §3.6, printed p. 452). The pairing of `π` with `ν π̃` in
  §4.8 is a `ν⁻¹`-pairing; in the Library's convention
  (`InvariantBilinear.forms ρ σ χ`: `B (ρ g v) (σ g w) = χ g * B v w`) it has
  covariance `g ↦ |det g|`. Restricted to `P`, this is exactly the covariance
  required by the published `MirabolicHighestDerivativePairingStatement`, whose
  Markdown identifies it with the source's `Δ`-pairing on `P`. So no
  Haar-modulus comparison enters here; the comparison of the Library's
  determinant normalization with the source's (statement task
  `a622f240-4846-4086-b34f-f650ba636ee4`) is neither used nor needed.
- The derivatives are the Library's determinant-normalized
  `mirabolicDerivativeOfOrder` and `generalLinearDerivative`, unchanged.
- An "invariant" pairing has covariance `fun _ => 1`, as in the conclusion of
  the pairing statement.

## Relation to the source proof

BZ77 §4.8 argues: the natural pairing of `π` and `π̄ = ν π̃` restricts to a
nondegenerate (in `ω`) pairing of `ω ⊆ π|P` and `π̄|P`; by 3.8 there is a
pairing of `ω^(k)` and `π̄^(k)` nondegenerate in `ω^(k)`; "from the existence
of non-zero pairing of `σ` and `π̄^(k)` it follows that `σ̃ ∈ JH(π̄^(k))`."
This module implements the first two steps exactly, and replaces the last one
by the nonzero intertwiner `π̄^(k) → σ̃` (the pairing restricted to `σ`). Its
consumer, the proof of the task target, uses Lemma 4.7(a) in quotient form, so
it never needs a Jordan–Hölder series or finite length of `π̄^(k)`. Here `ω` is
`W`, which is embedded in `π|P` by an injective intertwiner instead of being a
subrepresentation.

## Universes

The `GL` and mirabolic sections have the field universe `uF` and one carrier
universe `uV` for `π`, `π'`, `W` and `σ` (the target uses `uV := max uF uV`).
The pairing statement is applied with `uV = uW`. The contragredient section is
universe-polymorphic in `uG`, `uV`, `uW`, as explained above.

## Provenance

The module is internal. It formalizes steps of BZ77 §4.8 (printed pp.
455–456) and uses BZ77 Proposition 3.8 (printed p. 453) only through its
published proof `Derivative.mirabolicHighestDerivativePairing` (proof task
`a925b519-9bb9-4927-873e-ad322d41328e`). The definition
`pairingContragredientHom` only names the map `σ ↦ σ̃` induced by a pairing.

## Import closure and exclusion audit

The module imports `Classification.SupercuspidalTwist`,
`Classification.ConstituentRelations`, `Category.Contragredient`,
`Smooth.Contragredient.AdmissibleDualityProof`,
`Smooth.Contragredient.LawsProof` and
`Derivative.MirabolicHighestDerivativePairingProof` (all under
`Langlands.Representation`). At Library commit
`b22e185743f7c318f709e14e422801f4360105d5`, its transitive Langlands import
closure has 144 modules (not counting this module):

- `Langlands.Analysis` (1): `Local.QuotientMeasure`
- `Langlands.Group` (18): `GL.Basic`, `GL.Blocks`, `GL.CompactOpen`, `GL.IntegralSubgroup`, `GL.Maps`, `GL.Mirabolic`, `GL.MirabolicProjection`, `GL.MirabolicRadical`, `GL.Nonarchimedean`, `GL.NonarchimedeanStatement`, `GL.NormalizedCharacter`, `GL.OppositeBlocks`, `GL.Padic`, `GL.PadicBlocks`, `GL.PadicOppositeBlocks`, `GL.PadicUpperUnipotent`, `GL.RankMaps`, `GL.UpperUnipotent`
- `Langlands.HarmonicAnalysis` (11): `Basic`, `CharacterTransport`, `Conductor`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`, `RowSchwartzAction`, `RowTestSmoothProof`, `RowTestSmoothStatement`
- `Langlands.LocalFactor` (3): `Euler`, `Euler.Definitions`, `Harmonic.Statement`
- `Langlands.LocalField` (6): `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology`
- `Langlands.Representation.Category` (4): `Basic`, `Contragredient`, `Subquotients`, `Twist`
- `Langlands.Representation.Classification` (5): `ConstituentRelations`, `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, `SupercuspidalTwist`
- `Langlands.Representation.Compact` (5): `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`
- `Langlands.Representation.Conductor` (1): `Congruence`
- `Langlands.Representation.Derivative` (14): `Homogeneity`, `Iteration`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`, `MirabolicHighestDerivativePairingStatement`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusPairingTransferProof`, `MirabolicMinusPairingTransferStatement`, `MirabolicPhiMinusNondegeneratePairing`
- `Langlands.Representation.Dual` (1): `Definitions`
- `Langlands.Representation.Filtration` (4): `Definitions`, `InvariantBilinear`, `InvariantBilinearBounds`, `ObjectDefinitions`
- `Langlands.Representation.Hecke` (1): `TestFunction`
- `Langlands.Representation.Jacquet` (5): `CharacterAveraging`, `CharacterTwistEquiv`, `Coinvariants`, `Localization`, `SmoothTwist`
- `Langlands.Representation.MatrixCoefficient` (3): `Definitions`, `LawsProof`, `LawsStatement`
- `Langlands.Representation.RankinSelberg` (16): `AnalyticStatement`, `EqualRankFrobeniusProof`, `EqualRankFrobeniusStatement`, `EqualRankTrilinearAssembly`, `EqualRankTrilinearReduction`, `EqualRankTrilinearUniquenessStatement`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `LocalFactor`, `Measures`, `QuotientIntegrals`, `RationalContinuation`, `RationalZeta`, `TwistInvariance`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`
- `Langlands.Representation.Smooth` (20): `Admissibility.CofinalProof`, `Admissibility.CofinalStatement`, `Admissibility.EquivalenceProof`, `Admissibility.EquivalenceStatement`, `Contragredient.AdmissibleDualityProof`, `Contragredient.AdmissibleDualityStatement`, `Contragredient.CompactDualityProof`, `Contragredient.CompactDualityStatement`, `Contragredient.Definitions`, `Contragredient.FixedVectorsDefinitions`, `Contragredient.LawsProof`, `Contragredient.LawsStatement`, `Definitions`, `FixedVectors.Definitions`, `SmoothPart.Definitions`, `SmoothPart.FixedVectorsDefinitions`, `Transfer.PullbackProof`, `Transfer.PullbackStatement`, `Transfer.SubquotientProof`, `Transfer.SubquotientStatement`
- `Langlands.Representation.Twist` (16): `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `DualProof`, `DualStatement`, `RealPower`, `SmoothPartDefinitions`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`
- `Langlands.Representation.Unitary` (1): `Basic`
- `Langlands.Representation.Whittaker` (5): `Algebraic`, `AlgebraicTwist`, `DualTransform`, `GeneralLinear`, `Twist`
- `Langlands.Topology` (4): `CompactNormCharacter`, `CompactOpen.NeighborhoodBasis`, `CompactOpen.NeighborhoodBasisStatement`, `Nonarchimedean.Subgroup`

The derivative, Rankin–Selberg (compact-orbit and cutoff integrals), Whittaker
(basic Gelfand–Kazhdan definitions) and matrix-coefficient modules all enter
through the published BZ77 3.8 proof `Derivative.MirabolicHighestDerivativePairingProof`,
which the task admits as an input. Its closure also contains the published
proof of `MirabolicDerivativeDetection` (`Derivative.MirabolicDerivativeVanishing`).

The mathematical proof dependencies used directly are:
`mirabolicHighestDerivativePairing` (BZ77 3.8, admitted input),
`generalLinearDerivative_of_pos`, `level_eq_iff`, `hasNonzeroDerivative_iff`
(definitional facts about the derivative functors and the level),
`smoothDualPairing_invariant`, `smoothBidual_injective_of_compact_cofinal`,
`compactOpen_cofinal`, `smoothLift`, `coe_realPowerCharacter` (smooth duality,
smooth parts and real powers). Condition by condition, against the exclusions
of the task contract (`context.md` of task `0b3bf4c1`):

- `HighestDerivativeSupportShift`, task `f81d9b36` and its candidates and
  helpers (`HighestDerivativeSupportShiftBoundary`,
  `CuspidalProductDerivativeQuotientSupport`), and
  `CuspidalSupport.WholeLeviTransport`: none of these names occurs in any
  closure module.
- Items (b), (d), (e), (f) of task `8e5b4563` (`SegmentSocleDerivatives`,
  `NonjuxtaposedSegmentSocleConstituentLevel`,
  `NonjuxtaposedSegmentSocleDerivativeStrictMono`,
  `SegmentSocleProductHighestDerivative`) and the other statements of that
  contribution: none occurs. No closure module mentions `Segment`; the only
  mention of `Socle` is the general definition `IsIrreducibleSocle` in
  `Classification.ConstituentRelations`, which is not used.
- Two-supercuspidal product conclusions (`TwoSupercuspidal*`, tasks `3c9849a4`,
  `ab61f565`): none occurs.
- Segment derivative, Jacquet and product formulas, segment-socle/head
  existence, exhaustion, irreducibility criteria, linked and juxtaposed
  segment results, ordered-socle existence, socle commutation and gluing,
  special-head criteria, quotient coverage, ordered conversion, tempered
  uniqueness, `SquareIntegrableLanglandsClassification`,
  `GenericSegmentProductUniqueness`, square-integrable and regular exhaustion,
  special-segment square-integrability, Ze80 6.1(a) and later results of task
  `b711af72`: none occurs (the only word "Exhaustion" is a section name in
  `Jacquet.CharacterAveraging`, about compact open exhaustions of a unipotent
  group).
- Leibniz filtration (BZ77 4.5/4.6) and exactness of derivatives
  (`MirabolicMinusExactnessStatement`, `GeneralLinearDerivativeExactnessStatement`):
  no closure module mentions `Leibniz` or `Exactness`. The operator-paused task
  `b65bc667` is untouched.
- Whittaker coinvariant finiteness (`SupercuspidalCoinvariantFiniteness`,
  `IrreducibleCoinvariantFiniteness`, `LeviCuspidalCoinvariantFiniteness`,
  tasks `62de5903`, `5ab445dc`, `3ff5c8fb`) and `Whittaker.MirabolicFiniteLength`
  (task `5428fe2c`): none occurs.
- Derivatives of supercuspidal representations (BZ77 §4.4): not used.
- `UnitaryGenericCompatibilityStatement`, `TwistedProduct*`,
  `TwoSupercuspidalProductDualTwist`: absent.

The keyword search covered the module names and the full source text of every
closure module.
