# Harish-Chandra finiteness implies admissibility of generated realizations

`Langlands.Automorphic.GeneratedFormAdmissibilityReductionStatement.{u}` is
`HarishChandraFinitenessStatement.{u} → GeneratedFormAdmissibilityStatement.{u}`.
The theorem `generatedFormAdmissibility_of_harishChandraFiniteness` proves
this implication. Both propositions are defined in
[AutomorphicAdmissibilityStatement](AutomorphicAdmissibilityStatement.md).
The number field retains universe `u`. The conclusion ranges over all ranks,
automorphic forms, open finite adelic subgroups `L` and representations `σ`
of the standard compact subgroup `K_∞` on `Fin m → ℂ`.

## Proof

**A common annihilating ideal.** Write `Z` for the center of the archimedean
enveloping algebra. For an automorphic form `f`, `CenterSeed.seedSpan` forms
the span of the vectors `z · R(k)f` in the finite-smooth rational
functions, with `z ∈ Z` and `k ∈ K_∞`. This span contains `f`. Multiplication
in `Z` gives stability under the center, and covariance of the center action
gives stability under compact translation. The covariance is
`finiteSmoothRightAction_envelopingAction` restricted to the center.
[OperatorCompactCompatibility](OperatorCompactCompatibility.lean)

The compact orbit of `f` is spanned by finitely many compact translates by
`automorphicCompactRightAction_isFiniteVector`. Each such translate has a
finite-dimensional central orbit span, since covariance transports the
central orbit span of `f` by an invertible translation. Center finiteness
of `f` is used through `isCenterFinite_iff_finiteSmoothCenterVector`.
`CenterSeed.seedSpan_finite` bounds the span of all the vectors `z · R(k)f`
by the sum of these finitely many central orbit spans.
[DifferentialCenterFinite](DifferentialCenterFinite.lean)

Let `J` be the annihilator of that span. `CenterSeed.seedRestriction`
restricts the action of `Z` to the span, and
`CenterSeed.seedAnnihilator_finite_quotient` embeds `Z/J` into its
finite-dimensional space of endomorphisms. If `z` annihilates the span and
`w` belongs to it, then `R(k)(Ad(k)⁻¹(z) · w) = z · R(k)w = 0`.
Invertibility of `R(k)` yields the ideal stability needed in the proof.

**The generated realization.** `centerAnnihilatedRealization` consists of
stable automorphic functions annihilated by `J`. Finite adelic translations
commute with the enveloping action, compact translations preserve
annihilation by the covariance and ideal stability just proved, and
all enveloping operators commute with the center. The space therefore
contains the generated realization by
`generatedFormOperatorRealization_le_iff`. This inclusion and the finite
codimension of `J` are supplied by
`exists_center_ideal_generatedFormOperatorRealization`.
[FullOperatorRealization](FullOperatorRealization.lean)

**Multiplicity spaces.** For an open subgroup `L` and a representation `σ`,
postcomposition with `S.formInclusion` gives an injective complex linear
map from the multiplicity space of the generated realization `S` to
`annihilatedFormMultiplicitySpace F n J L.toSubgroup σ`. The inclusion
intertwines finite and compact translations, so postcomposition preserves
`L`-fixedness and `K_∞`-equivariance. The preceding inclusion of realizations
ensures the values are annihilated by `J`. The Harish-Chandra finiteness
premise supplies finite dimension for the codomain, which transfers across
the injection by `FiniteDimensional.of_injective`.

## Provenance

Borel and Jacquet derive Proposition 4.5 (1) ⇒ (4) from §4.3 (i). Their
§4.2 (b)–(c) supplies the compact and central finiteness conditions, and
§4.3 (i) gives finiteness at fixed type and ideal. The relevant locations
in *Automorphic forms and automorphic representations*, Corvallis Part I
(1979), are §4.2 and §4.3 (i) on printed p. 195 (PDF p. 190) and
Proposition 4.5 on printed p. 196 (PDF p. 191). The registered source is
`borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

The Lean proof supplies the operator-stability argument using the
annihilator of the central translates of the compact orbit. This is the
adelic version of the finite-span construction used for smooth
archimedean functions in
[ArchimedeanGeneratedCenterAnnihilator](../Global/ArchimedeanGeneratedCenterAnnihilator.md).
The final implication takes `HarishChandraFinitenessStatement` as its
sole premise. It is proved in the Library as `harishChandraFiniteness`
(module `Langlands.Automorphic.HarishChandraFinitenessProof`).
