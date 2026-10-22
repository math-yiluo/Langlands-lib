# Tempered representations modulo the center

Author: Worker 23.

This module defines tempered and essentially tempered representations by the
analytic condition on matrix coefficients. It also gives measure-free forms of
square-integrability, temperedness and their essential versions for `GL_n` over
every p-adic field.

The definition is not stated through Jacquet exponents. The exponent criteria
(Casselman's criterion, Silberger 1979 Lemma 4.5.3) are separate theorems.

## Generic layer

`G` is a topological group, `V` a complex vector space, and
`Q = G ⧸ Subgroup.center G` the actual central quotient with a supplied
measurable structure. The measure `μ` is a supplied Haar measure on `Q`, as in
the published `IsSquareIntegrableModCenter` of `MatrixCoefficient/ModuloCenter`.

- `IsTemperedModCenter ρ μ` holds when `ρ` is admissible and there is a unitary
  central character `c` (the published `UnitaryCentralCharacter ρ`: a character
  of the center with open kernel and absolute value one, by which the center
  acts). In addition, for every smooth-dual functional `ℓ`, every vector `v` and
  every real `ε > 0`, the function `gZ ↦ |ℓ(ρ(g) v)|` on `Q` must lie in
  `L^(2+ε)(μ)`, written as `MemLp … (ENNReal.ofReal (2 + ε)) μ`. That function
  is the published `c.coefficientNorm ℓ v`. It is well defined because the
  central character is unitary.
- `IsTemperedModCenter.isAdmissible` extracts admissibility.
- `isTemperedModCenter_of_equiv` and `isTemperedModCenter_iff_of_equiv` show
  that the predicate is invariant under actual equivalences of representations.
  The carriers may lie in different universes. The proof transports the central
  character and pulls functionals back along the equivalence, as for the
  published square-integrable predicate.
- `TemperedExponentData ν ρ μ` is a real `exponent` together with a proof that
  `realPowerTwist ν (-exponent) ρ` is tempered, where `ν : G →* ℝ≥0ˣ` is a
  positive character. `IsEssentiallyTemperedModCenter ν ρ μ` is its
  nonemptiness. This parallels the published `SquareIntegrableExponentData` of
  `Classification/Essential`.
  - `normalized`, `normalized_tempered`, `normalized_admissible` and
    `reconstruct` cover the normalization: `ν^exponent` applied to the
    normalized representation gives back `ρ`.
  - `isSmooth` derives smoothness of `ρ` when `ν` has open kernel.
  - `ofTempered` is the zero-exponent witness.
  - `shift t` adds `t` to the exponent for `realPowerTwist ν t ρ`.
  - `ofEquiv` and `isEssentiallyTemperedModCenter_iff_of_equiv` transport
    witnesses along equivalences.

## `GL_n` over a p-adic field

Fix a p-adic field `F`, a realization `T : F.TopologicalData` and `n`. Let
`Q = GL_n(F) ⧸ Z` be the actual central quotient with the quotient topology of
`T`.

- `T.centralQuotientMeasurableSpace n` is the Borel σ-algebra of `Q`.
  `T.centralQuotientBorelSpace n` records that it is Borel.
- `T.exists_isHaarMeasure_centralQuotient n` proves that `Q` has a Haar measure.
  The proof uses Mathlib's `haarMeasure`, which applies because `GL_n(F)` is
  locally compact (`generalLinearLocallyCompactSpace`) and hence so is `Q`.
- `T.IsSquareIntegrable ρ` means that `IsSquareIntegrableModCenter ρ μ` holds for
  every Haar measure `μ` on `Q`.
- `T.IsTempered ρ` means that `IsTemperedModCenter ρ μ` holds for every Haar
  measure `μ` on `Q`.
- `T.IsEssentiallySquareIntegrable ρ` means that
  `T.IsSquareIntegrable (realPowerTwist (T.determinantNorm n) (-s) ρ)` holds for
  some real `s`. Thus `ρ = ν^s ρ₀` with `ρ₀` square-integrable and `ν = |det|`.
  The absolute value is residue-normalized, `|ϖ| = q⁻¹`.
- `T.IsEssentiallyTempered ρ` is the same with `IsTempered`.

Proved facts:

- `IsSquareIntegrable.isAdmissible` and `IsTempered.isAdmissible`, using the
  existence of a Haar measure.
- Invariance under equivalences: `isSquareIntegrable_iff_of_equiv`,
  `isTempered_iff_of_equiv`, `isEssentiallySquareIntegrable_iff_of_equiv` and
  `isEssentiallyTempered_iff_of_equiv`.
- Exponent zero: `IsSquareIntegrable.isEssentiallySquareIntegrable` and
  `IsTempered.isEssentiallyTempered`.
- Stability under `ν^t`, with `t` added to the exponent:
  `IsEssentiallySquareIntegrable.realPowerTwist` and
  `IsEssentiallyTempered.realPowerTwist`.

**Why all Haar measures.** The sources integrate against "the" Haar measure of
`G/Z`, which is unique up to a positive scalar, and `L^p` membership does not
change under such scaling. The `GL_n` predicates quantify over all Borel Haar
measures. Because a Haar measure exists, they are not vacuous. Haar measures on
`Q` are unique up to scalar because `Q` is locally compact and second countable.
That theorem is neither proved nor assumed here, so "for every Haar measure" and
"for some Haar measure" are not proved equivalent. The same holds for the
published measure-dependent predicates. The `GL_n` forms carry no measure
argument, so they can be used for every block of a Levi subgroup at once.

## Source correspondence

- Kudla (1994), section 2.2, printed page 372 (PDF page 382 of the *Motives*
  Part 2 volume): "An irreducible algebraic representation π of G is tempered if
  it has a unitary central character and its matrix coefficients φ_{v,ṽ} lie in
  L^{2+ε}(Z\G) for all ε > 0. The essentially tempered representations are those
  that are obtained from a tempered representation by twisting by a character."
  Here `G = GL(n, F)`. On printed page 367 (PDF page 377), "algebraic" means
  smooth and admissible, and `π(s) = π ⊗ |det|^s`. This is `IsTemperedModCenter` and
  `T.IsTempered`. The unitary central character is the published datum, and the
  matrix coefficients `⟨π(g)v, ṽ⟩` are those of the smooth dual. Since `Z` is
  central, `Z\G` and `G ⧸ Z` are the same quotient group. `L^p` membership of a
  coefficient is membership of its absolute value, which descends to `G/Z`.
- Casselman (1995), section 2.5, printed page 28: the parallel definition of
  square-integrability modulo `Z`. It requires an admissible `ω`-representation
  with `|ω(z)| = 1` and every `|c_{v,ṽ}|` square-integrable on `G/Z`. This is the
  published `IsSquareIntegrableModCenter`, which `T.IsSquareIntegrable` uses for
  every Haar measure.
- Henniart (2002), sections 2.5--2.6, printed page 595: "essentiellement de carré
  intégrable", and twists by `ν`, the character of `F^×` given by the normalized
  absolute value. These are `T.IsEssentiallySquareIntegrable` and
  `T.determinantNorm`.
- Silberger (1979), section 4.5, printed pages 182--184 (PDF pages 188--190):
  the analytic setting. A function is tempered when its distribution extends
  continuously to the Harish-Chandra Schwartz space. Theorem 4.5.1 characterizes
  this, for functions bi-invariant under an open compact subgroup, by the weak
  inequality bounded by `Ξ(x)(1 + σ(x))^r`. An admissible representation is
  called tempered when its matrix-coefficient functions are tempered. The
  equivalence of this formulation with the `L^(2+ε)` formulation is a theorem.
  It needs Harish-Chandra's `Ξ`, which has not been formalized, and it is
  neither proved nor assumed here. Silberger's Lemma 4.5.3 (pp. 185--186) gives
  the exponent criterion, which is likewise not used as a definition.

Registered sources:

- `kudla-1994-local-langlands-nonarchimedean`, SHA256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`, the whole
  *Motives* Part 2 volume, printed pages 367 and 372.
- `casselman-1995-admissible-representations`, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`,
  section 2.5, printed page 28.
- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`,
  sections 2.5--2.6, printed page 595.
- `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`,
  section 4.5, printed pages 182--186.

## Derivations

- **Domain.** Kudla's definition is stated for irreducible representations. The
  predicates here apply to all admissible representations, as Silberger's does,
  and irreducibility is a separate restriction.
- **Essential versions.** Kudla twists by an arbitrary character. Here the
  twist is by a real power of `ν = |det|`, the form used by Henniart and by the
  Langlands data. For `GL_n` the two agree. Every character of `GL_n(F)` factors
  through `det`, and is a unitary character times a real power of `|·|`. Twisting
  by a unitary character preserves temperedness. These facts are theorems that
  are not proved here.
- **Order of quantifiers.** `T.IsEssentiallySquareIntegrable` puts the exponent
  first and quantifies over Haar measures afterwards. The published
  `IsEssentiallySquareIntegrableModCenter ν ρ μ` fixes one measure. The two agree
  under Haar uniqueness, which is not proved here.

## Universes and scope

The group lies in `Type uG` (for `GL_n`, in the field universe `uF`). The
representation carriers lie in independent universes `uV` and `uW`. The
coefficient field is `ℂ`. Every p-adic field, every realization `T` and every
`n` is covered. No irreducibility, finite dimension or unitarity is imposed.

## Not claimed

The module proves none of the following. Each is a separate theorem obligation:

- independence of the Haar measure;
- that square-integrable representations are tempered;
- stability under unitary twists or contragredients;
- the equivalence with Silberger's tempered functions;
- Casselman's or Silberger's exponent criteria;
- the classification of tempered representations of `GL_n` as irreducible
  inductions of square-integrable ones (Kudla, Proposition 2.2.1, attributed to
  Jacquet);
- the Langlands classification.
