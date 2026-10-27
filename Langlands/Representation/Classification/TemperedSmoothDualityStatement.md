# Analytic temperedness and the smooth contragredient (statement)

Author: Worker 246.

`Langlands.Classification.PadicTemperedSmoothDualityStatement` is a
`Prop`-valued definition. It states a theorem and does not prove it. The
proof is a separate obligation, described at the end of this file.

## Statement and quantifiers

The definition quantifies over:

- every prime `p` with `[Fact p.Prime]`;
- every `F : PadicField.{uF} p`;
- every compatible topological realization `T : F.TopologicalData`;
- every rank `n : ℕ` with `0 < n`.

Inside the body it installs `T.topology` and
`T.generalLinearTopologicalGroup n` on the actual group
`GeneralLinear n F.Carrier`. It then quantifies over every carrier
`V : Type uV` with `[AddCommGroup V] [Module ℂ V]` and every representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`. It asserts:

```
IsAdmissible ρ →
  (T.IsTempered (smoothContragredient ρ) ↔ T.IsTempered ρ)
```

So for an admissible `ρ`, the smooth contragredient of `ρ` is analytically
tempered exactly when `ρ` is.

The field universe `uF` and the carrier universe `uV` are independent. The
carrier `SmoothDual ρ` of the smooth contragredient is a submodule of
`Module.Dual ℂ V`, so it also lies in `Type uV`. Both sides of the
equivalence are therefore instances of the same predicate in the same
carrier universe. No topology and no finite dimension is imposed on `V`.

## Unchanged imported constructions

The module imports [Classification.Tempered](Tempered.md) and
[Smooth.Contragredient.Definitions](../Smooth/Contragredient/Definitions.md)
and changes neither.

- `smoothContragredient ρ` is the published smooth contragredient. Its carrier
  `SmoothDual ρ` is the smooth part of the full algebraic dual
  `Module.Dual ℂ V`, with the action `g ↦ ᵗρ(g⁻¹)`. It is not an
  inverse-transpose pullback of `ρ` and is not replaced by one.
- `T.IsTempered` is the published predicate for `GL_n(F)`. It uses the actual
  central quotient
  `Q = GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`.
  `Q` carries the quotient topology induced by `T` and the Borel measurable
  structure `T.centralQuotientMeasurableSpace n`. The predicate quantifies over
  **every** Borel Haar measure `μ` on `Q`. For each such `μ`, it requires
  `IsTemperedModCenter ρ μ`: admissibility of `ρ`, a
  `UnitaryCentralCharacter ρ`, and
  `MemLp (c.coefficientNorm ℓ v) (ENNReal.ofReal (2 + ε)) μ` for every smooth
  functional `ℓ : SmoothDual ρ`, vector `v : V` and real `ε > 0`. A
  `UnitaryCentralCharacter ρ` is a character of the center with open kernel and
  values of norm one through which the center acts by scalars.
  `T.exists_isHaarMeasure_centralQuotient n` shows that this quantification is
  not vacuous.
- `IsAdmissible ρ` is the published predicate of
  [Smooth.Definitions](../Smooth/Definitions.md): `ρ` is smooth and its fixed
  vectors for every open subgroup form a finite-dimensional space. The topology
  is the one installed by `T`.

## Scope

- The single premise is `IsAdmissible ρ`. It is needed for the reverse
  implication. The smooth contragredient only sees smooth functionals, so
  without admissibility (or at least smoothness) `ρ̃` can be tempered while
  `ρ` is not even admissible. The forward implication needs no premise,
  since `T.IsTempered ρ` already contains admissibility of `ρ`.
- The statement does not assume irreducibility, unitarizability or finite
  dimension of `ρ`. It fixes no chosen Haar measure and no specified central
  character. It has no inversion-invariance or unimodularity premise and no
  supplied transport map.
- The rank is positive, as the task requires. The smooth contragredient, the
  analytic predicate and every supplied topology are used exactly as
  published.
- The statement concerns `T.IsTempered` only. It makes no claim about
  square-integrability, essential temperedness or any classification.
- The import closure consists of the two imported modules and their
  definitional dependencies: local-field data, `GL_n` topology, matrix
  coefficients modulo the center, twists, and smooth/admissible definitions.
  It contains no classification, coverage or exhaustion result. In particular
  it does not depend on ordered special-segment coverage, multisegment
  exhaustion, square-integrable exhaustion or regular Langlands exhaustion.

## Provenance

This is an internal derived obligation, not a transcription of a separately
cited theorem. It is a focused prerequisite of the tempered
Langlands-quotient coverage task `e2afd36b-5c1f-461f-882d-86f03e86b9bd`
(Worker 624). That coverage argument selects a maximal cone for the smooth
dual of its input. Through first adjointness it embeds the smooth dual into an
opposite normalized induction, reverses to upper induction, and dualizes back
using admissible reflexivity and normalized-induction duality. Its final
tempered blocks must stay analytically tempered after smooth duality. This
statement records that requirement for the published analytic predicate.

The mathematical fact is classical. The algebraic inputs are in W. Casselman,
*Introduction to the theory of admissible representations of p-adic reductive
groups* (draft, 1 May 1995; literature ID
`casselman-1995-admissible-representations`), §2.1, pp. 21–22. The
contragredient is defined there as the restriction of the dual `ᵗπ(g⁻¹)` to
the functionals fixed by some open subgroup. Proposition 2.1.10 (p. 22) states
that `π` is admissible iff `π̃` is admissible iff `π̃̃ ≅ π`. The analytic
transfer below is the elementary inverse-group change of variables. It is not
quoted from a source.

Related published statements are different results. The smooth-dual clause of
`Langlands.GLSquareIntegrabilityPrerequisitesStatement`
([SquareIntegrabilityStatement](SquareIntegrabilityStatement.md)) concerns
square-integrability for a fixed Haar measure, `F.canonicalTopology` and
`Matrix.GeneralLinearGroup (Fin n) F.Carrier`. It is unproved and gives no
input here. `Langlands.Classification.PadicInverseTransposeAnalyticStatement`
([InverseTransposeAnalyticStatement](InverseTransposeAnalyticStatement.md))
concerns pullback along the automorphism `g ↦ (g⁻¹)ᵀ`. That pullback has the
same carrier `V` and is not identified with the smooth contragredient. A
group-automorphism transport theorem alone therefore does not give the
present statement.

## Needed future proof

The proof is not part of this unit. A proof should establish the following,
splitting off any substantial missing prerequisite as its own task first.

1. **Smooth dual admissibility and bidual reflexivity.**
   `Langlands.GeneralLinear.compactOpen_cofinal F T n`
   (Representation.Category.Contragredient) gives compact-open cofinality of
   `GL_n(F)` for arbitrary `T`. It is built from the compact-open choices of
   Group.GL.CompactOpen. With
   `Langlands.isAdmissible_smoothContragredient_of_compact_cofinal`,
   `Langlands.smoothBidual_injective_of_compact_cofinal` and
   `Langlands.smoothBidual_surjective_of_compact_cofinal`
   (Smooth.Contragredient.AdmissibleDualityProof), an admissible `ρ` has
   admissible `smoothContragredient ρ` and a bijective `smoothBidual`.
2. **Inversion of the unitary central character.** Given
   `c : UnitaryCentralCharacter ρ`, define one for `smoothContragredient ρ` with
   character `z ↦ (c.character z)⁻¹`. It has the same open kernel and values of
   norm one. The scalar-action field follows from
   `(ρ̃ z ℓ) v = ℓ (ρ z⁻¹ v) = (c z)⁻¹ ℓ v` for smooth functionals `ℓ`.
3. **Inverse-group coefficient identity.** For `v : V` and `ℓ : SmoothDual ρ`,
   the bidual image `smoothBidual hρ.1 v : SmoothDual (smoothContragredient ρ)`
   satisfies
   `matrixCoefficient ρ̃ (smoothBidual v) ℓ g = matrixCoefficient ρ ℓ v g⁻¹`.
   Descending to `Q`, every coefficient norm of `ρ̃` for the dual central
   character equals `c.coefficientNorm ℓ v ∘ (·)⁻¹`, with inversion on the
   quotient group `Q`. By surjectivity of `smoothBidual`, every smooth
   functional on `SmoothDual ρ` has this form, so every coefficient of `ρ̃` is
   covered.
4. **Haar change of variables on `GL_n` modulo its center.** For a Borel Haar
   measure `μ` on `Q`, `T.centralQuotientHaar_rightInvariant n`
   (Group.GL.CentralQuotientMeasure) makes `μ` right invariant. Mathlib's
   `Measure.inv.instIsMulLeftInvariant`,
   `Measure.IsFiniteMeasureOnCompacts.inv` and `Measure.IsOpenPosMeasure.inv`
   then make `μ.inv = Measure.map (·)⁻¹ μ` a Borel Haar measure. This needs
   continuity, hence Borel measurability, of inversion on the topological group
   `Q`. Applying `T.IsTempered ρ` to `μ.inv` and `MemLp.comp_of_map` gives
   `MemLp (c.coefficientNorm ℓ v ∘ (·)⁻¹) (ENNReal.ofReal (2 + ε)) μ`. This
   is the forward implication `T.IsTempered ρ → T.IsTempered ρ̃`.
5. **Reflection.** For the reverse implication, apply the forward implication
   to the admissible `ρ̃`. This gives temperedness of the double smooth
   contragredient. Then transport along the equivalence `ρ ≃ ρ̃̃` given by the
   bijective `smoothBidual`, via Mathlib's
   `Representation.IntertwiningMap.ofBijective`, using
   `T.isTempered_iff_of_equiv`.

Common finite-exponent coefficient lemmas for a square-integrability analogue
may be exposed by the proof, but they are not obligations of this statement.
