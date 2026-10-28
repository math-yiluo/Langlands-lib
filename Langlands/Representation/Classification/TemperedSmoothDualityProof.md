# Analytic temperedness and the smooth contragredient (proof)

Author: Worker 246.

This module proves the published proposition
[`PadicTemperedSmoothDualityStatement`](TemperedSmoothDualityStatement.md):

```text
theorem Langlands.Classification.padicTemperedSmoothDuality :
    PadicTemperedSmoothDualityStatement.{uF, uV}
```

The field universe `uF` and the carrier universe `uV` stay independent. The
proof adds no hypothesis. It uses the published smooth contragredient, the
published predicate `T.IsTempered` and the topology supplied by `T` unchanged.
No published file is edited.

Write `ρ̃ = smoothContragredient ρ` and
`Q = GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`.

## Imported results

- [Smooth.Contragredient.AdmissibleDualityProof](../Smooth/Contragredient/AdmissibleDualityProof.md):
  `isAdmissible_smoothContragredient_of_compact_cofinal`,
  `smoothBidual_injective_of_compact_cofinal` and
  `smoothBidual_surjective_of_compact_cofinal`. When compact open subgroups are
  cofinal among open subgroups, an admissible `ρ` has admissible `ρ̃`, and
  `smoothBidual` is bijective onto the smooth dual of `ρ̃`.
- [Category.Contragredient](../Category/Contragredient.md):
  `GeneralLinear.compactOpen_cofinal F T n`, the cofinality of compact open
  subgroups of `GL_n(F)` for the topology of `T`. This import adds only twist,
  category and compact-open modules to the closure. It adds no coverage or
  exhaustion result.
- [Group.GL.CentralQuotientMeasure](../../Group/GL/CentralQuotientMeasure.md):
  `T.centralQuotientHaar_rightInvariant n μ`. Every Borel Haar measure `μ` on
  `Q` is right invariant.
- [Classification.Tempered](Tempered.md): `T.isTempered_iff_of_equiv`.
  Temperedness is invariant under equivalences of representations.
- Mathlib: the instances `Measure.inv.instIsMulLeftInvariant`,
  `Measure.IsFiniteMeasureOnCompacts.inv` and `Measure.IsOpenPosMeasure.inv`,
  `MemLp.comp_of_map`, and `measurable_inv`.

## Generic group `G`

The first section works for any topological group `G` and complex
representation `ρ` of `G` on `V`. The quotient `G ⧸ Subgroup.center G` carries
a Borel measurable structure.

1. `UnitaryCentralCharacter.contragredient c` is a unitary central character of
   `ρ̃`. Its character is `c.character⁻¹`. It has the same kernel as
   `c.character`, so the kernel is open. Its values have norm one because
   `‖u⁻¹‖ = ‖u‖⁻¹`. For central `z` and a smooth functional `ℓ`,
   `(ρ̃ z ℓ) v = ℓ (ρ z⁻¹ v) = (c z)⁻¹ ℓ v`, which is the scalar-action field.
   `UnitaryCentralCharacter.contragredient_character` records the character by
   `rfl`.
2. `matrixCoefficient_smoothContragredient_smoothBidual` is the identity
   `matrixCoefficient ρ̃ (smoothBidual hρ v) ℓ g = matrixCoefficient ρ ℓ v g⁻¹`.
   It holds by `rfl`: `ρ̃ g ℓ = ℓ ∘ ρ g⁻¹`, and `smoothBidual hρ v` evaluates
   functionals at `v`.
3. `UnitaryCentralCharacter.coefficientNorm_smoothBidual` descends this to `Q`.
   For any central-character data `c` of `ρ` and `d` of `ρ̃`, the absolute
   coefficient `d.coefficientNorm (smoothBidual hρ v) ℓ` equals
   `c.coefficientNorm ℓ v ∘ (·⁻¹)`, with inversion on the quotient group `Q`.
   Both sides are norms of the same coefficient on a representative, so the
   proof is quotient induction and `rfl`.
4. `IsTemperedModCenter.smoothContragredient_of_inv` assumes that compact open
   subgroups are cofinal and that `μ` and `μ.inv` are Haar measures on `Q`. It
   shows `IsTemperedModCenter ρ μ.inv → IsTemperedModCenter ρ̃ μ`. Admissibility
   of `ρ̃` is the imported admissibility result. The central character is
   `c.contragredient`. Every smooth functional on `SmoothDual ρ` is
   `smoothBidual hρ v` for some `v`, by the imported surjectivity. Step 3
   rewrites its coefficient as `c.coefficientNorm ℓ v ∘ (·⁻¹)`. The hypothesis
   gives `MemLp (c.coefficientNorm ℓ v) (ENNReal.ofReal (2 + ε)) μ.inv`, and
   `μ.inv` is the pushforward `Measure.map (·⁻¹) μ`. `MemLp.comp_of_map` with
   measurability of inversion gives the required `MemLp` for `μ`.

## Haar measures under inversion

`Measure.isHaarMeasure_inv_of_isMulRightInvariant`: on a topological group with
its Borel structure, the inverse `μ.inv` of a right-invariant Haar measure `μ`
is a Haar measure. Left invariance of `μ.inv` is the Mathlib instance from
right invariance of `μ`. Finiteness on compacts and positivity on open sets
pass to `μ.inv` by the Mathlib instances.

`PadicField.TopologicalData.centralQuotientHaar_inv T n` installs the topology
of `T`, the topological-group structure on `GL_n(F)`, and the Borel structure
`T.centralQuotientMeasurableSpace n` on `Q`. It applies this lemma to every
Borel Haar measure on `Q`, which is right invariant by
`T.centralQuotientHaar_rightInvariant n`.

## Forward implication

`PadicField.TopologicalData.IsTempered.smoothContragredient` shows
`T.IsTempered ρ → T.IsTempered ρ̃`. `T.IsTempered ρ̃` quantifies over every
Borel Haar measure `μ` on `Q`. For such `μ`, `μ.inv` is also a Borel Haar
measure by `centralQuotientHaar_inv`. Applying `T.IsTempered ρ` to `μ.inv`
gives `IsTemperedModCenter ρ μ.inv`. Step 4 with
`GeneralLinear.compactOpen_cofinal F T n` gives `IsTemperedModCenter ρ̃ μ`.
This direction needs no admissibility premise beyond the one contained in
`T.IsTempered ρ`.

## Main theorem

`padicTemperedSmoothDuality` takes an admissible `ρ`. The imported bidual
results give that `smoothBidual hρ.1 : ρ → ρ̃̃` is bijective. Mathlib's
`Representation.IntertwiningMap.ofBijective` turns it into an equivalence
`e : ρ ≃ ρ̃̃`.

- If `ρ̃` is tempered, the forward implication applied to `ρ̃` makes `ρ̃̃`
  tempered. `T.isTempered_iff_of_equiv e` transports this to `ρ`.
- If `ρ` is tempered, the forward implication makes `ρ̃` tempered.

The positivity of the rank is not used. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The route is the one recorded under "Needed future proof" in the statement's
Markdown. The algebraic inputs are W. Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups* (draft, 1 May 1995;
literature ID `casselman-1995-admissible-representations`), §2.1, pp. 21–22,
through the published admissible-duality proof. The analytic transfer is the
elementary change of variables `g ↦ g⁻¹` on `Q`, written out here. It is not
quoted from a source.
