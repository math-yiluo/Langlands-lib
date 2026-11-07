# Continuous square-integrable functions on `[G]` and the unitary pairing

Author: Worker 112.

The published module `UnitaryCharacterPairing` works with a topological group
`H`, subgroups `Γ₀` and `Z`, and a unitary character `ω` of `Z`. It constructs
the invariant pairing `∫ conj f * g` on continuous functions on `H` that are
left `Γ₀`-invariant and transform by `ω` under left multiplication by `Z`. The
integral is over the actual quotient `LeftCosetSpace (Z ⊔ Γ₀)`. That module
does not compare its spaces with Mathlib's `Lp` or with any adelic quotient.

The present module does that comparison for the trivial character `ω = 1`, in
two steps.

1. Generic step, for any `H`. A continuous function on `H` with trivial
   character is the same as a continuous function on `LeftCosetSpace (Z ⊔ Γ₀)`.
   Under this identification, the square-integrable functions of the pairing
   are the continuous `L²` functions on the quotient, and the pairing is the
   inner product of their classes in `Lp ℂ 2 μ`. Positive right translation on
   `H` becomes composition with the published actual right translation
   `LeftCosetSpace.rightTranslate`.
2. `[G]` step. Take `Γ₀ = G(F)` and `Z` the split-centre subgroup of the
   published restriction quotient `RestrictionSplitCentre.Quotient F G S j`.
   Then the generic quotient is the published `[G]`. The functions of the
   pairing are identified with the published continuous square-integrable
   functions `quotientContinuousL2Submodule` on `[G]`, compatibly with the
   published right actions and the published map to `L²([G])`. For the
   canonical quotient measure `quotientHaarMeasure` of a connected reductive
   group, the module gives an `InvariantPositiveForm` that equals the
   `L²([G])` inner product, and proves injectivity of the map to `L²([G])`.

The quotient `[G] = A_G G(F) \ G(A_F)` follows Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69); the
published `AdelicRestrictionSplitCentre` implements it. The module imports the
published `UnitaryCharacterPairing`, `GroupSchemeRestrictionFullAEL2Hilbert`
and `GroupSchemeRestrictionCuspidalL2`.

## Generic step

### An instance on the actual quotient

`LeftCosetSpace.opensMeasurableSpace Γ` (namespace `Langlands.Global`): if
`H` has a topology and a measurable structure with `[OpensMeasurableSpace H]`,
open sets of the actual quotient `LeftCosetSpace Γ` are measurable for the
quotient measurable structure. An open set has an open preimage under the
continuous quotient map, and that preimage is measurable.

### Trivial character and descent

Namespace `Langlands.Automorphic.UnitaryCharacterPairing`. Here
`H : Type u` is a group with a topology and `[ContinuousMul H]`, and `Γ₀` and
`Z` are arbitrary subgroups. `CharacterFunctions Γ₀ Z 1` is the published space
for the trivial character.

- `le_leftStabilizer_of_trivial f`: such an `f` is fixed by left multiplication
  by every element of `Z ⊔ Γ₀`. This is the published `sup_le_leftStabilizer`
  applied to the two defining conditions.
- `quotientFunction f` is `f` descended to a continuous function on
  `LeftCosetSpace (Z ⊔ Γ₀)` by the published `descend`. `quotientFunction_mk`
  holds by definition, and `quotientFunction_add` and `quotientFunction_smul`
  give linearity.
- `quotientFunction_characterAction`: descending the published right translate
  `characterAction Γ₀ Z 1 g f` gives the descended function composed with
  `rightTranslate (Z ⊔ Γ₀) g`.
- `norm_quotientFunction` and `pairingDensity_eq_quotientFunction`: the
  published densities `normDensity f` and `pairingDensity f g` are
  `‖quotientFunction f‖` and `conj (quotientFunction f) * quotientFunction g`
  pointwise.
- `ofQuotient Γ₀ Z φ` pulls a continuous `φ` on the quotient back to `H`, as a
  function with trivial character. `ofQuotient_val_apply` holds by definition.
  The `Γ₀` and `Z` conditions are `LeftCosetSpace.mk_subgroup_mul` for elements
  of `Z ⊔ Γ₀`.
- `trivialCharacterEquiv Γ₀ Z` is the complex-linear equivalence
  `CharacterFunctions Γ₀ Z 1 ≃ₗ[ℂ] C(LeftCosetSpace (Z ⊔ Γ₀), ℂ)` given by
  `quotientFunction` and `ofQuotient` (`quotientFunction_ofQuotient`,
  `ofQuotient_quotientFunction`), with `_apply` and `_symm_apply`.
- `trivialCharacterEquiv_characterAction` assumes `[IsTopologicalGroup H]`,
  which the published `LeftCosetSpace.continuous_rightTranslate` requires. The
  equivalence carries `characterAction g` to composition with the continuous
  map `rightTranslate (Z ⊔ Γ₀) g`.

### `L²`

The quotient carries any `MeasurableSpace` with `[OpensMeasurableSpace]`, and
`μ` is any measure on it.

- `memLp_quotientFunction_iff f`: `MemLp (quotientFunction f) 2 μ` holds exactly
  when `f` lies in the published `l2CharacterSubmodule Γ₀ Z 1 μ`. The proof uses
  `memLp_norm_iff` and `norm_quotientFunction`.
- `quotientL2Submodule Γ₀ Z μ` is the submodule of continuous functions on the
  quotient with `MemLp φ 2 μ` (`mem_quotientL2Submodule`). `quotientL2ToLp μ`
  sends `φ` to its class `MemLp.toLp`, and `coeFn_quotientL2ToLp` holds.
- From here on, `hμ : RightInvariant Γ₀ Z μ` is the published hypothesis that
  every right translation preserves `μ`.
  `memLp_quotientFunction_toCharacter` is the published `toCharacter_mem`
  translated by `memLp_quotientFunction_iff`.
- `ofQuotientL2 hμ` and `l2QuotientEquiv hμ` give the complex-linear
  equivalence between the published `L2Functions Γ₀ Z 1 μ hμ` and
  `quotientL2Submodule Γ₀ Z μ`. The lemmas `l2QuotientEquiv_apply_mk` and
  `l2QuotientEquiv_symm_apply_val` hold by definition.
  `l2QuotientEquiv_l2Action` shows that the published `l2Action g` becomes
  composition with `rightTranslate (Z ⊔ Γ₀) g`.
- `toL2 hμ` is `quotientL2ToLp μ` composed with `l2QuotientEquiv hμ`. The
  lemmas `toL2_apply` and `coeFn_toL2` (almost everywhere equal to the
  descended function) hold.
- `inner_toL2`: `inner ℂ (toL2 hμ f) (toL2 hμ g)` equals the published
  `pairing Γ₀ Z 1 μ (toCharacter f) (toCharacter g)`. The proof rewrites the
  `L²` inner product as `∫ conj (toL2 f) * toL2 g` (`MeasureTheory.L2.inner_def`)
  and replaces both classes by the descended functions almost everywhere.
  `inner_toL2_eq_sesquilinearPairing` restates this with the published
  `sesquilinearPairing`. `norm_toL2_sq` gives
  `‖toL2 hμ f‖ ^ 2 = ∫ (normDensity f)² dμ`.
- `toL2_l2Action`: `toL2 hμ (l2Action g f)` is
  `Lp.compMeasurePreserving (rightTranslate (Z ⊔ Γ₀) g) (hμ g) (toL2 hμ f)`.
  The proof uses `Lp.toLp_compMeasurePreserving`.
- `quotientL2ToLp_injective` assumes `[μ.IsOpenPosMeasure]`. Two continuous
  functions with the same class are equal (`Measure.eq_of_ae_eq`), as in the
  published `quotientContinuousL2ToLp_injective`. `toL2_injective` follows,
  because `l2QuotientEquiv hμ` is injective.

## `[G]` step

Namespace `Langlands.Global.RestrictionSplitCentre`. The data are as for the
published `Quotient F G S j`:

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`.

### Two spellings of the same quotient

The published `Quotient F G S j` is `LeftCosetSpace (rationalSubgroup F G S j)`.
The published `rationalSubgroup F G S j` is, by definition,
`subgroup F G S j ⊔ AdelicGroupPoints.rationalSubgroup F G`. With
`Z = subgroup F G S j` and `Γ₀ = AdelicGroupPoints.rationalSubgroup F G`, the
generic quotient `LeftCosetSpace (Z ⊔ Γ₀)` is therefore definitionally `[G]`,
and every declaration below is the generic one at these subgroups.

A measure `measureQ` on `Quotient F G S j` carries the measurable structure of
`LeftCosetSpace (rationalSubgroup F G S j)`. The generic declarations are
elaborated on the `Z ⊔ Γ₀` spelling, so they see this measurable structure
together with the topology of `LeftCosetSpace (Z ⊔ Γ₀)`. Instance search does
not unfold the definition `rationalSubgroup`. It therefore does not apply
instances stated for one spelling to this mixed pair. Two declarations bridge
the gap:

- the instance `quotientOpensMeasurableSpace` is the generic instance
  `LeftCosetSpace.opensMeasurableSpace (rationalSubgroup F G S j)` of this
  module. It is stated with the topology of `LeftCosetSpace (Z ⊔ Γ₀)` and the
  measurable structure of `Quotient F G S j`;
- the theorem `isOpenPosMeasure_sup F G measureQ` takes
  `[measureQ.IsOpenPosMeasure]` for a measure on `Quotient F G S j` and returns
  the same hypothesis, stated for the same mixed pair of structures.

Both are proved by the term they restate. They change only how the type is
written.

### Comparison with the published spaces on `[G]`

Let `measureQ` be any measure on `Quotient F G S j` and
`hInv : QuotientRightInvariant F G measureQ`. This published proposition
states that every actual right translation preserves `measureQ`; it is the
generic `RightInvariant` for these subgroups.

- `ContinuousL2Functions F G measureQ hInv` is the published
  `L2Functions G(F) Z 1 measureQ hInv`. It consists of continuous functions on
  `G(A_F)` that are left `G(F)`-invariant and left invariant under the split
  centre, with square-integrable descent to `[G]`.
  `continuousL2Action F G measureQ hInv` is positive right translation by
  `G(A_F)` on it, the published `l2Action`.
- `continuousL2Equiv F G measureQ hInv` is the generic `l2QuotientEquiv`. It is
  a complex-linear equivalence onto the published
  `quotientContinuousL2Submodule F G measureQ`. The lemmas
  `continuousL2Equiv_apply_mk` and `continuousL2Equiv_symm_apply_val` hold by
  definition.
- `continuousL2Equiv_continuousL2Action`: the equivalence carries
  `continuousL2Action g` to the published
  `quotientContinuousL2RightAction F G measureQ hInv g`.
- `quotientContinuousL2ToLp_continuousL2Equiv`: the published
  `quotientContinuousL2ToLp F G measureQ` composed with the equivalence is
  `toL2 hInv` (by definition).
- `toL2_continuousL2Action`: `toL2 hInv` carries `continuousL2Action g` to the
  published right regular representation
  `rationalQuotientL2RightAction F G measureQ hInv g` on `L²([G])`.
- `inner_quotientContinuousL2ToLp_continuousL2Equiv`: the `L²([G])` inner
  product of the classes of `continuousL2Equiv f` and `continuousL2Equiv g` is
  the published `sesquilinearPairing f g`, that is, `∫ conj f * g` over `[G]`.

### The canonical measure for connected reductive `G`

In addition, assume:

- `hG : IsConnectedReductive G`.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`, with
  `h : subgroup F G S j = imageSubgroup F T G i`.
- `characterRestrict i` is injective (`hi`) with finite-index range,
  `hc : IsCentral i`, and `hT : IsSplitTorus T.toGrp`.

The published `quotientHaarMeasure_rightInvariant_of_connectedReductive` and
`quotientHaarMeasure_isOpenPosMeasure_of_connectedReductive` (in
`GroupSchemeRestrictionFullAEL2Hilbert`) give, from these hypotheses, right
invariance and positivity on nonempty open sets of the canonical
`quotientHaarMeasure F G S j`. No separate right-invariance hypothesis on
norm-one Haar measure is taken. Write `hμ` for that right-invariance proof.

- `reductiveContinuousL2InvariantForm F G hG h hi hc hT` is the published
  `UnitaryCharacterPairing.invariantPositiveForm` for
  `continuousL2Action F G (quotientHaarMeasure F G S j) hμ`. It is a published
  `InvariantPositiveForm`: positive definite, Hermitian, and invariant under
  every right translation.
- `reductiveContinuousL2InvariantForm_inner`: its value on `f` and `g` is the
  `L²([G])` inner product of the classes
  `quotientContinuousL2ToLp (continuousL2Equiv f)` and
  `quotientContinuousL2ToLp (continuousL2Equiv g)`.
- `isUnitarizable_reductiveContinuousL2Action`: the action is
  `IsUnitarizable`.
- `reductive_toL2_injective`: `toL2 hμ` is injective. Positivity on open sets
  enters through `isOpenPosMeasure_sup`.

### Split components

The section `SplitComponents` takes `hG`, `hi` with finite-index range, and
`hj : IsSplitComponent j` and `hs : IsSplitComponent i` instead of `h`, `hc`
and `hT`. It uses the published
`quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive`
and `quotientHaarMeasure_isOpenPosMeasure_of_splitComponents_of_connectedReductive`,
and gives `splitComponentContinuousL2InvariantForm`,
`splitComponentContinuousL2InvariantForm_inner`,
`isUnitarizable_splitComponentContinuousL2Action` and
`splitComponent_toL2_injective`, with the same statements as above.

## Scope

Only the trivial character `ω = 1` is compared with `L²`. A nontrivial unitary
central character would need `L²` of a line bundle on the quotient, which is
not constructed here. The module does not complete the space of continuous
functions or prove that it is dense in `L²([G])`. It does not prove that cusp
forms or other automorphic forms are square integrable. For the canonical
measure, right invariance and positivity on open sets come from the published
theorems named above. For a general `measureQ` they are hypotheses.

## Provenance

The quotient `[G]` is Getz--Hahn (2.20)--(2.21), as implemented by the
published `AdelicRestrictionSplitCentre`. Its `L²` space, right regular
representation and continuous square-integrable functions are the published
`GroupSchemeRestrictionQuotientL2` and `GroupSchemeRestrictionCuspidalL2`. The
pairing is the published `UnitaryCharacterPairing`. This module identifies the
two constructions. It asserts no external theorem. The proofs use only these
published interfaces and Mathlib's `L²` lemmas: `MeasureTheory.L2.inner_def`,
`MemLp.toLp_congr`, `Lp.toLp_compMeasurePreserving`, `MemLp.toLp_eq_toLp_iff`
and `Measure.eq_of_ae_eq`.
