# NYLL M140.011: the kernel of the normalized valuation on field units

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_exists_integerUnitStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_exists_integerUnit`.
The theorem's type is the target applied to all its parameters: a field `L`
in universe `u` with a valuative relation, a topology and the
`IsNonarchimedeanLocalField L` instance, and a field unit `x : Lˣ`.
The imports are the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements`
and the published proof module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs`.
The published statement and its imported definitions remain unchanged.

The statement is

```lean
valuationUnitsMulHom L x = 1 ↔ ∃ y : 𝒪[L]ˣ, integerUnitsToFieldUnits L y = x
```

that is, a field unit has multiplicative normalized valuation `1` exactly when
it is the image of a unit of the valuation integer ring `𝒪[L]` under the
published inclusion `integerUnitsToFieldUnits L : 𝒪[L]ˣ →* Lˣ`.

## Implemented proof

After unfolding the target definition, the proof establishes two local facts
and then runs the source argument.

1. `hOneIffZero`: `valuationUnitsMulHom L x = 1 ↔ valuationMap L (Additive.ofMul x) = 0`.
   This is NYLL M140.010 at `x`, whose proof is not yet in the Library. It is
   proved by the original M140.010 proof: `valuationMap L` is
   `MonoidHom.toAdditive (valuationUnitsMulHom L)`, so after a `change` both
   directions follow from `Multiplicative.toAdd` and its injectivity.

2. `hRange`: for every `y : Lˣ`,
   `y ∈ MonoidHom.range (integerUnitsToFieldUnits L) ↔ valuationMap L (Additive.ofMul y) = 0`.
   This is NYLL M134.029, whose proof is not yet in the Library. It is proved
   by the original M134.029 argument.
   - Forward: for `y = integerUnitsToFieldUnits L w`, the goal is changed to
     `v L (Additive.ofMul (integerUnitsToFieldUnits L w)) = 0`. This uses the
     definitional equality `valuationMap L = v L` on these arguments, which
     is the content of M134.004 `valuationMap_apply` (proved by `rfl`). The
     goal is then closed by the published theorem
     `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits`
     (NYLL M128.019, from the imported `Basic.U019.Proofs` module).
   - Reverse: from `valuationMap L (Additive.ofMul y) = 0` the proof first
     derives `hv : ValuativeRel.valuation L y = 1`. This is NYLL M134.020,
     whose proof is not yet in the Library, and it is proved by the original
     M134.020 proof. It unfolds the published `v`, so that the hypothesis says
     the `WithZero.unzero` of the image of `valuation L y` under
     `valueGroupWithZeroIsoInt L` is `1`. It then coerces back to
     `WithZero (Multiplicative ℤ)`, rewrites with `WithZero.coe_unzero`, and
     concludes by injectivity of `valueGroupWithZeroIsoInt L`. Next comes the
     integer unit `w : 𝒪[L]ˣ` with value `y` and inverse `y⁻¹`. Both lie in
     `𝒪[L]` by Mathlib's `Valuation.mem_integer_iff` together with `hv`, and
     the unit laws follow from `mul_inv_cancel₀` and `inv_mul_cancel₀`.
     Finally `integerUnitsToFieldUnits L w = y` holds by `ext; rfl`.

3. The main goal is rewritten by `hOneIffZero`. The forward direction is
   `(hRange x).2`. In the reverse direction, `x = integerUnitsToFieldUnits L y`
   and `(hRange _).1 ⟨y, rfl⟩` applies.

The local facts are `have`s and `let`s inside the proof, so the file adds no
declaration besides the required theorem. Apart from the published
definitions reached through the statement import, the proof uses the
published M128.019 and Mathlib only.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`:

- `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`
  (SHA-256 `478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`):
  the target theorem at lines 222–237 (docstring at lines 222–223, theorem at
  lines 224–237), and the inlined M140.010 proof at lines 213–220.
- `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`
  (SHA-256 `8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`):
  the inlined M134.020 proof `valuation_eq_one_of_valuationMap_eq_zero` at lines
  182–205 (theorem at lines 178–205), the definition
  `integerUnitOfValuationMapZero` at lines 251–270 with its specification
  `integerUnitOfValuationMapZero_spec` at lines 272–280, and the M134.029 proof
  `integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero` at lines
  288–294 (theorem at lines 283–294).

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_exists_integerUnit` | `Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_exists_integerUnit` |

Modifications:

- The namespace prefix is `Langlands.NYLL`. The imports are the focused
  statement import and the published `Basic.U019.Proofs`.
- The result is expressed as the published target proposition applied to all
  its parameters, so the proof first unfolds that definition.
- The source rewrites by M140.010 and applies M134.029. Here both are local
  `have`s with their original proofs, since neither proof is in the Library.
  The task allows such local proofs and forbids publishing second copies
  under the adapted names.
- In M134.029, the source rewrite `rw [valuationMap_apply]` becomes a `change`
  to the same definitionally equal goal.
- The source's separate definition `integerUnitOfValuationMapZero` is built
  inline as a local `let`. Its `_spec` lemma becomes a local `have` with the
  original `ext; rfl` proof.
- In that construction, the source's NYLL lemma `valuation_integer_membership`
  (M130.001) is replaced by Mathlib's `Valuation.mem_integer_iff`. The source
  lemma is itself built from `Valuation.mem_integer_iff`, and here the Mathlib
  lemma rewrites membership in `𝒪[L]` to `valuation L _ ≤ 1`. The M134.020
  result, called inside the construction in the source, is proved once before
  it as `hv`.
- The source `noncomputable section` and all other source declarations are
  omitted.

The retained original snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The original copyright, Apache-2.0 license statement and author header are
preserved in the Lean file, followed by the modification record. The
inherited `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain
unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This support lemma proves M140.011 only. It does not publish M140.010,
M134.020 or M134.029, and it proves no host class-formation, cup-product,
transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `aed16b9e-8615-4bc7-9667-993627fc8532` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
