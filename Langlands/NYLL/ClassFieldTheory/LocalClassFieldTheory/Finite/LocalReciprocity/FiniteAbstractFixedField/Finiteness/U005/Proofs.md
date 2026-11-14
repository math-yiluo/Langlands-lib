# NYLL M099.005: finite abstract fields have finite-dimensional fixed fields

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensionalStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensional`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractFixedField_finiteDimensionalStatement k Ω H hfinite`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, the explicit fields `k Ω : Type` with
instances `[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]` (the section's
Galois hypothesis is kept, as in the source and the statement), a closed
subgroup `H : ClosedSubgroup (Gal(Ω/k))` and the hypothesis

```lean
hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
  extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))
```

that the quotient of the distinguished base subgroup (the whole group) by
`H`, viewed as a subgroup of it, is finite. It has no universe parameters.

Unfolding the published proposition gives
`FiniteDimensional k (abstractFixedField k Ω H)`, where the published
abbreviation `abstractFixedField k Ω H` is
`IntermediateField.fixedField H.toSubgroup`, the intermediate field of `Ω`
fixed by `H`.

## Implemented proof

The source proof calls the M099.004 theorem
`abstractFiniteClosedSubgroup_isOpen`, whose source proof in turn calls the
M099.003 theorem `ambientQuotientFiniteOfAbstractFinite`. Neither proof is in
the Library yet (both are candidates of this task), so, as the task permits,
this module proves both results locally under non-conflicting names, as
`private` theorems:

- `ambientQuotientFiniteOfAbstractFinite_local`, with the source signature
  of `ambientQuotientFiniteOfAbstractFinite` (source lines 48–55, including
  `omit [IsGalois k Ω] in`, conclusion `Finite (Gal(Ω/k) ⧸ H.toSubgroup)`)
  and its source proof (lines 56–64) verbatim. `Nat.finite_of_card_ne_zero`
  reduces finiteness to `H.toSubgroup.index ≠ 0`; rewriting backwards with
  `Subgroup.relIndex_top_right` and a `change` restate this as the index of
  the abstract extension subgroup inside
  `(baseField (Gal(Ω/k))).toSubgroup = ⊤` being nonzero; and
  `Subgroup.index_ne_zero_of_finite`, with `hfinite` as the finiteness
  instance, closes it.
- `abstractFiniteClosedSubgroup_isOpen_local`, with the source signature of
  `abstractFiniteClosedSubgroup_isOpen` (source lines 66–73, including
  `omit [IsGalois k Ω] in`, conclusion `IsOpen H.carrier`) and its source
  proof (lines 74–78), calling `ambientQuotientFiniteOfAbstractFinite_local`
  in place of `ambientQuotientFiniteOfAbstractFinite`. The finite quotient
  gives the local instance `Subgroup.FiniteIndex H.toSubgroup` by
  `Subgroup.finiteIndex_of_finite_quotient`, and
  `Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'`
  shows that the closed finite-index subgroup is open.

The complete proof body of the required theorem is

```lean
  apply (InfiniteGalois.isOpen_iff_finite
    (K := Ω) (abstractFixedField k Ω H)).1
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  exact abstractFiniteClosedSubgroup_isOpen_local k Ω H hfinite
```

Mathlib's `InfiniteGalois.isOpen_iff_finite L`, for an intermediate field
`L` of the Galois extension `Ω/k`, states
`IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k L`. Applying its
forward direction to `L = abstractFixedField k Ω H` (after the elaborator
unfolds the statement definition) reduces the goal to openness of the
fixing subgroup of the fixed field of `H`. Since `abstractFixedField` is an
abbreviation of `IntermediateField.fixedField H.toSubgroup`, Mathlib's
`InfiniteGalois.fixingSubgroup_fixedField H`, which says that this fixing
subgroup is `H.toSubgroup` for a closed subgroup `H`, rewrites the goal to
`IsOpen H.carrier`. The local openness lemma closes it. Both Mathlib
theorems use the instance `IsGalois k Ω`.

Apart from stating the type as the published proposition and calling the
local lemma in place of `abstractFiniteClosedSubgroup_isOpen`, this is the
original declaration verbatim, including its docstring. No other auxiliary
declaration, extra hypothesis or global instance is introduced. The
development check reports no errors or warnings, no universe parameters, and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensionalStatement`
  in FiniteAbstractFixedField.Finiteness.Statements.
- The published abbreviation
  `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`
  (FiniteAbstractFixedField.Initial.Definitions), the published definitions
  `Langlands.NYLL.ClassFormation.baseField`
  (AbstractClassFieldTheory.Degree.Fields.Definitions) and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
  (GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions), and
  the published theorem `Langlands.NYLL.ClassFormation.le_baseField`
  (AbstractClassFieldTheory.Degree.Fields.U005.Proofs), which occur in the
  statement and the local lemmas; all are reached through the Statements
  module's imports.
- The private local lemmas `ambientQuotientFiniteOfAbstractFinite_local` and
  `abstractFiniteClosedSubgroup_isOpen_local` of this module, described
  above.
- Mathlib's `InfiniteGalois.isOpen_iff_finite` and
  `InfiniteGalois.fixingSubgroup_fixedField`
  (`Mathlib/FieldTheory/Galois/Infinite.lean`); and, in the local lemmas,
  `Nat.finite_of_card_ne_zero`, `Subgroup.relIndex_top_right`,
  `Subgroup.index_ne_zero_of_finite`,
  `Subgroup.finiteIndex_of_finite_quotient`,
  `Subgroup.isOpen_of_isClosed_of_finiteIndex` and `ClosedSubgroup` with its
  field `isClosed'`.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:80–90`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L80-L90).
Lines 80–81 are the docstring, 82–86 the signature and 87–90 the proof. The
local lemmas copy lines 48–64 (M099.003) and 66–78 (M099.004). The section
variable line 31 is
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, inside
`namespace LocalClassFieldTheory` (line 22) with
`open RamificationTheory KummerTheory CyclicCohomology` (line 23),
`open ClassFormation` (25) and `noncomputable section` (29). The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.005 (source unit start line 82). The whole-file
SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `abstractFixedField_finiteDimensional` (M099.005) | Published `abstractFixedField_finiteDimensionalStatement` in FiniteAbstractFixedField.Finiteness.Statements |
| Proof `abstractFixedField_finiteDimensional` | This theorem of the same adapted name in FiniteAbstractFixedField.Finiteness.U005.Proofs |
| `ambientQuotientFiniteOfAbstractFinite` (M099.003) | Private local copy `ambientQuotientFiniteOfAbstractFinite_local` in this module |
| `abstractFiniteClosedSubgroup_isOpen` (M099.004), used by the proof | Private local copy `abstractFiniteClosedSubgroup_isOpen_local` in this module |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, merges the source's
namespace openings into `open CyclicCohomology ClassFormation` (omitting the
unused `RamificationTheory` and `KummerTheory`), keeps the
`noncomputable section`, the section variables and the docstrings, adds the
two private local lemmas, and states the theorem's type as the published
proposition applied to `k Ω H hfinite`. The proof is otherwise unchanged.

Once the M099.003 and M099.004 proofs are in the Library, the local lemmas
duplicate them privately; they are not second public copies under the
adapted names.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused; the local
lemmas follow the pinned source (and agree with Worker 395's own M099.003 and
M099.004 candidates). There are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M099.005. The other M099 units and any host
class-formation, cup, transfer, Tate or reciprocity target are separate work.
