# NYLL M099.004: finite abstract fields are open subgroups

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractFiniteClosedSubgroup_isOpenStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abstractFiniteClosedSubgroup_isOpen`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractFiniteClosedSubgroup_isOpenStatement k Ω H hfinite`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, the explicit fields `k Ω : Type` with
instances `[Field k] [Field Ω] [Algebra k Ω]` (the section's
`[IsGalois k Ω]` is omitted, as in the source and the statement), a closed
subgroup `H : ClosedSubgroup (Gal(Ω/k))` and the hypothesis

```lean
hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
  extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))
```

that the quotient of the distinguished base subgroup (the whole group) by
`H`, viewed as a subgroup of it, is finite. It has no universe parameters.

Unfolding the published proposition gives `IsOpen H.carrier`: `H` is open in
the Krull topology of `Gal(Ω/k)`.

## Implemented proof

The source proof calls the M099.003 theorem
`ambientQuotientFiniteOfAbstractFinite`. That proof has been accepted for
this task (candidate `f9589122-1032-415c-a704-0761b3ddbf0b`) but is not yet
in the Library, so, as the task permits, this module proves the needed
result locally under a non-conflicting name:

```lean
private theorem ambientQuotientFiniteOfAbstractFinite_local
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) :
    Finite (Gal(Ω/k) ⧸ H.toSubgroup)
```

Its signature is the source signature of `ambientQuotientFiniteOfAbstractFinite`
(source lines 51–55, with `omit [IsGalois k Ω] in`), and its proof is the
source proof (lines 56–64) verbatim: `Nat.finite_of_card_ne_zero` reduces
finiteness of the quotient to `H.toSubgroup.index ≠ 0`; rewriting backwards
with `Subgroup.relIndex_top_right` and a `change` restate this as the index
of the abstract extension subgroup
`extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H)` inside
`(baseField (Gal(Ω/k))).toSubgroup = ⊤` being nonzero, and
`Subgroup.index_ne_zero_of_finite`, applied with `hfinite` as the finiteness
instance, closes it. The lemma is `private`, so this module adds no public
declaration besides the required theorem.

The complete proof body of the required theorem is

```lean
  let : Finite (Gal(Ω/k) ⧸ H.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite_local k Ω H hfinite
  let : Subgroup.FiniteIndex H.toSubgroup :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'
```

The first `let` makes the finiteness of `Gal(Ω/k) ⧸ H.toSubgroup` available
as a local instance. Mathlib's `Subgroup.finiteIndex_of_finite_quotient`
turns it into the instance `Subgroup.FiniteIndex H.toSubgroup`. Mathlib's
`Subgroup.isOpen_of_isClosed_of_finiteIndex` states that a closed subgroup of
finite index in a topological group is open; it is applied to
`H.toSubgroup` and the closedness field `H.isClosed'` of the closed subgroup,
and its conclusion `IsOpen (H.toSubgroup : Set (Gal(Ω/k)))` is
definitionally `IsOpen H.carrier`, the published proposition after the
elaborator unfolds the statement definition.

Apart from stating the type as the published proposition and calling the
local lemma in place of `ambientQuotientFiniteOfAbstractFinite`, this is the
original declaration verbatim, including its docstring and the
`omit [IsGalois k Ω] in` of source line 66. No other auxiliary declaration,
extra hypothesis or global instance is introduced. The development check
reports no errors or warnings, no universe parameters, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractFiniteClosedSubgroup_isOpenStatement`
  in FiniteAbstractFixedField.Finiteness.Statements.
- The published definitions `Langlands.NYLL.ClassFormation.baseField`
  (AbstractClassFieldTheory.Degree.Fields.Definitions) and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
  (GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions), and
  the published theorem `Langlands.NYLL.ClassFormation.le_baseField`
  (AbstractClassFieldTheory.Degree.Fields.U005.Proofs), which occur in the
  statement and the local lemma; all are reached through the Statements
  module's imports.
- The private local lemma `ambientQuotientFiniteOfAbstractFinite_local` of
  this module, described above.
- Mathlib's `Nat.finite_of_card_ne_zero`, `Subgroup.relIndex_top_right`,
  `Subgroup.index_ne_zero_of_finite` and
  `Subgroup.finiteIndex_of_finite_quotient` (`Mathlib/GroupTheory/Index.lean`
  and `Mathlib/SetTheory/Cardinal/Finite.lean`),
  `Subgroup.isOpen_of_isClosed_of_finiteIndex` and the structure
  `ClosedSubgroup` with its field `isClosed'`
  (`Mathlib/Topology/Algebra/Group/ClosedSubgroup.lean`), together with the
  Krull topology on `Gal(Ω/k)`.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:66–78`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L66-L78).
Line 66 is `omit [IsGalois k Ω] in`, 67–68 the docstring, 69–73 the
signature and 74–78 the proof. The local lemma copies lines 48–64 (the
M099.003 theorem). The section variable line 31 is
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, inside
`namespace LocalClassFieldTheory` (line 22) with
`open RamificationTheory KummerTheory CyclicCohomology` (line 23),
`open ClassFormation` (25) and `noncomputable section` (29). The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.004 (source unit start line 69). The whole-file
SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `abstractFiniteClosedSubgroup_isOpen` (M099.004) | Published `abstractFiniteClosedSubgroup_isOpenStatement` in FiniteAbstractFixedField.Finiteness.Statements |
| Proof `abstractFiniteClosedSubgroup_isOpen` | This theorem of the same adapted name in FiniteAbstractFixedField.Finiteness.U004.Proofs |
| `ambientQuotientFiniteOfAbstractFinite` (M099.003), used by the proof | Private local copy `ambientQuotientFiniteOfAbstractFinite_local` in this module |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, merges the source's
namespace openings into `open CyclicCohomology ClassFormation` (omitting the
unused `RamificationTheory` and `KummerTheory`), keeps the
`noncomputable section`, the section variables, `omit [IsGalois k Ω] in` and
the docstring, adds the private local lemma, and states the theorem's type as
the published proposition applied to `k Ω H hfinite`. The proof is otherwise
unchanged.

Once the M099.003 proof is in the Library, the local lemma duplicates it
privately; it is not a second public copy under the adapted name.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused; the local
lemma follows the pinned source (and agrees with Worker 395's own accepted
M099.003 candidate). There are no project coauthors.

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

This proof covers only M099.004. The finite-dimensionality unit M099.005,
which uses this result, and any host class-formation, cup, transfer, Tate or
reciprocity target are separate work.
