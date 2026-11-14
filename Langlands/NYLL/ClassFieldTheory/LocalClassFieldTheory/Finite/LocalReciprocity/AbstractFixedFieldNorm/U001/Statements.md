# Relative norms along equal closed subgroups: congruence target (M166.001)

Let `G` be a topological group and `A` an integral representation of `G`.
For closed subgroups `C ≤ B` of `G` with finitely many left cosets of `C` in
`B`, the published relative norm `relativeNorm A B C hCB` sends a `C`-fixed
element of `A` to a `B`-fixed element. Its value is the sum, over the left
cosets `bC` of `C` in `B`, of the translates `b · x`.

This module states, without proof, the source theorem
`relativeNorm_coe_eq_of_closedSubgroup_eq` (M166.001). Suppose `B = B'` and
`C = C'` as closed subgroups, and `x` and `x'` are fixed elements of `A`
with the same underlying element of `A`. Then the relative norms of `x`
along `C ≤ B` and of `x'` along `C' ≤ B'` have the same underlying element
of `A`.

So the value of a relative norm depends only on the subgroups and on the
underlying element. It does not depend on the containment proofs, on the
finiteness instances, or on the subtypes in which the fixed elements are
presented. The source uses this congruence to avoid dependent rewriting
through the containment proof carried by `relativeNorm`.

The target is the Prop-valued definition
`relativeNorm_coe_eq_of_closedSubgroup_eqStatement` in the namespace
`Langlands.NYLL.LocalClassFieldTheory`. It is a target for a later proof.

## The Lean statement

```lean
namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology KummerTheory ClassFormation

set_option linter.unusedVariables false in
def relativeNorm_coe_eq_of_closedSubgroup_eqStatement
    {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G)
    (B B' C C' : ClosedSubgroup G)
    (hCB : C.toSubgroup ≤ B.toSubgroup)
    (hC'B' : C'.toSubgroup ≤ B'.toSubgroup)
    [hfinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B C hCB)]
    [hfinite' : Finite
      (B'.toSubgroup ⧸ extensionSubgroup B' C' hC'B')]
    (hB : B = B') (hC : C = C')
    (x : ambientFixedAddSubgroup A C)
    (x' : ambientFixedAddSubgroup A C')
    (hx : x.1 = x'.1) : Prop :=
  ((relativeNorm A B C hCB x : ambientFixedAddSubgroup A B) : A.V) =
    ((relativeNorm A B' C' hC'B' x' :
      ambientFixedAddSubgroup A B') : A.V)
```

The hypotheses `hB`, `hC` and `hx` do not occur in the proposition. They are
binders of the definition, so the proposition is asserted only for data that
satisfy them. A proof of the target for given arguments must therefore be
supplied together with proofs of `B = B'`, `C = C'` and `x.1 = x'.1`, exactly
as for the source theorem. `set_option linter.unusedVariables false in` only
silences the linter warning about these three names. It does not change the
definition. The published Library uses the same option for the same reason,
for example in
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic.Statements`.

## The objects involved

All names below are published in the Library.

- `ClosedSubgroup G` is Mathlib's type of closed subgroups of the
  topological group `G`; `.toSubgroup` is the underlying subgroup.
- `extensionSubgroup B C h`
  (`Langlands.NYLL.CyclicCohomology.extensionSubgroup`, source M004.002) is
  the abbreviation `C.toSubgroup.subgroupOf B.toSubgroup`: `C` viewed as a
  subgroup of `B`. The proof `h` does not change the subgroup. The quotient
  `B.toSubgroup ⧸ extensionSubgroup B C h` is the type of left cosets of `C`
  in `B`, and `Finite` is Mathlib's class of types with finitely many
  elements.
- `ambientFixedAddSubgroup A H`
  (`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`, source M023.001)
  is the additive subgroup of `A.V` of the elements fixed by every element of
  `H`. For `x` in it, `x.1` is its underlying element of `A.V`.
- `relativeNorm A K L hLK`
  (`Langlands.NYLL.ClassFormation.relativeNorm`, source M024.009) is the
  additive homomorphism from the `L`-fixed elements to the `K`-fixed elements
  that sums the coset translates. It requires the instance
  `[Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]`. Because
  `extensionSubgroup` is an abbreviation for that `subgroupOf`, the
  instance binders `hfinite` and `hfinite'` of the target supply it.

Both sides of the equation are coerced twice: from the homomorphism value in
`ambientFixedAddSubgroup A B` (respectively `B'`) to `A.V`. The comparison
takes place in `A.V`, where the two sides have the same type even before the
equalities `B = B'` and `C = C'` are used.

## Source and binders

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean),
SHA-256 `f4529e6c10db2c36c8c1dd88506cb999bd030618c1800f1d1ab96ab604e5f4fd`.
The relevant lines are:

- the namespace and opens, lines 21–28: `namespace LocalClassFieldTheory`,
  `open RamificationTheory CyclicCohomology KummerTheory ClassFormation`,
  `open LocalFieldTheory`, `noncomputable section`;
- `open scoped ValuativeRel` and the file-level section variables
  `(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]`,
  lines 30–32;
- M166.001: the docstring at lines 34–37 and the theorem at lines 38–63. Its
  binders and type are at lines 38–54; the proof at lines 55–63 is omitted.

The theorem's binders are exactly the binders of the target, unchanged and
in the source order, including the names `hfinite` and `hfinite'` of the two
instance binders. The section variables `K`, `Ω` and their instances occur
neither in the binders nor in the type of the theorem, so Lean does not
include them in the source theorem. The target does not take them either.

The acting group `G` is in `Type` (universe 0), as in the source and as the
published `relativeNorm` requires. The representation `A : Rep ℤ G` has an
arbitrary carrier universe. As for the published `relativeNorm`, the target
therefore has exactly one universe parameter, the automatically named
`u_1`, for that carrier. The source theorem has the same universe parameter.

## Declaration map

The Library's `notes/errata/` has no NYLL entry. Row M166.001 of the
published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves the adapted name without the `Statement` suffix for the proof. No
declaration of the target name exists in the current Library or Mathlib.

| Original declaration | Adapted declaration |
| --- | --- |
| theorem `LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq` (M166.001), type only | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eqStatement` (this module) |
| `ClassFormation.relativeNorm` (M024.009, used) | `Langlands.NYLL.ClassFormation.relativeNorm` (published) |
| `KummerTheory.ambientFixedAddSubgroup` (M023.001, used) | `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (published) |
| `CyclicCohomology.extensionSubgroup` (M004.002, used) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (published) |

## Imports and modification record

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`,
  defining `relativeNorm`. Through it come `ambientFixedAddSubgroup`,
  Mathlib's `Rep` and `ClosedSubgroup`;
- `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  defining `extensionSubgroup`.

These replace the source's three NYLL imports (`AbstractFixedFieldUnits`,
`HenselianValuationBase` and `SeparableFixedFieldNorm`). Every transitive
import lies in the approved Mathlib environment or the published Library.

Worker 85 extracted this statement on 14 November 2026. The Lean header
records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`, and the suffix `Statement` is
  added to the name;
- the theorem becomes a Prop-valued definition whose binders are the
  theorem's binders and whose body is the theorem's type;
- `set_option linter.unusedVariables false in` is added before the
  definition, as explained above;
- the proof is omitted; it belongs to a later proof;
- of the source's opens, `CyclicCohomology`, `KummerTheory` and
  `ClassFormation` are kept, as one `open` line. Inside the new namespace
  they resolve to the `Langlands.NYLL` namespaces that supply
  `extensionSubgroup`, `ambientFixedAddSubgroup` and `relativeNorm`. The
  other opened namespaces (`RamificationTheory`, `LocalFieldTheory`, scoped
  `ValuativeRel`), the `noncomputable section` and the section variables
  provide nothing this statement uses;
- the imports are replaced as described above.

The proposition is unchanged. Every other source declaration is omitted. No
theorem, instance, notation or alias is introduced.

## Checks

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports the target
as a definition with the single level parameter `u_1` whose type returns
`Prop`, using only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

A private probe, not part of this module, also compiled with zero errors and
zero warnings. In it the source proof, preceded by `unfold` of the target,
proves the target: it substitutes `B'`, `C'`, the containment proof, the
finiteness instance and `x'`, then closes the goal by `rfl`. This development
check is not independent acceptance.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. Worker 85
adapted this unit directly from the pinned original; no other project
worker supplied code.
