# Native norm subgroup transport and containment targets

This pair defines the two proposition targets M300.008 and M300.009. It
contains no proof of either target.

## Source and attribution

The source is Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`.
The retained original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`;
its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original Apache-2.0 copyright and author header is preserved. The
unchanged shared notices are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
Worker 538 performed this focused statement adaptation.

## Declaration map

Every original name below has prefix `LocalClassFieldTheory.`; every
adapted name has prefix `Langlands.NYLL.LocalClassFieldTheory.`.

| Unit | Original name and lines | Adapted name |
| --- | --- | --- |
| M300.008 | `map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup`, 236–301 (type 236–241) | `map_finiteAbelianNormSubgroup_eq_additiveNormSubgroupStatement` |
| M300.009 | `finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map`, 305–329 (type 305–312) | `finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_mapStatement` |

Both inherit the source's noncomputable section, namespace and explicit
`(K : Type) [Field K]` at lines 25–32. In particular, `K` is in universe
zero. Each retains explicit
`(L : ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K))`.
M300.009 then retains explicit `(H : Subgroup Kˣ)` followed by the explicit
proof argument `h` with its complete source type. The local-field section
starts only at source lines 331–334 and supplies no parameters to these
two declarations.

## Exact propositions

M300.008 states equality of additive subgroups of `Additive Kˣ`:

```lean
(L.normSubgroup (intrinsicAbsoluteUnits K)).map
  (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
  additiveNormSubgroup K
    (abstractFixedField K (SeparableClosure K) L.field)
```

Here `L.field` is the actual closed subgroup stored in the finite-abelian
package. Its represented field is the actual intermediate fixed field in
`SeparableClosure K`. On the left, `L.normSubgroup` is the abstract norm
image in the units fixed by the intrinsic base subgroup. The map uses the
inverse of the published base-unit additive equivalence. On the right,
`CyclicCohomology.additiveNormSubgroup` is the additive form of
`LocalFieldTheory.localNormSubgroup`, the range of the actual unit norm.
There is no replacement by a supplied equality or arbitrary subgroup.

M300.009 takes the explicit source premise

```lean
(h : L.normSubgroup (intrinsicAbsoluteUnits K) ≤
  H.toAddSubgroup.map
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom)
```

and returns the proposition `finiteAbelianNormSubgroup K L ≤ H`, using
the native multiplicative subgroup of `Kˣ`. The argument `h` is retained
in the definition's telescope even though the proposition body does not
refer to its proof term. A later proof must accept that argument; this
target does not assert containment without the premise.

Neither target adds a finite-dimensional, Galois, valuation, topology,
local-field or supplied norm-identity hypothesis. Such structures used
inside the original proof of M300.008 are not source statement parameters
and do not enter these targets.

## Reused interfaces

All following names are in `Langlands.NYLL`.

| Reused name | Source correspondence and role |
| --- | --- |
| `ClassFormation.FiniteAbelianSubextension`, `.field` | M296.001–.002, `AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:44–56`; the actual package and its closed subgroup |
| `ClassFormation.FiniteAbelianSubextension.normSubgroup` | M296.030, the same source file, 415–419; the actual `finiteNormSubgroup` with packaged quotient finiteness supplied locally |
| `LocalClassFieldTheory.intrinsicAbsoluteUnits`, `.intrinsicAbstractBase` | M091.002–.003, `LocalReciprocity/IntrinsicAbsoluteData.lean:32–45`; chosen separable-closure unit representation and intrinsic base subgroup |
| `LocalClassFieldTheory.abstractFixedField` | M099.001, `LocalReciprocity/FiniteAbstractFixedField.lean:34–36`; actual intermediate fixed field |
| `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` | M096.001, `LocalReciprocity/SeparableUnitsNorm.lean:41–50`; base units identified with units fixed by the bottom-field fixing subgroup |
| `CyclicCohomology.additiveNormSubgroup` | M095.008, `GaloisCohomology/Cyclic/TateH0/NormImage.lean:119–121`; additive form of the actual native norm range |
| `LocalClassFieldTheory.finiteAbelianNormSubgroup` | M300.003, `NormSubgroupOrderEmbedding.lean:79–81`; native norm subgroup of the represented fixed field |

Mathlib's `SeparableClosure`, `Subgroup.toAddSubgroup`, `AddSubgroup.map`
and additive equivalence homomorphisms are reused directly. The targets
introduce no data constructions or global instances. The imported
interfaces retain their existing instance scopes.

## Modification record

1. Extract only source theorem types 236–241 and 305–312, retaining their
   complete inherited telescope. Replace `theorem` by `def`, append
   `Statement` and make the result type explicitly `Prop`. Omit both source
   proofs.
2. Prefix the namespace with `Langlands.NYLL`. Qualify
   `ClassFormation.FiniteAbelianSubextension` explicitly, preserving the
   same source object and argument order.
3. Replace the source module's broad NYLL and Mathlib imports with focused
   imports supplying the reused norm data, native norm definition,
   base-unit equivalence and additive norm definition. Do not import the
   upstream repository.
4. Retain `open CyclicCohomology`, which resolves `additiveNormSubgroup`.
   Omit the unused source openings of `LocalFieldTheory`,
   `RamificationTheory`, `KummerTheory` and `ClassFormation`; referenced
   package names are qualified. Preserve the noncomputable section.
5. Replace the whole-module description and proof-asserting declaration
   docstrings with descriptions of these proposition targets. Retain the
   original copyright and author header and shared license notices.

No mathematical hypothesis, bound universe, map orientation, subgroup,
fixed field or conclusion is changed. The original arguments identify
norm-map ranges and transport containment; those proofs remain separate
from this statement pair.

## Development validation

Both exact declarations compile and inspect as proposition-valued definitions
in approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`. The elaborated
telescopes retain universe-zero `K`, its field instance and explicit `L`;
M300.009 also retains explicit `H` and the source containment proof `h`.
The entry module reports the expected unused-variable warning for `h`, whose
name and binder are intentionally preserved. These development checks establish
neither a proof of either target nor independent acceptance.
