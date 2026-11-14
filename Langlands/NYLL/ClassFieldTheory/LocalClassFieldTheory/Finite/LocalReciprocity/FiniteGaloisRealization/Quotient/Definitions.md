# The abstract quotient of an embedded finite Galois extension

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`
(file SHA-256 `c3681d1d4a2363fb2b1a28fb984b458e8051e97c30c3d4ec66bc43608b1f44b2`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The source
file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M090.009 | def `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` (docstring 111–112, definition 113–127) | `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` |

The original name is in the source namespace `LocalClassFieldTheory`; the
adapted name is
`Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`.

The unit lies in the dependency closure of Task 5264 but was not routed to any
task. Worker 5264, who routes that closure, agreed that Task 5799 stages it.
It is a prerequisite of Task 5799 units in `FixedFieldIntrinsicReciprocity`,
for example M274.005.

## Parameters and type

The definition sits under the source section variables of lines 32–33,

```lean
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
```

and takes the source binder `(i : L →ₐ[K] SeparableClosure K)`. All fields are
in `Type` (universe zero), as in the source. The definition does not use
`[FiniteDimensional K L]`, so Lean does not include it as an argument; the
elaborated type, printed by `#check` in a private check, is

```lean
finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    (closedFixingSubgroup K (SeparableClosure K) ⊥).toSubgroup ⧸
        extensionSubgroup (closedFixingSubgroup K (SeparableClosure K) ⊥)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i)) ≃*
      Gal(L / K)
```

The source elaborates under the same rule, so its elaborated type has the same
binders.

## Content

Write `Ω := SeparableClosure K`, `E := finiteGaloisFieldRangeOfEmbedding K L i`
(the field range of `i`, an intermediate field of `Ω / K`),
`G₀ := closedFixingSubgroup K Ω ⊥` and
`G_E := finiteGaloisClosedFixingSubgroupOfEmbedding K L i`, which unfolds to
`closedFixingSubgroup K Ω E`. The domain is the quotient of `G₀` by the
extension subgroup of `G_E` in `G₀`, that is, `G_E` viewed as a subgroup of
`G₀` (via the inclusion `fixingSubgroupLeBase K Ω E : G_E ≤ G₀`).

The quotient is a group because that extension subgroup is normal. Lean finds
this normality from the published instance
`finiteGaloisExtensionSubgroupOfEmbedding_normal` (M090.006); a private
`#synth` check confirmed that this instance is the one found. It is the
instance that the source uses, by the same name, from the same source file.

The definition is the composite of two multiplicative equivalences:

1. `baseFixingExtensionQuotientEquivGaloisGroup K Ω E` (M089.011) identifies
   the quotient of `G₀` by the extension subgroup of
   `closedFixingSubgroup K Ω E` with `Gal(E / K)`. Its domain is the domain
   above after unfolding `G_E`.
2. The inverse of `AlgEquiv.autCongr (finiteGaloisFieldRangeEquivOfEmbedding K L i)`
   identifies `Gal(E / K)` with `Gal(L / K)`, where
   `finiteGaloisFieldRangeEquivOfEmbedding K L i : L ≃ₐ[K] E` (M090.002) is the
   isomorphism of `L` onto its field range. The instance `IsGalois K E` used by
   step 1 is the published instance `finiteGaloisFieldRangeOfEmbedding_isGalois`
   (M090.003).

The body is copied from the source without change.

Published components used, all by their Library names:

- `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding`
  (M090.001), `finiteGaloisFieldRangeEquivOfEmbedding` (M090.002), the instance
  `finiteGaloisFieldRangeOfEmbedding_isGalois` (M090.003) and
  `finiteGaloisClosedFixingSubgroupOfEmbedding` (M090.005), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Realization.Definitions`;
- the instance `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal`
  (M090.006), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Normality.U006.Proofs`.
  There it is a theorem whose type is the published target
  `finiteGaloisExtensionSubgroupOfEmbedding_normalStatement` (module
  `FiniteGaloisRealization/Normality/Statements`), registered with
  `attribute [instance]`;
- `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotientEquivGaloisGroup`
  (M089.011), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions`;
- through these modules, `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`,
  `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002) and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002).

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The definition is placed in its own file `FiniteGaloisRealization/Quotient/Definitions`.
- The source imports `Mathlib.SetTheory.Cardinal.Finite`,
  `Mathlib.FieldTheory.SeparableClosure` and the broad NYLL modules
  `AlgebraicNumberTheory.SeparableClosureEmbedding` and
  `GaloisExtensionQuotient` (lines 7–10). The port imports the three published
  modules listed above, which supply every declaration the definition uses.
- The source opens `RamificationTheory CyclicCohomology KummerTheory`
  (line 26). The port opens `RamificationTheory CyclicCohomology`.
  `KummerTheory` is not used by this definition.
- The docstring, the keyword `def`, the section variables, the binder, the
  result type and the body are copied from source lines 32–33 and 111–127
  without change, inside the source's `noncomputable section` (line 30).
- No other declaration of the source module is included. The other source
  declarations that this definition uses are the published ones listed above.

## Library and Mathlib comparison

A search of the Library `.lean` files at commit
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86` found no declaration named
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`. Within
`Langlands/NYLL`, the only uses of `baseFixingExtensionQuotientEquivGaloisGroup`
or `finiteGaloisFieldRangeEquivOfEmbedding` are in their defining modules, in
the published instance `baseFixingExtensionQuotient_finite` (M096.003,
`SeparableUnitsNorm/Finite/Definitions`, a finiteness proof) and in the
statements module `SeparableUnitsNorm/BaseUnits/Statements`. None of them
identifies the extension quotient of an embedded finite Galois extension with
`Gal(L / K)`.

Outside `Langlands/NYLL`, the related declarations are
`Langlands.Weil.Local.finiteGaloisQuotientKernelEquiv`
(`Langlands/Weil/Local/FiniteGaloisQuotient.lean`), which identifies the
local Weil group of a `p`-adic extension with the kernel of a finite Galois
quotient map and is not a statement about Galois-group quotients, and uses of Mathlib's
`InfiniteGalois.normalAutEquivQuotient` and `IsGalois.normalAutEquivQuotient`
inside proofs and definitions about other groups. Mathlib's
`InfiniteGalois.normalAutEquivQuotient` identifies `Gal(Ω / K)` modulo a
closed normal subgroup with the Galois group of its fixed field; it is used
inside the body of M089.011, but it is not stated for the quotient of `G₀` by
an extension subgroup, and Mathlib has no class-formation extension subgroups.

The original copyright and author header is retained in the Lean file,
followed by a dated modification record. Apache-2.0 attribution and notices
are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
