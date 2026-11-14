# Cosets of the base fixing subgroup as embeddings: finiteness and coset-action targets (M165.006, M165.008)

Let `Ω / K` be a Galois extension and `E` an intermediate field. Write
`G = Gal(Ω / K)` and `H = Gal(Ω / E)` for the subgroup of automorphisms
fixing `E` pointwise. This module states, without proofs, two facts from the
source file about the left cosets `G / H`:

- `baseFixingExtensionQuotient_finite_of_isSeparableStatement K Ω E`
  (source instance M165.006): if `Ω` is separably closed and `E` is
  finite-dimensional and separable over `K`, then `G / H` is finite.
- `relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement K Ω E x q`
  (source theorem M165.008): for a unit `x ∈ Eˣ` and a coset `q = σH`, the
  abstract class-formation coset action of `q` on `x`, viewed in `Ω`, equals
  `σ|_E (x)`. Here `σ|_E` is the `K`-embedding of `E` into `Ω` attached to
  `q`. This holds for every intermediate field `E`, with no finiteness,
  separability or separable-closedness hypothesis.

Both are Prop-valued definitions in the namespace
`Langlands.NYLL.LocalClassFieldTheory`. They are targets for later proofs.

## The Lean statements

```lean
namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

abbrev baseFixingExtensionQuotient_finite_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] : Prop :=
  Finite
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E))

def relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω)
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) : Prop :=
  ((Additive.toMul
    (relativeCosetAction (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x)) q) : Ωˣ) : Ω) =
    baseFixingCosetToAlgHom K Ω E q (x : E)
```

## The objects involved

All names below are published in the Library.

- `closedFixingSubgroup K Ω F`
  (`Langlands.NYLL.RamificationTheory.closedFixingSubgroup`, source M087.001)
  is the closed subgroup of `Gal(Ω / K)` whose underlying subgroup is
  Mathlib's `IntermediateField.fixingSubgroup F`. For `F = ⊥` its
  `.toSubgroup` is all of `G`, presented as a subgroup. For `F = E` it is
  `H`.
- `extensionSubgroup B C h`
  (`Langlands.NYLL.CyclicCohomology.extensionSubgroup`, source M004.002) is
  the abbreviation `C.toSubgroup.subgroupOf B.toSubgroup`: `H` viewed as a
  subgroup of the subgroup `G`. The containment proof `h` is the published
  theorem `fixingSubgroupLeBase K Ω E` (source M089.002). Because it is a
  proof, it does not change the subgroup.
- `⧸` is Mathlib's quotient by a subgroup. Its elements are left cosets: by
  `QuotientGroup.leftRel_apply`, `σ` and `τ` are identified exactly when
  `σ⁻¹ * τ` lies in the subgroup. `Finite` is Mathlib's class of types with
  finitely many elements.
- `galoisAmbientUnitsRep K Ω` (source M088.001) is the abbreviation for
  Mathlib's `Rep.ofAlgebraAutOnUnits K Ω`, the integral representation
  `Rep.ofMulDistribMulAction (Ω ≃ₐ[K] Ω) Ωˣ` of `Gal(Ω / K)` on the units of
  `Ω`, written additively: `σ` acts by `u ↦ σ(u)`.
- `intermediateFieldUnitsEquivGaloisFixed K Ω E` (source M088.006) is the
  additive equivalence from `Additive Eˣ` to the `H`-fixed part of that
  representation, `ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
  (closedFixingSubgroup K Ω E)`. It sends `x` to `x` viewed as a unit of
  `Ω`.
- `relativeCosetAction A B C h a q`
  (`Langlands.NYLL.ClassFormation.relativeCosetAction`, source M024.001) is
  the action of a left coset `q = bC` of `C` in `B` on a `C`-fixed element
  `a` of the representation `A`. It is `A.ρ b a`, which does not depend on
  the representative `b`.
- `baseFixingCosetToAlgHom K Ω E`
  (`Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom`, source
  M165.001) sends the left coset of `σ` to `σ.1.toAlgHom.comp E.val`, the
  restriction of `σ` to `E` as a `K`-algebra map `E →ₐ[K] Ω`.

The left side of the M165.008 equation starts from `x : Eˣ`. It applies
`Additive.ofMul`, the equivalence `intermediateFieldUnitsEquivGaloisFixed`
and the coset action of `q`. This gives an element of `Additive Ωˣ`. Then
`Additive.toMul` and the two coercions return the underlying element of
`Ω`. The right side applies the embedding attached to `q` to the element
`(x : E)` of `E`.

## Source and binders

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean),
SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`.
The relevant lines are:

- the namespace and opens, lines 23–34: `namespace LocalClassFieldTheory`,
  `open RamificationTheory KummerTheory`, `open LocalFieldTheory`,
  `open ClassFormation CyclicCohomology`, `noncomputable section`,
  `open scoped BigOperators`;
- the file-level section variables, lines 36–37:
  `(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]`;
- M165.006: in `section CosetsAndEmbeddings` (line 39) with section variable
  `(E : IntermediateField K Ω)` (line 41), the docstring at line 154 and the
  instance at lines 155–162. Its binders and type are at lines 155–161; the
  body at line 162 is omitted;
- M165.008: in `section NormAsProduct` (line 166), with section variables
  `(E : IntermediateField K Ω) [FiniteDimensional K E] [Algebra.IsSeparable K E]`
  (lines 175–176), the line
  `omit [IsSepClosed Ω] [FiniteDimensional K E] [Algebra.IsSeparable K E] in`
  (line 178), the docstring at lines 179–180 and the theorem at lines
  181–197. Its binders and type are at lines 181–194; the proof at lines
  195–197 is omitted.

Each target takes, as explicit binders in the source order, exactly the
section variables that the source declaration receives:

- M165.006 is an instance whose binders are the section variables
  `K`, `Ω`, `[Field K]`, `[Field Ω]`, `[Algebra K Ω]`, `[IsGalois K Ω]`,
  `[IsSepClosed Ω]`, `E` and its own binders `[FiniteDimensional K E]`
  `[Algebra.IsSeparable K E]`. Its proof uses the equivalence
  `baseFixingCosetEquivAlgHom`, which needs `[IsSepClosed Ω]` and both
  instances on `E`. `[IsGalois K Ω]` is an argument of
  `closedFixingSubgroup`. So the instance takes all of them, and so does the
  target.
- M165.008 omits `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
  `[Algebra.IsSeparable K E]` by the `omit ... in` line. The target takes
  the remaining section variables `K`, `Ω`, `[Field K]`, `[Field Ω]`,
  `[Algebra K Ω]`, `[IsGalois K Ω]`, `E`, followed by the theorem's own
  binders `x` and `q`. The local instance `finiteSeparableAlgHomFintype`
  (M165.007, line 168) is in scope at the source theorem, but its type does
  not occur in the statement.

The fields are in `Type` (universe 0), as in the source; neither target has
a universe parameter.

M165.006 is published as an `abbrev`, a reducible definition. A later proof
`theorem baseFixingExtensionQuotient_finite_of_isSeparable ... :
baseFixingExtensionQuotient_finite_of_isSeparableStatement K Ω E` can then
be registered with `attribute [instance]`, because instance search unfolds
the abbreviation to the `Finite` class. This follows the published precedent
`finiteGaloisExtensionSubgroup_normalStatement` (module
`...FiniteGaloisRealization.Normality.Statements`). The source uses this
instance when it forms the relative norm in M165.009, whose `relativeNorm`
requires the `Finite` instance on the coset space. M165.008 is an ordinary
theorem and is published as a `def`.

## Declaration map

The Library's `notes/errata/` has no NYLL entry. Rows M165.006 and M165.008
of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserve the adapted names without the `Statement` suffix for the proofs. No
declaration of either target name exists in the current Library or
Mathlib.

| Original declaration | Adapted declaration |
| --- | --- |
| instance `LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable` (M165.006), type only | `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparableStatement` (this module) |
| theorem `LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable` (M165.008), type only | `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement` (this module) |
| `LocalClassFieldTheory.baseFixingCosetToAlgHom` (M165.001, used) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom` (published) |
| `LocalClassFieldTheory.galoisAmbientUnitsRep` (M088.001, used) | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep` (published) |
| `LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` (M088.006, used) | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` (published) |
| `ClassFormation.relativeCosetAction` (M024.001, used) | `Langlands.NYLL.ClassFormation.relativeCosetAction` (published) |
| `RamificationTheory.closedFixingSubgroup` (M087.001, used) | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (published) |
| `CyclicCohomology.extensionSubgroup` (M004.002, used) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (published) |
| `LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002, used) | `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (published) |

## Imports and modification record

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Definitions`,
  defining `baseFixingCosetToAlgHom`. Through it come `closedFixingSubgroup`,
  `extensionSubgroup`, `fixingSubgroupLeBase` and Mathlib's `IsSepClosed`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions`,
  defining `intermediateFieldUnitsEquivGaloisFixed`. Through it comes
  `galoisAmbientUnitsRep`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions`,
  defining `relativeCosetAction`.

These replace the source's NYLL imports (`SeparableNormProduct` and
`SeparableUnitsNorm`) and its Mathlib import
`Mathlib.FieldTheory.PrimitiveElement`, which reaches this module through the
first import. Every transitive import lies in the approved Mathlib
environment or the published Library.

Worker 85 extracted these two statements on 14 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`, and the suffix `Statement` is
  added to each name;
- each source declaration becomes a Prop-valued definition whose body is the
  source type, with its section variables as explicit binders as described
  above. The instance target is an `abbrev`, the theorem target a `def`;
- the proofs, the instance registration and the `noncomputable` modifier of
  M165.006 are omitted; they belong to later proofs;
- of the source's opens, only `RamificationTheory`, `CyclicCohomology` and
  `ClassFormation` are kept, as one `open` line. Inside the new namespace
  they resolve to the `Langlands.NYLL` namespaces that supply
  `closedFixingSubgroup`, `extensionSubgroup` and `relativeCosetAction`. The
  other opened namespaces (`KummerTheory`, `LocalFieldTheory`, scoped
  `BigOperators`), the `noncomputable section` and the two sections provide
  nothing these statements use;
- the imports are replaced as described above.

The propositions are unchanged. Every other source declaration is omitted,
including the local instance M165.007 and the theorems M165.009 and M165.010.
No theorem, instance, notation or alias is introduced.

## Checks

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports each target
as a definition with no level parameters whose type returns `Prop`, using only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

A private probe, not part of this module, also compiled with zero errors. In
it the source proofs, adapted to the published names, prove both targets. For
M165.006 the proof is `Equiv.finite_iff` applied to the equivalence built from
the published `PortInternal.M165.d003` and `d004`, with Mathlib's finiteness
of `E →ₐ[K] Ω`. For M165.008 it is `Quotient.inductionOn'` followed by
`rfl`. Registering the M165.006 proof as an instance then let the M165.009
statement, which uses `relativeNorm`, elaborate. These development checks are
not independent acceptance.

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
adapted these units directly from the pinned original; no other project
worker supplied code.
