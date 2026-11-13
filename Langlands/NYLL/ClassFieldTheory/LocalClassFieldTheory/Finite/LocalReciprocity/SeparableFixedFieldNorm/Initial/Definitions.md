# Cosets of the base fixing subgroup as embeddings: the restriction map (M165.001)

Let `Ω / K` be a Galois extension and `E` an intermediate field. The
Galois group `Gal(Ω / K)` contains the subgroup `Gal(Ω / E)` of
automorphisms fixing `E` pointwise. Every `σ ∈ Gal(Ω / K)` restricts to a
`K`-embedding `σ|_E : E → Ω`, and two automorphisms in the same left coset
`σ · Gal(Ω / E)` have the same restriction. This module defines the
resulting map from left cosets to embeddings:

- `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom K Ω E`
  sends the left coset of `σ` to `σ|_E`.

In Lean:

```lean
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

variable (E : IntermediateField K Ω)

def baseFixingCosetToAlgHom :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) →
      (E →ₐ[K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => σ.1.toAlgHom.comp E.val)
    (by ...)  -- the source's well-definedness proof, unchanged
```

The Lean file contains the complete body.

## The objects involved

The domain is written with the abstract class-formation names that the
source uses. The quotient is of the following group by the following
subgroup:

- `closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)` is the published
  `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (source unit
  M087.001, module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`).
  For an intermediate field `F` it is the closed subgroup of `Gal(Ω / K)`
  whose underlying subgroup is Mathlib's `IntermediateField.fixingSubgroup F`.
  For `F = ⊥` every automorphism fixes `F`, so the underlying subgroup
  `.toSubgroup` is all of `Gal(Ω / K)`, presented as a subgroup. The quotient's
  ambient group is the type of its elements, pairs `⟨σ, h⟩` with
  `σ : Gal(Ω / K)` and a membership proof `h`.
- `extensionSubgroup G_⊥ G_E h` is the published
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (source unit M004.002,
  module
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`),
  the abbreviation `G_E.toSubgroup.subgroupOf G_⊥.toSubgroup`. Here it is
  `Gal(Ω / E)` viewed as a subgroup of the subgroup above.
- `fixingSubgroupLeBase K Ω E` is the published theorem
  `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (source unit
  M089.002, module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs`).
  Its type is the published target
  `fixingSubgroupLeBaseStatement K Ω E`, which unfolds to
  `(closedFixingSubgroup K Ω E).toSubgroup ≤ (closedFixingSubgroup K Ω ⊥).toSubgroup`.
  This is the containment argument that `extensionSubgroup` requires. Because
  it is a proof, it does not change the subgroup.

`⧸` is Mathlib's quotient by a subgroup, whose elements are left cosets: by
`QuotientGroup.leftRel_apply`, `σ` and `τ` are identified exactly when
`σ⁻¹ * τ` lies in the subgroup. The codomain `E →ₐ[K] Ω` is the type of
`K`-algebra homomorphisms from `E` to `Ω`.

The body is `Quotient.liftOn'` of the map
`σ ↦ σ.1.toAlgHom.comp E.val`, the automorphism `σ.1 : Ω ≃ₐ[K] Ω` composed
with the inclusion `E.val : E →ₐ[K] Ω`. The source proof that this respects
the relation is kept unchanged. If `σ⁻¹ * τ` fixes `E`, write
`τ = σ · η` with `η ∈ Gal(Ω / E)`. Then `σ x = σ (η x) = τ x` for every
`x ∈ E`, so the two restrictions agree.

## Section variables and binders

The section variables are those of the source, unchanged:
`(K Ω : Type)`, then `[Field K]`, `[Field Ω]`, `[Algebra K Ω]`,
`[IsGalois K Ω]`, `[IsSepClosed Ω]`, then `(E : IntermediateField K Ω)`.
The fields are in `Type` (universe 0), as in the source; the declaration has
no universe parameter.

Lean adds a section variable to a definition only when the definition uses
it. `[IsSepClosed Ω]` is not used by this body, so `baseFixingCosetToAlgHom`
takes the arguments `K`, `Ω`, `[Field K]`, `[Field Ω]`, `[Algebra K Ω]`,
`[IsGalois K Ω]` and `E`, and no separable-closedness argument. The source
relies on this too: its theorem `baseFixingCosetToAlgHom_mk` (source line 81)
and its injectivity theorem (source line 119) state facts about this map
under `omit [IsSepClosed Ω] in`. In the port, the companion statement target
`Langlands.NYLL.PortInternal.M165.d004Statement` applies the map with no
`IsSepClosed` instance in scope and compiles. `[IsGalois K Ω]` is used: it is
an argument of `closedFixingSubgroup`.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean),
SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`.
The relevant lines are:

- the namespace and opens, lines 23–34: `namespace LocalClassFieldTheory`,
  `open RamificationTheory KummerTheory`, `open LocalFieldTheory`,
  `open ClassFormation CyclicCohomology`, `noncomputable section`,
  `open scoped BigOperators`;
- the section variables, lines 36–37 and 41 (the latter inside
  `section CosetsAndEmbeddings`, line 39);
- M165.001: docstring at lines 43–44, definition at lines 45–79.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.baseFixingCosetToAlgHom` (M165.001) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom` (this module) |
| `RamificationTheory.closedFixingSubgroup` (M087.001, used) | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (published) |
| `CyclicCohomology.extensionSubgroup` (M004.002, used) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (published) |
| `LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002, used) | `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (published) |

Row M165.001 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves the adapted name. No declaration of that name exists in the current
Library or Mathlib.

## Imports and modification record

The direct imports are:

- `Mathlib.FieldTheory.PrimitiveElement`, the source's Mathlib import;
- `Mathlib.FieldTheory.IsSepClosed`, for the class `IsSepClosed` in the
  section variables. The source receives it through its NYLL imports;
- `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`,
  defining `closedFixingSubgroup`;
- `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  defining `extensionSubgroup`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs`,
  proving `fixingSubgroupLeBase`.

These replace the source's two NYLL imports (`SeparableNormProduct` and
`SeparableUnitsNorm`). Through them the source definition receives only the
three NYLL declarations listed in the table above; it uses nothing else from
them. Every transitive import lies in the approved Mathlib environment or the
published Library.

Worker 85 extracted this one source definition on 13 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the imports are replaced as described above;
- of the source's opens, only `RamificationTheory` and `CyclicCohomology` are
  kept, as one `open` line. Inside the new namespace they resolve to
  `Langlands.NYLL.RamificationTheory` and `Langlands.NYLL.CyclicCohomology`,
  which supply `closedFixingSubgroup` and `extensionSubgroup`. The other
  opened namespaces (`KummerTheory`, `LocalFieldTheory`, `ClassFormation`,
  scoped `BigOperators`) provide nothing this definition uses.

The section variables, the section `CosetsAndEmbeddings`, the
`noncomputable section`, the docstring, the type and the body, including its
proof, are unchanged. Every other source declaration is omitted: the `@[simp]`
lemma M165.002 `baseFixingCosetToAlgHom_mk`, the private theorems M165.003
and M165.004 (whose statements are the targets
`Langlands.NYLL.PortInternal.M165.d003Statement` and `d004Statement` in the
sibling module `Statements`), the equivalence M165.005, the instance M165.006
and the norm comparison results M165.007–M165.010. No theorem, instance,
notation or alias is introduced.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of
`baseFixingCosetToAlgHom` reports a definition with no level parameters and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
This development check is not independent acceptance.

## Use downstream

For a finite separable `E`, the source shows that this map is a bijection
(M165.003/.004), packages it as the equivalence `baseFixingCosetEquivAlgHom`
(M165.005) and deduces finiteness of the coset space (M165.006). It then uses
the equivalence to compare the abstract class-formation coset norm with the
ordinary field norm for intermediate fields that need not be normal
(M165.008–M165.010).

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 85 adapted this unit directly from the
pinned original; no other project worker supplied code.
