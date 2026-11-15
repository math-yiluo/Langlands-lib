# The class-formation norm from a finite separable intermediate field is the field norm: target (M165.009)

Let `Ω / K` be a Galois extension with `Ω` separably closed, and let `E` be
an intermediate field that is finite-dimensional and separable over `K`.
`E / K` need not be normal. Write `G = Gal(Ω / K)` and `H = Gal(Ω / E)` for
the subgroup of automorphisms fixing `E` pointwise. This module states,
without proof, the source theorem M165.009:

- `relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement K Ω E x`:
  for a unit `x ∈ Eˣ`, the abstract class-formation norm of `x` from `H` to
  `G`, viewed in `Ω`, equals `N_{E/K}(x)` viewed in `Ω`. The abstract norm
  is the product of the coset actions of `x` over all left cosets `σH` of
  `H` in `G`. `N_{E/K}` is Mathlib's field norm `Algebra.norm K`.

It is a Prop-valued definition in the namespace
`Langlands.NYLL.LocalClassFieldTheory`, a target for a later proof.

## The Lean statement

```lean
namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

def relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (x : Eˣ) : Prop :=
  ((Additive.toMul
    ((relativeNorm (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
    algebraMap K Ω (Algebra.norm K (x : E))
```

## The objects involved

All names below are published in the Library or are in Mathlib.

- `closedFixingSubgroup K Ω F`
  (`Langlands.NYLL.RamificationTheory.closedFixingSubgroup`, source M087.001)
  is the closed subgroup of `Gal(Ω / K)` whose underlying subgroup is
  Mathlib's `IntermediateField.fixingSubgroup F`. For `F = ⊥` its
  `.toSubgroup` is all of `G`, presented as a subgroup. For `F = E` it is
  `H`.
- `fixingSubgroupLeBase K Ω E`
  (`Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase`, source
  M089.002) is the proof that `H ≤ G`. It is a proof, so it does not change
  any value.
- `galoisAmbientUnitsRep K Ω`
  (`Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`, source
  M088.001) is the abbreviation for Mathlib's `Rep.ofAlgebraAutOnUnits K Ω`,
  the integral representation `Rep.ofMulDistribMulAction (Ω ≃ₐ[K] Ω) Ωˣ` of
  `Gal(Ω / K)` on the units of `Ω`, written additively: `σ` acts by
  `u ↦ σ(u)`.
- `intermediateFieldUnitsEquivGaloisFixed K Ω E`
  (`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed`,
  source M088.006) is the additive equivalence from `Additive Eˣ` to the
  `H`-fixed part of that representation, `ambientFixedAddSubgroup
  (galoisAmbientUnitsRep K Ω) (closedFixingSubgroup K Ω E)`. It sends `x` to
  `x` viewed as a unit of `Ω`.
- `relativeNorm A B C h`
  (`Langlands.NYLL.ClassFormation.relativeNorm`, source M024.009) is the
  additive homomorphism from the `C`-fixed part to the `B`-fixed part of a
  representation `A`, for closed subgroups `C ≤ B` such that the left cosets
  `B / C` are finite. Its value on `a` is the published
  `relativeNormValue A B C h a` (source M024.005), the sum over all cosets
  `q` of `relativeCosetAction A B C h a q` (source M024.001); the coset
  action of `q = bC` on `a` is `A.ρ b a`, independent of the representative
  `b`. `.1` takes the underlying element of the representation module, here
  an element of `Additive Ωˣ`. Since the representation is written
  additively, the sum is the product of the units `σ(x)` over one `σ` in
  each coset `σH`.
- `relativeNorm` takes an instance argument
  `[Finite (B.toSubgroup ⧸ (C.toSubgroup.subgroupOf B.toSubgroup))]`. Here
  `C.toSubgroup.subgroupOf B.toSubgroup` is `H` viewed as a subgroup of `G`;
  the published `extensionSubgroup` (source M004.002) is the abbreviation for
  it. Instance search supplies the argument from the published instance
  `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable`
  (source M165.006, module
  `...SeparableFixedFieldNorm.U006.Proofs`, registered with
  `attribute [instance]`). That instance proves `G / H` finite exactly from
  `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
  `[Algebra.IsSeparable K E]`. As in the source, nothing else is needed. The
  argument is a proof of a proposition, so the choice of instance does not
  change the statement.
- `Algebra.norm K : E →* K` is Mathlib's field norm, the determinant of
  multiplication on `E` as a `K`-vector space. `algebraMap K Ω` is the
  structure map of `Ω` as a `K`-algebra.

The left side starts from `x : Eˣ`. It applies `Additive.ofMul`, the
equivalence `intermediateFieldUnitsEquivGaloisFixed` and the relative norm,
then takes `.1`. This gives an element of `Additive Ωˣ`. Then
`Additive.toMul` and the two coercions return the underlying element of
`Ω`. The right side is the field norm of `(x : E)`, mapped into `Ω`.

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
- `section NormAsProduct` (line 166), with the local instance
  `finiteSeparableAlgHomFintype` (M165.007, lines 168–173) and the section
  variables
  `(E : IntermediateField K Ω) [FiniteDimensional K E] [Algebra.IsSeparable K E]`
  (lines 175–176);
- M165.009: the docstring at lines 199–200 and the theorem at lines
  201–262. Its binder and type are at lines 201–208; the proof at lines
  209–262 is omitted.

Unlike M165.008 (line 178), M165.009 has no `omit ... in` line. The theorem
uses `K`, `Ω` and `E` and needs the `Finite` instance of `G / H`, which
depends on `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
`[Algebra.IsSeparable K E]`; `[IsGalois K Ω]` is an argument of
`closedFixingSubgroup`. So the theorem receives every section variable. The
target takes them as explicit binders in the source order, followed by the
theorem's own binder `x`. The local instance M165.007 is in scope at the
source theorem, but no `Fintype` of algebra maps occurs in the statement.
It is used only in the proof.

The fields are in `Type` (universe 0), as in the source; the target has no
universe parameter.

## Declaration map

The Library's `notes/errata/` has no NYLL entry. Row M165.009 of the
published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves the adapted name without the `Statement` suffix for the proof. No
declaration of the target name exists in the current Library or Mathlib.

| Original declaration | Adapted declaration |
| --- | --- |
| theorem `LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable` (M165.009), type only | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement` (this module) |
| instance `LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable` (M165.006, used by instance search) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable` (published proof, registered instance) |
| `ClassFormation.relativeNorm` (M024.009, used) | `Langlands.NYLL.ClassFormation.relativeNorm` (published) |
| `LocalClassFieldTheory.galoisAmbientUnitsRep` (M088.001, used) | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep` (published) |
| `LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` (M088.006, used) | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` (published) |
| `RamificationTheory.closedFixingSubgroup` (M087.001, used) | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (published) |
| `LocalClassFieldTheory.fixingSubgroupLeBase` (M089.002, used) | `Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` (published) |

## Imports and modification record

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U006.Proofs`,
  the published proof of M165.006, which registers the `Finite` instance
  above. Through it come `closedFixingSubgroup`, `extensionSubgroup`,
  `fixingSubgroupLeBase` and Mathlib's `IsSepClosed`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions`,
  defining `intermediateFieldUnitsEquivGaloisFixed`. Through it comes
  `galoisAmbientUnitsRep`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`,
  defining `relativeNorm`.

These replace the source's NYLL imports (`SeparableNormProduct` and
`SeparableUnitsNorm`) and its Mathlib import
`Mathlib.FieldTheory.PrimitiveElement`. `Algebra.norm` reaches this module
through these imports. Every transitive import lies in the approved Mathlib
environment or the published Library.

Worker 85 extracted this statement on 15 November 2026. The Lean header
records the change. The changes are:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`, and the suffix `Statement` is
  added to the name;
- the source theorem becomes a Prop-valued `def` whose body is the source
  type, with its section variables as explicit binders as described above;
- the proof is omitted; it belongs to a later proof;
- of the source's opens, only `RamificationTheory`, `CyclicCohomology` and
  `ClassFormation` are kept, as one `open` line. Inside the new namespace
  they resolve to the `Langlands.NYLL` namespaces that supply
  `closedFixingSubgroup` and `relativeNorm`. The other opened namespaces
  (`KummerTheory`, `LocalFieldTheory`, scoped `BigOperators`), the
  `noncomputable section` and the section provide nothing this statement
  uses;
- the local instance M165.007 is not reproduced, since the statement does
  not use it;
- the imports are replaced as described above.

The proposition is unchanged. Every other source declaration is omitted,
including M165.010. No theorem, instance, notation or alias is introduced.

## Checks

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) over Library commit
`0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`. Inspection reports the target as a
definition with no level parameters whose type returns `Prop`, using only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

A private probe, not part of this module, also compiled with zero errors and
zero warnings. In it the source proof (lines 209–262), adapted to the
published names, proves the target. Two changes were needed. The private
M165.007 instance is replaced by `attribute [local instance]` on the
published `Langlands.NYLL.PortInternal.M164.d001`, whose body is the same
`PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k F)`. And
`rw [relativeNormValue]` becomes `unfold relativeNormValue`. The proof then
uses the published proof of M165.008 for each coset and the published
`algebraMap_norm_eq_prod_embeddings_of_isSepClosed` (module
`...SeparableNormProduct.U003.Proofs`) to identify the product with the
field norm. These development checks are not independent acceptance.

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
