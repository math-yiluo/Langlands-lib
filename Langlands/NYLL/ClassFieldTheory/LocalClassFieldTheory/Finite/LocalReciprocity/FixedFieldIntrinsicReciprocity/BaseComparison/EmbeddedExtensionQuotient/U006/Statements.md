# Embedded extension quotients: values of the Galois group equivalence

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`. They are the statement phases of
source rows M274.006 and M274.007:

- `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement`, for the
  source theorem `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`;
- `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement`, for
  the source theorem `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither is proved here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`
and
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply`.

Both compute values of the published equivalence
`ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e` (source row
M274.005). That equivalence identifies a quotient of closed subgroups of
`Gal(SeparableClosure K / K)` with `Gal(E / F)`.

## Common parameters and local data

Both propositions universally quantify, in the source order,

```lean
(K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
  [FiniteDimensional K F] [Algebra.IsSeparable K F]
  [FiniteDimensional F E] [IsGalois F E]
  (j : E →ₐ[K] SeparableClosure K)
```

So `K ⊆ F ⊆ E` is a tower of fields in `Type` (universe zero, as in the
source) with `F / K` finite separable and `E / F` finite Galois, and `j` is
a `K`-algebra embedding of `E` into Mathlib's separable closure
`SeparableClosure K`. There is no valuation, topology or local-field
hypothesis. Both then introduce, as in the source,

```lean
let i := j.comp (IsScalarTower.toAlgHom K F E)
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
letI : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
```

Here `i : F →ₐ[K] SeparableClosure K` is the restriction of `j` to `F`. The
first local instance is the algebra structure of the intermediate field
`separableClosure F (AlgebraicClosure F)`, which is how Mathlib defines
`SeparableClosure F`. The second makes `SeparableClosure K` an `F`-algebra
through `i`. Both propositions then quantify over an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for these structures.

Both use the following local data from the source (the first proposition
uses all of it, the second only `H₀`, `J₀` and `hJH`):

- `jF : E →ₐ[F] SeparableClosure K`, the map `j` regarded as an `F`-algebra
  map (`commutes'` holds by `rfl` because the `F`-algebra structure on
  `SeparableClosure K` is given by `i`, the restriction of `j`);
- `jI : E →ₐ[F] SeparableClosure F := e.symm.toAlgHom.comp jF`, the
  corresponding embedding of `E` into the separable closure of `F`;
- `EI := finiteGaloisAbstractExtensionOfEmbedding F E jI`, the published
  finite abstract extension object of `E / F` attached to `jI` (source row
  M097.005);
- `H₀ := closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)`
  and `J₀ := closedFixingSubgroup K (SeparableClosure K)
  (AlgHom.fieldRange j)`, the closed subgroups of
  `Gal(SeparableClosure K / K)` fixing `i(F)` and `j(E)`;
- `hJH : J₀.toSubgroup ≤ H₀.toSubgroup`, with the source's tactic proof
  (`IntermediateField.fixingSubgroup_le` applied to the inclusion
  `i(F) ⊆ j(E)`, which holds because `i y = j (algebraMap F E y)`). The two
  source theorems name the bound variables of this proof differently
  (`x`, `y` and `y`, `z`); the port keeps each as in the source;
- the local instance `_hTargetNormal : (extensionSubgroup H₀ J₀ hJH).Normal`,
  given by the published theorem `ambientEmbeddedExtensionSubgroup_normal`
  (M274.003). This is the same instance that the type of
  `ambientEmbeddedExtensionQuotientEquivGaloisGroup` introduces, so the
  quotient `H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH` below is the domain
  of that equivalence.

The Library `extensionSubgroup H J h` (source row M004.002) is the subgroup
`J.toSubgroup.subgroupOf H.toSubgroup` of `H.toSubgroup`.

## The proposition `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement`

Besides `e`, it quantifies over an element
`tau : (intrinsicAbstractBase F).toSubgroup`. The Library
`intrinsicAbstractBase F` (source row M091.003) is the closed subgroup of
`Gal(SeparableClosure F / F)` fixing the bottom intermediate field, which is
the whole group. It also introduces the local instance
`_hSourceNormal := EI.normal`, the normality of the intrinsic extension
subgroup `extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below`.
The conclusion is

```lean
ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e
    (QuotientGroup.mk (intrinsicBaseEquivAmbientEmbeddedField K F i e tau)) =
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI
    (QuotientGroup.mk tau)
```

Here `intrinsicBaseEquivAmbientEmbeddedField K F i e` (M273.006) is the
equivalence from `intrinsicAbstractBase F` onto `H₀`, and
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI` (M090.009)
identifies the quotient of the whole group `Gal(SeparableClosure F / F)` by
the subgroup fixing `jI(E)` with `Gal(E / F)`. So the proposition says: the
automorphism of `E` attached to the class of the transported automorphism
`intrinsicBaseEquivAmbientEmbeddedField K F i e tau` is the automorphism
attached to the class of `tau` itself. The right-hand side typechecks because
`intrinsicAbstractBase F` is by definition
`closedFixingSubgroup F (SeparableClosure F) ⊥` and `EI.field` is
`finiteGaloisClosedFixingSubgroupOfEmbedding F E jI`.

## The proposition `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement`

Besides `e`, it quantifies over
`rho : (closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)).toSubgroup`,
an element of `H₀`, and over `x : E`. The conclusion is

```lean
j (ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e
    (QuotientGroup.mk rho) x) =
  rho.1.1 (j x)
```

So the automorphism of `E` attached to the class of `rho` acts on `E`, after
applying `j`, as `rho` acts on `j(E)`. Here `rho.1` is the underlying element
of `Gal(SeparableClosure K / K)` and `rho.1.1` its underlying equivalence of
types (the first parent `toEquiv` of `AlgEquiv`), applied to `j x`. The
right-hand side does not involve `e`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M274.005, `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U005.Definitions`, the only import) |
| M274.003, `LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` (module `...BaseComparison.EmbeddedExtensionQuotient.U003.Proofs`, imported through the U005 module) |
| M090.009, `LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` (module `...LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions`, imported through the U005 module) |
| M273.006, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` (module `...BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`, imported through the U005 module) |
| M097.005, `LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding` (module `...LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions`, imported through the U005 module) |
| M091.003, `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (module `...LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`, imported through the U005 module) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`, imported through the U005 module) |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`, imported through the U005 module) |

All of these declarations are published in the Library and are used under the
names above. They are reached through the source's `open RamificationTheory
CyclicCohomology` line inside the namespace
`Langlands.NYLL.LocalClassFieldTheory`. The statements are otherwise the
source text.

This unit does not include the source proofs. Besides the declarations
above, they cite three source theorems:

- the M274.006 proof cites the M274.002 theorem
  `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`, but only to
  supply a proof of the subgroup equality `hmap` inside a `change`. The
  Library publishes the statement as
  `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`, in
  module `...BaseComparison.EmbeddedExtensionQuotient.U001.Statements`. At
  the Library commit named below, the Library does not prove it;
- the M274.007 proof uses M274.006 and the source theorem
  `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply` (source
  row M098.027). The Library publishes that statement as
  `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement`,
  in module `...LocalReciprocity.ConcreteReciprocityCanonical.U027.Statements`,
  and does not yet prove it;
- the M274.007 proof also uses
  `intrinsicBaseEquivAmbientEmbeddedField_apply_val` (source row M273.008).
  This theorem is published in module
  `...BaseComparison.IntrinsicBaseEquivalence.U008.Proofs`, which the U005
  module imports.

The later proof children must supply the missing proofs or work around them.

## Relation to other Library and Mathlib declarations

The propositions are about `ambientEmbeddedExtensionQuotientEquivGaloisGroup`,
which exists only in this port. At Library commit
`e5bc828a22b84321024b9601684a29be845ce351` I searched all Library `.lean`
files for the name of this equivalence and for value formulas (`_mk`,
`_mk_apply`, `_apply_val`) of quotient-to-Galois-group equivalences. No
declaration states either proposition or any other value formula for this
equivalence. The closest published facts are:

- `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val`
  (M273.008, `...BaseComparison.IntrinsicBaseEquivalence.U008.Proofs`)
  gives the pointwise formula for `intrinsicBaseEquivAmbientEmbeddedField`;
- the published M274.001 and M274.002 statements
  (`intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement` and
  `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`, in
  `...BaseComparison.EmbeddedExtensionQuotient.U001.Statements`) say how that
  equivalence treats the extension subgroups;
- `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement`
  (M098.027, `...LocalReciprocity.ConcreteReciprocityCanonical.U027.Statements`)
  is the corresponding formula for the intrinsic equivalence
  `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` (M090.009), which
  is the right-hand side of the first proposition here;
- `Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup_applyStatement`
  (`...LocalReciprocity.FiniteAbstractFixedField.Initial.Statements`) and
  `Langlands.NYLL.LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_valStatement`
  (`...LocalReciprocity.AbstractFixedFieldUnits.Action.Statements`) are value
  formulas of the same shape for different equivalences. The first is for
  the equivalence between a closed subgroup `H` of `Gal(Ω / k)` and the
  Galois group of `Ω` over the fixed field of `H`. The second is for the
  equivalence between a quotient `K / L` of closed subgroups and the
  relative Galois group of their fixed fields. Neither involves the
  embedding `j` or the transport `e`.

Mathlib's `QuotientGroup.congr_mk` computes values of `QuotientGroup.congr`,
one of the equivalences that the definition of
`ambientEmbeddedExtensionQuotientEquivGaloisGroup` is built from. It does not
state these propositions.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>).
The complete file was read and its SHA-256 verified as
`6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The M274.006 docstring occupies lines 484–485 and its signature lines
486–535; its proof occupies lines 536–596. The M274.007 docstring occupies
lines 598–599 and its signature lines 600–639; its proof occupies lines
640–723. The header occupies lines 1–5, the `noncomputable section` line 20,
the namespace line 22 and the `open` lines 24–26.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M274.006, `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mkStatement`, closed Prop target |
| M274.007, `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk` and `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase. The
  binders, local `let`/`letI` data and conclusions are otherwise the source
  text, including the tactic proof inside `hJH`.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the single Library module that publishes
  `ambientEmbeddedExtensionQuotientEquivGaloisGroup`; it imports the other
  Library declarations used.
- The `noncomputable section`, the unused `open LocalFieldTheory` and
  `KummerTheory`, the unused `open ClassFormation` and the
  `open scoped ValuativeRel` are omitted. All other declarations of the
  source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M274.006 and M274.007 statement targets. Their
proofs and the other rows of the source file are not part of this unit.
