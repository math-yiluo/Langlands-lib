# Embedded extension quotients: normality and finiteness statements

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M274.003 and M274.004:

- `ambientEmbeddedExtensionSubgroup_normalStatement`, for the source theorem
  `ambientEmbeddedExtensionSubgroup_normal`;
- `ambientEmbeddedExtensionQuotient_finiteStatement`, for the source theorem
  `ambientEmbeddedExtensionQuotient_finite`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal`
and `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite`.

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

All three fields are in `Type` (universe zero), as in the source. So
`K ⊆ F ⊆ E` is a tower in which `F / K` is finite and separable and `E / F`
is finite Galois, and `j` is a `K`-algebra embedding of `E` into Mathlib's
separable closure `SeparableClosure K`. There is no valuation, topology or
local-field hypothesis.

Both propositions then introduce, as in the source,

```lean
let i := j.comp (IsScalarTower.toAlgHom K F E)
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
letI : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
```

So `i : F →ₐ[K] SeparableClosure K` is the restriction of `j` to `F`. The first
local instance is the algebra structure of the intermediate field
`separableClosure F (AlgebraicClosure F)`, which is how Mathlib defines
`SeparableClosure F`. The second makes `SeparableClosure K` an `F`-algebra
through `i`. Both propositions then quantify over an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for these structures, and
introduce

```lean
let H₀ := Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
  (AlgHom.fieldRange i)
let J₀ := Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
  (AlgHom.fieldRange j)
```

the closed subgroups of `Gal(SeparableClosure K / K)` fixing the images
`i(F)` and `j(E)`. Since `i(F) ⊆ j(E)`, `J₀ ≤ H₀`. Neither conclusion depends
on `e`; it is a bound variable in both propositions, as in the source.

## The two propositions

`ambientEmbeddedExtensionSubgroup_normalStatement` keeps the source's
`let _e := e` and concludes

```lean
(J₀.toSubgroup.subgroupOf H₀.toSubgroup).Normal
```

So `J₀`, viewed as a subgroup of the group `H₀`, is a normal subgroup of `H₀`.

`ambientEmbeddedExtensionQuotient_finiteStatement` names the isomorphism
binder `_e` and concludes

```lean
Finite (H₀.toSubgroup ⧸ J₀.toSubgroup.subgroupOf H₀.toSubgroup)
```

So `H₀` contains only finitely many left cosets of `J₀`. The quotient here is
Mathlib's quotient by left cosets, which needs no normality.

## Reused Library declaration and source abbreviations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`) |

The Library `closedFixingSubgroup k Ω K` is
`⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩` for a Galois
extension `Ω / k`, as in the source. Mathlib's instance `IsSepClosure.isGalois`
supplies `IsGalois K (SeparableClosure K)`.

The source statements also use the abbreviation M004.002
`CyclicCohomology.extensionSubgroup K L hLK := L.toSubgroup.subgroupOf
K.toSubgroup`, which is not published as a Lean declaration. It ignores its
inclusion proof. Both source statements apply it as
`extensionSubgroup H₀ J₀ hJH`, where `hJH : J₀.toSubgroup ≤ H₀.toSubgroup` is a
local `let` proved by a short tactic block inside the statement. This module
writes the body `J₀.toSubgroup.subgroupOf H₀.toSubgroup` directly. The proof
`hJH` is then no longer used, so it is omitted. The published Library module
`Langlands/NYLL/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields/AbstractExtension/Definitions.lean`
makes the same replacement of `extensionSubgroup` by its `Subgroup.subgroupOf`
body.

The source M274.004 statement also contains the local instance

```lean
letI _hTargetNormal : (extensionSubgroup H₀ J₀ hJH).Normal :=
  ambientEmbeddedExtensionSubgroup_normal K F E j e
```

which applies the source theorem M274.003. The conclusion does not use it: a
quotient by left cosets needs no normality instance. `letI` substitutes its
value into the body, so the instance does not appear in the elaborated source
statement. This module omits it. That also removes the only use of `e` in
M274.004, so its binder is named `_e`. The adapted M274.004 statement
therefore does not depend on M274.003.

A private check, not part of this submission, copies the source statements
verbatim, with the source `extensionSubgroup` and the source `hJH` tactic
proofs. For M274.004 it replaces the source theorem in `_hTargetNormal` by an
arbitrary proof of the source M274.003 statement. It confirms by `Iff.rfl`
and `rfl` that both propositions here are definitionally the source
statements.

## Relation to other Library and Mathlib declarations

No published declaration states either proposition. The Library module
`Langlands/ClassFieldTheory/Local/CommonClosureFiniteRestrictions.lean`
(namespace `Langlands.LocalClassField.FiniteQuotientTransport`) uses
subgroups of the form `L.fixingSubgroup.subgroupOf E.fixingSubgroup` for
intermediate fields `E ≤ L` of `AlgebraicClosure K`. It identifies such a
subgroup as the kernel of a restriction homomorphism
(`finiteRestrictionHom_ker`), but states no normality or finiteness
proposition of the form above. Mathlib has absolute versions for an
intermediate field `L` of a Galois extension `Ω / k`:
`InfiniteGalois.normal_iff_isGalois` (`L.fixingSubgroup` is normal in
`Gal(Ω/k)` exactly when `L / k` is Galois), `IntermediateField.fixingSubgroup_isOpen`
(the fixing subgroup of a finite-dimensional `L` is open) and
`IntermediateField.finrank_eq_fixingSubgroup_index`. They concern subgroups of
the whole Galois group, not the relative subgroup of `H₀` cut out by the
images of an embedded tower.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>).
The complete file was read and its SHA-256 verified as
`6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The M274.003 docstring and signature occupy lines 219–250; the theorem begins
at line 221, and its proof occupies lines 251–296. The M274.004 docstring and
signature occupy lines 298–332; the theorem begins at line 300, and its proof
occupies lines 333–392. The header occupies lines 1–5, the module docstring
lines 10–16, the `noncomputable section` line 20, the namespace line 22 and
the `open` lines 24–26. The source abbreviation `extensionSubgroup` is in
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` (SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`), lines
51–54.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M274.003, `LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normalStatement`, closed Prop target |
| M274.004, `LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finiteStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` and `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`,
  and the published name `closedFixingSubgroup` is written fully qualified
  instead of being reached through the source `open` lines.
- `extensionSubgroup H₀ J₀ hJH` is replaced by its body
  `J₀.toSubgroup.subgroupOf H₀.toSubgroup`, and the then unused local proof
  `hJH` is omitted, as described above.
- In M274.004 the unused local instance `_hTargetNormal` is omitted and the
  binder `e` is renamed `_e`, as described above.
- The source imports are replaced by the Library module that provides
  `closedFixingSubgroup` and by `Mathlib.FieldTheory.IsSepClosed`, which
  provides `SeparableClosure` and, through its imports, `separableClosure`
  and `AlgebraicClosure`.
- The `noncomputable section` and the `open` lines are omitted. All other
  declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M274.003 and M274.004 statement targets. Their
proofs and the other rows of the source file (M274.001, M274.002 and
M274.005–M274.007) are not part of this unit.
