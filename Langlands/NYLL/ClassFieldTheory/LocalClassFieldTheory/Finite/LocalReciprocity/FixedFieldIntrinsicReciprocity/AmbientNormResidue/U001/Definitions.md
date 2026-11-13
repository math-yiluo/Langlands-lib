# The ambient separable-closure equivalence type

This module defines one type abbreviation,
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedSeparableClosureEquiv`.
It adapts source row M282.001, the abbreviation
`LocalClassFieldTheory.ambientEmbeddedSeparableClosureEquiv`, with its
telescope, docstring and body unchanged. The abbreviation produces a type
in `Type`. It installs no instance, constructs no element of the type, and
proves no theorem.

## Telescope

The abbreviation takes, in the source order,

```lean
(K F E : Type)
[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]
[Field E] [Algebra K F] [Algebra F E] [Algebra K E]
[IsScalarTower K F E]
[FiniteDimensional K F] [Algebra.IsSeparable K F]
[Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
[FiniteDimensional F E] [IsGalois F E]
(j : E →ₐ[K] SeparableClosure K)
```

So `K` and `F` are nonarchimedean local fields (Mathlib's root class
`IsNonarchimedeanLocalField`, with their own valuative relations and
topologies). `F` is a finite separable extension of `K`, and the valuation of
`F` extends that of `K`. `E` is a finite Galois extension of `F`, with
compatible `K`-, `F`- and `K`-to-`E` algebra structures forming a scalar
tower. `j` is a `K`-algebra embedding of `E` into Mathlib's separable closure
`SeparableClosure K`. All three field types are in universe zero, as in the
source.

## Body

The body is

```lean
@AlgEquiv F (SeparableClosure F) (SeparableClosure K)
  _ _ _
  (separableClosure F (AlgebraicClosure F)).algebra
  (j.comp (IsScalarTower.toAlgHom K F E)).toRingHom.toAlgebra
```

It is the type of `F`-algebra isomorphisms from `SeparableClosure F` to
`SeparableClosure K`, with the two `F`-algebra structures given explicitly:

- On the source, `SeparableClosure F` is Mathlib's abbreviation for the
  intermediate field `separableClosure F (AlgebraicClosure F)` viewed as a
  type. The structure `(separableClosure F (AlgebraicClosure F)).algebra`
  elaborates to `Subalgebra.algebra` of its underlying subalgebra. This is the
  usual `F`-algebra structure, whose algebra map is the inclusion of `F` into
  the separable closure.
- On the target, `SeparableClosure K` is made an `F`-algebra through the ring
  homomorphism `F → E → SeparableClosure K`. Here
  `IsScalarTower.toAlgHom K F E : F →ₐ[K] E` is the algebra map of `F` into
  `E`, viewed as a `K`-algebra map, and it is followed by `j`.
  `RingHom.toAlgebra` turns the composite into an algebra structure.

The three `_` are the commutative-semiring structure of `F` and the
semiring structures of the two separable closures, found by instance
search. An element of this type is therefore a ring isomorphism
`SeparableClosure F ≃ SeparableClosure K` that is the identity on `F`, where
`F` is embedded into `SeparableClosure K` through `j`. The source uses such
an isomorphism to compare the intrinsic extension over `F` with its
realization inside the ambient separable closure of `K`.

Only `Field K`, `Field F`, `Field E`, the three algebra structures, the
scalar tower and `j` occur in the body. The valuative, topological,
local-field, finiteness, separability, valuation-extension and Galois
instance parameters are not used in the body. They are kept so that the
telescope is the source's: later source declarations apply the
abbreviation to all of these arguments. Keeping them changes neither the
resulting type nor its algebra structures.

## Reused declarations and imports

The definition uses only Mathlib: `AlgEquiv`, `SeparableClosure`,
`separableClosure`, `AlgebraicClosure`, `Subalgebra.algebra`,
`AlgHom.comp`, `IsScalarTower.toAlgHom`, `RingHom.toAlgebra`,
`ValuativeRel.valuation`, `Valuation.HasExtension`,
`IsNonarchimedeanLocalField`, `FiniteDimensional`, `Algebra.IsSeparable` and
`IsGalois`. The source imports are replaced by four Mathlib modules:
`Mathlib.FieldTheory.Galois.Basic` (`IsGalois`),
`Mathlib.FieldTheory.IsSepClosed` (`SeparableClosure`),
`Mathlib.NumberTheory.LocalField.Basic` (`IsNonarchimedeanLocalField`) and
`Mathlib.RingTheory.Valuation.Extension` (`Valuation.HasExtension`). Their
import closure supplies the rest. No NYLL module is needed.

## Library search

The whole Library at commit `8cfcc2bff12a9cb7a1f89a973a0c59f2dc39865a`
(whose Lean files are identical to those of the current base
`125eb56832ba1e00c87d0a67981fe249453d68b4`) was
searched for `SeparableClosure` together with `AlgEquiv`, `≃ₐ` and
`RingHom.toAlgebra`. The algebra equivalences found are Galois groups
`SeparableClosure K ≃ₐ[K] SeparableClosure K` and central-simple-algebra
splittings over `SeparableClosure K`. The `RingHom.toAlgebra` structures on
`SeparableClosure k` occur only as local `let`s inside proofs in
`Langlands/GroupScheme/`. The NYLL Library has the embeddings
`Langlands.NYLL.AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure`
and `Langlands.NYLL.PortInternal.M262.d004`, which are algebra
homomorphisms into `SeparableClosure K`, not this equivalence type. No
Library declaration names the type of `F`-algebra isomorphisms
`SeparableClosure F ≃ SeparableClosure K` with the target structure through
`j`. So nothing in the Library already covers M282.001.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean>).
The complete file was read; its SHA-256 is
`68d2430b93071e1b8d5a021fef789a2548146fc18d268ac2887fc4710d2d08dc`.
The header is at lines 1–5, the imports at 7–9, the module docstring at
11–18, `noncomputable section` at 22, the namespace at 24 and the `open`
lines at 26–29.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M282.001, `LocalClassFieldTheory.ambientEmbeddedSeparableClosureEquiv` | docstring 31–32, telescope 33–45, body 46–49 | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedSeparableClosureEquiv` |

In the source, the abbreviation is used again in the same file (lines 267 and
358) and in `AmbientPrimeWitness.lean`, `AmbientPrimeSymbolSetup.lean`,
`AmbientPrimeComparison.lean` and `AmbientPrimeWitnessComparison.lean`.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the abbreviation directly from the pinned original on
13 November 2026 and made these changes:

- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
  The name, docstring, telescope and body are unchanged.
- The source imports (the NYLL `EmbeddedFrobeniusTransport` module,
  `Mathlib.FieldTheory.Galois.Abelian` and
  `Mathlib.GroupTheory.Abelianization.Defs`) are replaced by the four Mathlib
  modules listed above. The abbreviation uses nothing from the NYLL module.
- The `open` lines are omitted. The body and telescope use none of the
  opened namespaces. The `noncomputable section` is kept around the
  definition, as in the source.
- All other declarations of the source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this abbreviation. It asserts no theorem, so no proof
obligation remains. The later declarations of the source file, starting with
the structure `AmbientEmbeddedFixedFieldPresentation` (M282.002, line 57),
are separate units.
