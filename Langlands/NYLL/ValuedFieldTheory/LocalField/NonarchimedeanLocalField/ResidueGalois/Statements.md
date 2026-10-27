# Residue evaluation and base-residue fixedness statements

This module defines exactly two closed propositions in
`Langlands.NYLL.LocalFieldTheory`, adapting the types of NYLL source units
M160.002 and M160.004. Both concern the published residue-field equivalence
`galoisGroupResidueFieldEquivOfIsIntegralClosure`. The first says how it
acts on a residue class with a given representative. The second says that it
fixes the image of the base residue field. The module supplies statement
targets only; it proves neither formula.

## Complete targets

The first declaration is
`Langlands.NYLL.LocalFieldTheory.GaloisGroupResidueFieldEquivOfIsIntegralClosureResidueStatement`.
It has type `Prop`, one arbitrary universe parameter `u`, and no
mathematical declaration parameters. Its entire body is:

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]),
  galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
      (IsLocalRing.residue 𝒪[L] x) =
    IsLocalRing.residue 𝒪[L]
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x)
```

In words, applying the residue-field equivalence to the class of an integer
`x` of `L` gives the class of the image of `x` under the integer-ring
restriction of `σ`. The left side is the residue-field map applied to the
reduction. The right side is the reduction of the restricted image.

The second declaration is
`Langlands.NYLL.LocalFieldTheory.GaloisGroupResidueFieldEquivOfIsIntegralClosureAlgebraMapStatement`.
It likewise has type `Prop`, one arbitrary universe parameter `u`, and no
mathematical declaration parameters. Its entire body is:

```lean
∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝓀[K]),
  galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (algebraMap 𝓀[K] 𝓀[L] x) =
    algebraMap 𝓀[K] 𝓀[L] x
```

In words, the residue-field equivalence fixes every element of `𝓀[L]`
that comes from the base residue field `𝓀[K]` under the canonical map.
The equality is oriented from the equivalence applied to the image to the
image itself.

Both orientations, the maps and the hypothesis lists are those of the
original theorems. Neither statement is replaced by an abstract action law,
an algebra-equivalence `commutes` field, or an existential package.

## Hypotheses, concrete rings, and scalar structures

The fields `K` and `L` share the arbitrary universe `u`, as in the original
source. All fields, instances, the automorphism `σ` and the element `x` are
universally quantified inside each proposition. Neither target is
specialized to `Type 0`.

With `open scoped ValuativeRel`, the notation `𝒪[F]` means the actual
Mathlib valuation integer ring `Valuation.integer (ValuativeRel.valuation F)`,
the elements of `F` of valuation at most one. The notation `𝓀[F]` means
`IsLocalRing.ResidueField 𝒪[F]`, the quotient of that integer ring by its
maximal ideal, and `IsLocalRing.residue 𝒪[L]` is the quotient map. The
notation `Gal(L/K)` denotes the `K`-algebra automorphisms of `L`; no
`IsGalois K L` assumption is made.

The supplied `Algebra K L` is the field algebra structure. The instance
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
says that the valuation on `K` is equivalent to the pullback of the
valuation on `L`. From it, Mathlib's `Valuation.HasExtension.instAlgebraInteger`
gives the algebra structure of `𝒪[L]` over `𝒪[K]`, whose map is the
restriction of `algebraMap K L`. Mathlib's
`Valuation.HasExtension.instIsLocalHomValuationInteger` shows that this map
is a local homomorphism.

The map `algebraMap 𝓀[K] 𝓀[L]` in the second target is then Mathlib's
`IsLocalRing.ResidueField.instAlgebra` for that integer-ring algebra. It is
definitionally `IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[L])`. On
the class of a base integer `a`, it gives the class of
`algebraMap 𝒪[K] 𝒪[L] a`, as stated by Mathlib's
`IsLocalRing.ResidueField.algebraMap_residue`. This is the same map that
the original `ResidueExtension.lean` names
`residueFieldMapOfValuationExtension` and identifies with this
`algebraMap` by `rfl`. No NYLL alias for it is ported here. This module
installs no scalar or action instances.

The relative `IsIntegralClosure 𝒪[L] 𝒪[K] L` instance says that the
embedded integer ring of `L` is the integral closure of the integer ring of
`K` in `L`. It is the hypothesis of the published integer-ring and
residue-field equivalences. These are exactly the original hypotheses.
Neither target adds algebraicity, finite-dimensionality, `IsGalois`,
topology, completeness, local-field, discrete-valuation, residue-cardinality,
prime, preservation-certificate or fixedness hypotheses.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The full source file
has SHA-256
`b3c47318364659eb1a14b872f8462a2284f47125b1d84391c5c93a3ba87f2c67`.

| Partition unit | Original declaration in `LocalFieldTheory` | Original lines | Closed target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M160.002 | `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue` | 43–54 | `GaloisGroupResidueFieldEquivOfIsIntegralClosureResidueStatement` |
| M160.004 | `galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap` | 70–84 | `GaloisGroupResidueFieldEquivOfIsIntegralClosureAlgebraMapStatement` |

The line ranges include the docstrings; the theorem keywords are on lines
46 and 71. The
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m160)
provides these source unit identifiers. Each target body is the original
theorem's binder list followed by its conclusion, with the binders moved
inside a universal quantifier. The only changes are the namespace prefix
and the PascalCase name.

The original M160.002 carries `@[simp]` and has proof `rfl`. The original
M160.004 has no attribute. Its proof chooses a representative
`a : 𝒪[K]` of `x` and rewrites with `residueField_algebraMap_residue`,
from original `ResidueExtension.lean` lines 90–96. It then rewrites with
M160.002 and applies `galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap`,
from original `GaloisIntegerRing.lean` lines 123–134. That lemma says the
restriction fixes base integers, which follows from `σ.commutes`. Its
`integerRingMapOfValuationExtension` is defined at `ResidueExtension.lean`
lines 36–40 as `algebraMap 𝒪[K] 𝒪[L]`. The original proofs are not
reproduced here.

The partition's `.END` dependencies, including M160.003 before M160.004,
are conservative scheduling markers, not logical hypotheses. The second
formula does not use residue units.

## Proof boundary

This statement unit proves neither formula, and exports no theorem, proof,
or simp lemma.

The original source restricts `σ` with explicit subtype constructors, so its
integer-ring evaluation in `L` holds by `rfl`. The published
[integer-ring definition](../GaloisIntegerRing/Definitions.md) instead uses
Mathlib's `galRestrict'` packaged by `AlgEquiv.ofAlgHom`. Its agreement with
`σ` in `L` is propositional, through Mathlib's `algebraMap_galRestrict'_apply`;
it is not claimed to hold by `rfl`. A later proof of M160.004 must use that
published implementation. It cannot assume the original subtype construction
or an unpublished port of `galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap`.

The author also ran private, unsubmitted `lean_check` diagnostics. They
suggest that the first formula holds by unfolding Mathlib's
`IsLocalRing.ResidueField.mapEquiv`. They suggest that the second follows by
choosing a representative, then using `IsLocalRing.ResidueField.algebraMap_residue`,
`algebraMap_galRestrict'_apply` and `σ.commutes`. These diagnostics are
neither part of this candidate nor proof evidence. Proofs belong to separate
exact-target tasks.

## Scope and imports

Only M160.002 and M160.004 are covered. M160.003, the residue-unit formula,
is excluded. So are M160.005–006, the residue algebra equivalence and its
group homomorphism, and every later homomorphism, action, stabilizer,
kernel, inertia or ramification-index unit. No duplicate
`ResidueExtension.lean` alias is ported. No host inertia or reciprocity
comparison is asserted.

The explicit imports are
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
`Mathlib.RingTheory.Valuation.Extension`, and
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.Definitions`.
The first provides the residue-field algebra instance, and through its
imported `Mathlib.RingTheory.LocalRing.ResidueField.Defs` the residue field
and `IsLocalRing.residue`. The second provides the integer-ring algebra of a valuation
extension. The third is the published
[residue-field definition](Definitions.md), which imports the published
integer-ring restriction. The two Mathlib modules are already imported
transitively; they are listed to show where the canonical data come from.
The original imports of `Mathlib.SetTheory.Cardinal.Finite`,
`Mathlib.FieldTheory.Galois.Basic`, `Mathlib.NumberTheory.RamificationInertia.Galois`
and the NYLL `GaloisIntegerRing` module are not used. The unused original
namespace opening `_root_.LocalFieldTheory.IsNonarchimedeanLocalField` is
omitted.

Author checks through `lean_check` succeeded in the approved Lean 4.34.0 /
Mathlib `5ed2965256430c3649e86755f9576b54eca72435` environment, without
errors or warnings. Inspection of each complete unapplied declaration
reported `statement_returns_prop: true`, the single universe parameter `u`,
and only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
Private printing confirmed the quantified bodies above. It also confirmed
that the instances used are `IsLocalRing.ResidueField.instAlgebra`,
`Valuation.HasExtension.instAlgebraInteger` and
`Valuation.HasExtension.instIsLocalHomValuationInteger`. These are author
diagnostics, separate from independent review.

## Provenance, license, and modifications

Worker 761 read original `ResidueGalois.lean` lines 1–100. This includes
its imports, namespace, universe and openings, the M160.001 definition, and
both theorems and proofs above, plus M160.003 and M160.005–006 for scope.
Original `ResidueExtension.lean` lines 1–100 were also read, with SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`;
lines 34–96 give the canonical map and reduction conventions. Original
`GaloisIntegerRing.lean` lines 1–135 were read, with SHA-256
`5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`; they
cover the original restriction and base-integer fixedness. Mathlib's
`RingTheory/Valuation/Extension.lean` section `AlgebraInstances` and
`RingTheory/LocalRing/ResidueField/Basic.lean` residue-algebra section were
read in the approved environment.

The readable original belongs to registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum file was found in the project or current Library
notes. The public partition records no patch10 change to `ResidueGalois.lean`,
and no patch10 code is reused.

The original copyright and author header is retained verbatim in the Lean
file: copyright 2026 Naganori Yamaguchi, all rights reserved; authors
Naganori Yamaguchi (assisted by OpenAI Codex). The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged in
the Library. They match the pinned source byte for byte, with SHA-256
values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. The NOTICE has no entry specific to `ResidueGalois.lean`.

On 27 October 2026, Worker 761 extracted the two theorem types, added the
namespace prefix, and renamed them to the two PascalCase statement targets.
Worker 761 also moved every mathematical parameter inside its proposition,
kept the shared arbitrary universe, removed the proofs and the `@[simp]`
attribute, and reduced the imports. Worker 761 wrote this documentation. No
other worker contributed an adapted draft to this pair. The published
residue-field and integer-ring definitions and Mathlib are reused by import
and declaration name; their implementations are not copied here.
