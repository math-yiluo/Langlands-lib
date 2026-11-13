# Residue arithmetic Frobenius of a valuation extension

This module adapts NYLL source unit M264.001. It exports one data definition,
`Langlands.NYLL.LocalFieldTheory.residueExtensionArithmeticFrobeniusOfValuationExtension`:
the arithmetic Frobenius automorphism `x ↦ x ^ q` of the residue field
`𝓀[L]` over `𝓀[K]`, where `q` is the number of elements of `𝓀[K]`. It is
the residue-level ingredient of the field arithmetic Frobenius of a finite
unramified extension (source unit M264.007), which is defined later by
transporting it through the Galois-to-residue isomorphism.

## Interface and meaning

```lean
def residueExtensionArithmeticFrobeniusOfValuationExtension
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]
```

The universe `u` is arbitrary and shared by `K` and `L`, as in the source;
it is the only universe parameter. `IsNonarchimedeanLocalField` is Mathlib's
class (`Mathlib.NumberTheory.LocalField.Basic`): a valuative topology that is
locally compact with a nontrivial valuation. The scoped notation `𝒪[F]` is
the integer ring `Valuation.integer (ValuativeRel.valuation F)`, and `𝓀[F]` is
its residue field `IsLocalRing.ResidueField 𝒪[F]` (both from
`open scoped ValuativeRel`).

The `𝓀[K]`-algebra structure on `𝓀[L]` is Mathlib's canonical
`IsLocalRing.ResidueField` algebra. It is induced by the integer-ring algebra
`Valuation.HasExtension.instAlgebraInteger`, the restriction of
`algebraMap K L`, which is a local homomorphism. This is the same algebra
structure used by the published residue maps
`galoisGroupResidueAlgEquivOfIsIntegralClosure` and
`galoisGroupResidueAlgEquivHomOfIsIntegralClosure`; see
[the residue algebra definitions](../ResidueGalois/AlgebraDefinitions.md).

The result is a `𝓀[K]`-algebra automorphism of `𝓀[L]`. Its forward map is
`x ↦ x ^ Fintype.card 𝓀[K]`, where the `Fintype` structure is
`Fintype.ofFinite 𝓀[K]`. So the exponent is the cardinality of `𝓀[K]`, which
is also `Nat.card 𝓀[K]`. The definition needs neither `FiniteDimensional K L`
nor `IsGalois K L` nor an unramifiedness hypothesis; the source states it in
the same generality. No instance is declared.

## Construction

The complete body is

```lean
  letI := Fintype.ofFinite 𝓀[K]
  FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]
```

Mathlib's instance `IsNonarchimedeanLocalField` → `Finite 𝓀[K]` (in
`Mathlib.NumberTheory.LocalField.Basic`) makes the residue field finite;
`Fintype.ofFinite` turns this into the `Fintype` structure that
`FiniteField.frobeniusAlgEquivOfAlgebraic` requires. That Mathlib definition
(`Mathlib.FieldTheory.Finite.Basic`) takes a finite field `K'`, a field `L'`
with `[Algebra K' L']` and `[Algebra.IsAlgebraic K' L']`, and returns the
`K'`-algebra automorphism of `L'` whose underlying function is
`(· ^ Fintype.card K')` (Mathlib's `coe_frobeniusAlgEquivOfAlgebraic`, proved
by `rfl`). The algebraicity instance `Algebra.IsAlgebraic 𝓀[K] 𝓀[L]` is
found by instance search, because `𝓀[L]` is also a finite field.

## Checks

All checks used `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The module compiled with no
errors or warnings. Inspection of the declaration reported kind
`definition`, level parameters `[u]`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

A private, unexported author probe also compiled without errors or
warnings. It checked:

- by `rfl`, that the definition equals the source body verbatim, including
  the source's local `letI : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance`;
- the source theorem M264.002: the value at `x : 𝓀[L]` is
  `x ^ Nat.card 𝓀[K]` (by `change` to the Mathlib automorphism and `simp`
  with `Nat.card_eq_fintype_card`);
- the source theorem M264.004: its order is
  `Module.finrank 𝓀[K] 𝓀[L]`, which is Mathlib's
  `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`.

These are author diagnostics. They do not replace machine validation or
independent review, and none of these theorems is exported here.

## Imports and scope

The three explicit imports are Mathlib modules:

- `Mathlib.FieldTheory.Finite.Basic`, for
  `FiniteField.frobeniusAlgEquivOfAlgebraic`;
- `Mathlib.NumberTheory.LocalField.Basic`, for `IsNonarchimedeanLocalField`
  and the instance `Finite 𝓀[K]`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension` and
  the integer-ring algebra that induces the residue algebra.

The scoped notations `𝒪[F]` and `𝓀[F]` come from
`Mathlib.Topology.Algebra.Valued.ValuativeRel`, which these imports load. The
source imports (`Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`,
`Mathlib.SetTheory.Cardinal.Finite`, `Mathlib.FieldTheory.Galois.Basic`,
`Mathlib.FieldTheory.Finite.Extension`, the NYLL module `FiniteUnramified` and
the NYLL Hensel lemma module) serve the rest of the source module and are not
needed for this unit. The source's `open _root_.LocalFieldTheory.IsNonarchimedeanLocalField`
is omitted; it is not used by this definition.

Only M264.001 is adapted. The source theorems M264.002–M264.006 about this
automorphism, the field arithmetic Frobenius M264.007 and the rest of the
module are not ported here.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean#L33-L44)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has SHA-256
`7839a2b17c7afc0b94c113a3b528b252dd05954e7452d282ff173d615b923104`, which is
the value recorded for M264 in the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m263-m269.md#m264).

| Partition unit | Original declaration in `LocalFieldTheory` | Original lines | Adapted definition in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M264.001 | `residueExtensionArithmeticFrobeniusOfValuationExtension` | 33–44 | `residueExtensionArithmeticFrobeniusOfValuationExtension` |

Lines 33–35 are the doc comment, line 36 the `noncomputable def` keyword, lines
37–41 the parameters and result type, and lines 42–44 the tactic body. The
source module declares `universe u` (line 26) and works in
`noncomputable section` (line 24); the adapted module does the same.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix;
- kept the parameters, their order and the result type exactly;
- wrote the body as a term instead of the source tactic block
  `by letI := ...; letI : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance; exact ...`.
  The local algebraicity declaration is dropped because instance search
  finds the same instance; the probe above shows the two bodies are
  definitionally equal (`rfl`);
- rewrote the doc comment to describe the adapted definition;
- replaced the source imports by the three Mathlib modules above.

No draft from another worker was used. Mathlib is reused by declaration
name; its code is not copied here.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `UnramifiedFrobenius.lean`.

The Lean file keeps the original copyright and author header verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). The header then records the
modifications above. The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
