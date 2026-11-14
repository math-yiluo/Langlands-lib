# The Frobenius image in a residue algebraic closure (data)

Adapted by Worker 46 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`
(whole-file SHA-256 `650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M236.002 (private instance) | `residueAlgebraicClosureIsAlgClosure` (47–48) | inlined by `haveI` in the body below |
| M236.003 (private instance) | `residueAlgebraicClosureIsGalois` (50–52) | inlined by `haveI` in the body below |
| M236.004 (private instance) | `residueAlgebraicClosureGaloisT2` (54–56) | inlined by `haveI` in the body below |
| M236.012 | `residueAbsoluteFrobeniusRangeIn` (172–179) | `residueAbsoluteFrobeniusRangeIn` |

Every unqualified original name above is in `LocalClassFieldTheory`. Every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Let `k : Type u` be a field with `[Fintype k]`, and let `Omega : Type v` be a `k`-algebra field
with `[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]` (source `variable` blocks,
lines 39–41). In other words, `Omega` is an algebraic closure of the finite field `k`.

`residueAbsoluteFrobeniusRangeIn k Omega : ClosedSubgroup (Omega ≃ₐ[k] Omega)` is the range of
the canonical continuous Frobenius-parameter homomorphism
`residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)` (M168.005). It is a closed
subgroup of the Galois group with its Krull topology. Its underlying subgroup is
`(residueAbsoluteFrobenius k Omega).toMonoidHom.range`. Closedness holds because the range of a
continuous map from the compact space `ZHatMul` is compact (`isCompact_range`), and a compact set in
a Hausdorff space is closed (`IsCompact.isClosed`).

Parameters, in order: `k`, `[Field k]`, `[Fintype k]`, `Omega`, `[Field Omega]`,
`[Algebra k Omega]`, `[Algebra.IsAlgebraic k Omega]`, `[IsAlgClosed Omega]`. These are the source
definition's parameters: it uses all of its section binders, through the private instances below.

## Modifications

- The namespace is prefixed by `Langlands.NYLL`. The source `variable` blocks, universes, `open`
  commands, name, type, field values and `noncomputable` status are retained.
- Private instances M236.002–M236.004. In the source they are section instances that instance
  search uses in the body. `residueAbsoluteFrobenius k Omega` needs `[IsGalois k Omega]`, and
  `IsCompact.isClosed` needs `T2Space (Omega ≃ₐ[k] Omega)`. Here no instance is declared. The body
  starts with three `haveI`s that supply the values:
  - `haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩` is the source's M236.002
    value.
  - `haveI : IsGalois k Omega := {}` stands for M236.003. The source proves it by
    `infer_instance`. In the pinned Mathlib of this environment, `IsAlgClosure.isGalois` requires
    `[CharZero k]`, so the structure instance `{}` is used instead. It fills the fields
    `Algebra.IsSeparable k Omega` (`k` is finite, hence perfect, and `Omega` is algebraic) and
    `Normal k Omega` (from the local `IsAlgClosure` instance) by instance search.
  - `haveI : T2Space (Omega ≃ₐ[k] Omega) := krullTopology_t2` stands for M236.004. The source proves
    it by `infer_instance`; here Mathlib's theorem `krullTopology_t2` for the integral extension
    `Omega/k` gives it, since it is not an instance in this Mathlib.

  All three classes are propositions, so any two instances are definitionally equal and the
  definition's value is the source's. No global or local instance is added.
- The source's `where` clauses become an anonymous structure instance
  `{ toSubgroup := …, isClosed' := … }` after the `haveI`s, with the source's field values.
- Imports: the source imports of NYLL modules are replaced by the published `Langlands.NYLL` port of
  `residueAbsoluteFrobenius` (M168.005). `ClosedSubgroup` is Mathlib's
  (`Mathlib.Topology.Algebra.Group.ClosedSubgroup`) and `ZHatMul` is
  `Langlands.NYLL.ClassFormation.ZHatMul`. The source's
  `open RamificationTheory.Field.absoluteGaloisGroup` is dropped because that NYLL namespace is
  unused here.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. This support unit makes no claim to discharge
the host class-formation, cup, transfer, Tate or reciprocity targets.
