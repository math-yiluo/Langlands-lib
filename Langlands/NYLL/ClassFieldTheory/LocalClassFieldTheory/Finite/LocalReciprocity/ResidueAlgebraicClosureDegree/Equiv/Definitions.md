# The intrinsic residue degree (data)

Adapted by Worker 46 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`
(whole-file SHA-256 `650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M236.002 (private instance) | `residueAlgebraicClosureIsAlgClosure` (47–48) | inlined by `haveI` in the body of M236.016 |
| M236.003 (private instance) | `residueAlgebraicClosureIsGalois` (50–52) | inlined by `haveI` in the body of M236.016 |
| M236.004 (private instance) | `residueAlgebraicClosureGaloisT2` (54–56) | inlined by `haveI` in the body of M236.016 |
| M236.016 | `residueAbsoluteFrobeniusEquivIn` (222–237) | `residueAbsoluteFrobeniusEquivIn` |
| M236.017 | `residueAbsoluteDegreeIn` (239–244) | `residueAbsoluteDegreeIn` |

Every unqualified original name above is in `LocalClassFieldTheory`. Every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Let `k : Type u` be a field with `[Fintype k]`, and let `Omega : Type v` be a `k`-algebra field
with `[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]` (source `variable` blocks,
lines 39–41). In other words, `Omega` is an algebraic closure of the finite field `k`. Let
`residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)` be the canonical continuous
Frobenius-parameter homomorphism (M168.005), where `ZHatMul` is the multiplicative profinite
integers and `Omega ≃ₐ[k] Omega` carries the Krull topology.

- M236.016. `residueAbsoluteFrobeniusEquivIn k Omega : ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega)` is the
  topological group isomorphism whose underlying map is `residueAbsoluteFrobenius k Omega`. Its
  multiplicative equivalence is `MulEquiv.ofBijective` of
  `(residueAbsoluteFrobenius k Omega).toMonoidHom`. The bijectivity proof is the pair of the
  published proofs `residueAbsoluteFrobenius_isAlgClosure_injective k Omega` (M236.010) and
  `residueAbsoluteFrobenius_isAlgClosure_surjective k Omega` (M236.015). The forward map is
  continuous because `residueAbsoluteFrobenius k Omega` is. The inverse is continuous by
  `Continuous.continuous_symm_of_equiv_compact_to_t2`: `ZHatMul` is compact and the Galois group
  is Hausdorff.
- M236.017. `residueAbsoluteDegreeIn k Omega : (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul` is the inverse of
  this equivalence, `(residueAbsoluteFrobeniusEquivIn k Omega).symm`, as a continuous monoid
  homomorphism (`ContinuousMonoidHom.toContinuousMonoidHom`). It is the intrinsic residue degree:
  it sends an automorphism of `Omega` over `k` to its Frobenius exponent in `ZHat`, written
  multiplicatively.

Parameters of both definitions, in order: `k`, `[Field k]`, `[Fintype k]`, `Omega`,
`[Field Omega]`, `[Algebra k Omega]`, `[Algebra.IsAlgebraic k Omega]`, `[IsAlgClosed Omega]`. These
are the source definitions' parameters: neither has an `omit`, and every section binder is used,
through `residueAbsoluteFrobenius` and the inlined instances below (M236.017 through M236.016).

## Modifications

- The namespace is prefixed by `Langlands.NYLL`. The source `variable` blocks, universes, `open`
  commands, names, types, field values, bodies and `noncomputable` status are retained.
- Private instances M236.002–M236.004. In the source they are section instances that instance
  search uses in the body of M236.016: `residueAbsoluteFrobenius k Omega` needs
  `[IsGalois k Omega]`, and `Continuous.continuous_symm_of_equiv_compact_to_t2` needs
  `T2Space (Omega ≃ₐ[k] Omega)`. Here no instance is declared. The body of M236.016 starts with
  three `haveI`s that supply the values:
  - `haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩` is the source's M236.002
    value.
  - `haveI : IsGalois k Omega := {}` stands for M236.003. The source proves it by
    `infer_instance`. In the pinned Mathlib of this environment, `IsAlgClosure.isGalois` requires
    `[CharZero k]`, so the structure instance `{}` is used instead. It fills the fields
    `Algebra.IsSeparable k Omega` (`k` is finite, hence perfect, and `Omega` is algebraic) and
    `Normal k Omega` (from the local `IsAlgClosure` instance) by instance search.
  - `haveI : T2Space (Omega ≃ₐ[k] Omega) := krullTopology_t2` stands for M236.004. The source proves
    it by `infer_instance`. Here Mathlib's theorem `krullTopology_t2` for the integral extension
    `Omega/k` gives it, since it is not an instance in this Mathlib.

  All three classes are propositions, so any two instances are definitionally equal and the
  definition's value is the source's. No global or local instance is added. M236.017 needs none
  of them: its body only uses M236.016.
- The source's `where` clauses of M236.016 become an anonymous structure instance
  `{ toMulEquiv := …, continuous_toFun := …, continuous_invFun := … }` after the `haveI`s, with the
  source's field values.
- The source theorems M236.010 and M236.015 used in the body are the published proofs of the
  targets `residueAbsoluteFrobenius_isAlgClosure_injectiveStatement` and
  `residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement`. Their types are these `Statement`
  definitions, which unfold by definition to `Function.Injective (residueAbsoluteFrobenius k Omega)`
  and `Function.Surjective (residueAbsoluteFrobenius k Omega)` with the same inlined instances.
  So the pair is accepted as the bijectivity proof.
- Imports: the source imports of NYLL modules are replaced by the published proof modules
  `ResidueAlgebraicClosureDegree.U010.Proofs` (M236.010) and
  `ResidueAlgebraicClosureDegree.U015.Proofs` (M236.015), which import the published port of
  `residueAbsoluteFrobenius`. `ZHatMul` is `Langlands.NYLL.ClassFormation.ZHatMul`. The source's
  `open RamificationTheory.Field.absoluteGaloisGroup` is dropped because that NYLL namespace is
  unused here.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. This support unit makes no claim to discharge
the host class-formation, cup, transfer, Tate or reciprocity targets.
