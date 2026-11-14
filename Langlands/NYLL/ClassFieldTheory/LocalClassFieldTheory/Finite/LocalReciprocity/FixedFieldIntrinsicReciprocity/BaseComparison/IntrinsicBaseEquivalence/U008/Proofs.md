# Action of the embedded base equivalence on the separable closure

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement`
(source row M273.008) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U007.Statements`,
the published module that contains the statement (together with M273.007).
That published Lean/Markdown pair and everything it imports stay unchanged.

## Target

Write `Ω := SeparableClosure K`. In the statement, `F` is a field with
`[Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]`,
`i : F →ₐ[K] Ω` is a `K`-algebra embedding, `Ω` is made an `F`-algebra by
`i.toRingHom.toAlgebra`, `SeparableClosure F` carries its standard
`F`-algebra structure, `e : SeparableClosure F ≃ₐ[F] Ω` is an
`F`-algebra equivalence and `tau` is an element of
`(intrinsicAbstractBase F).toSubgroup`, the subgroup of
`Gal(SeparableClosure F / F)` fixing the bottom intermediate field (that is,
the whole group).

For every `x : Ω`, the statement asserts

```lean
(intrinsicBaseEquivAmbientEmbeddedField K F i e tau).1.1 x =
  e (tau.1 (e.symm x))
```

that is, the image of `tau` acts on `Ω` by conjugating `tau` through `e`.

## Implemented proof

```lean
  intro K F _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e tau x
  -- local copies of H₀, F₀, FiniteDimensional K F₀, the separability and
  -- IsSepClosure instances, the F₀-algebra on SeparableClosure F₀ and e₀
  ...
  show e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x)))))) =
    e (tau.1 (e.symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
```

1. After introducing the binders, the `F`-algebra structure on `Ω` induced
   by `i` is installed as in the statement.
2. The proof rebuilds, as local `let` bindings, the data that the body of
   `intrinsicBaseEquivAmbientEmbeddedField` (published in
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`) constructs:
   `H₀ := closedFixingSubgroup K Ω i.fieldRange`, its fixed field
   `F₀ := abstractFixedField K Ω H₀`, the instance `FiniteDimensional K F₀`
   (proved exactly as in that definition body, by transporting along
   `AlgEquiv.ofInjectiveField i` and the equality
   `InfiniteGalois.fixedField_fixingSubgroup i.fieldRange`), the separability of
   `Ω` over `F₀`, the `IsSepClosure F₀ Ω` instance, the standard `F₀`-algebra
   structure on `SeparableClosure F₀` and
   `e₀ := IsSepClosure.equiv F₀ (SeparableClosure F₀) Ω`.
3. Unfolding the definitions, the value of
   `intrinsicBaseEquivAmbientEmbeddedField K F i e tau` at `x : Ω` is
   definitionally `e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x))))))`:
   `intrinsicAbstractBaseEquivAbsolute F` sends `tau` to `tau.1`; the
   conjugation `theta` of the definition body, through
   `c := e` followed by `e₀⁻¹`, sends it to `y ↦ e₀⁻¹ (e (tau.1 (e⁻¹ (e₀ y))))`;
   `(intrinsicAbstractBaseEquivAbsolute F₀).symm` only wraps this automorphism
   in a subtype; and `intrinsicBaseEquivAmbientFixedField K H e₀` conjugates by
   `e₀` (via `AlgEquiv.autCongr e₀`) and then applies
   `(abstractSubgroupEquivGaloisGroup K Ω H₀).symm`, which does not change the
   underlying function.
   The `show` step checks this identification by definitional unfolding.
4. Two rewrites with Mathlib's `AlgEquiv.apply_symm_apply`
   (`e₀ (e₀.symm y) = y`) close the goal.

The proof does not use M273.007. It uses only Mathlib and the declarations
the statement already imports. No hypothesis, global instance or auxiliary
declaration is added.

## Relation to the original proof

The original proof (lines 515–582) rebuilds the data of the statement of
M273.007, rewrites with that theorem
(`intrinsicBaseEquivAmbientEmbeddedField_apply`), and finishes with a `calc`
chain through `(abstractSubgroupEquivGaloisGroup K Ω H₀).apply_symm_apply`.
The invoked source proof of M273.007 obtains its instance
`FiniteDimensional K F₀` from `abstractFixedField_finiteDimensional`
(source row M099.005), whose proof is not used here. The implemented
proof computes the value directly instead.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean>),
SHA-256 `0c4403626ce06952a02d1bd927112542e4f69466ca939a1d0896195d94ef5800`.
The theorem `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val`
has its docstring at lines 498–499, its signature at lines 500–514 and its proof
at lines 515–582. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` | Published `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement` (U007 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the proof is replaced as described above and placed in its own module `U008/Proofs`; the source imports are replaced by the single U007 Statements import; all other
declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

Worker 697 reused Worker 57's shared Task 6441 draft (revision 1), checked
the correspondence with the published definitions and original source, and
clarified the preceding description of the original proof dependency. The
Lean proof is unchanged from that draft.

This module contains only the M273.008 proof.
