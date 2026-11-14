# Value of the embedded base equivalence as a subgroup element

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_applyStatement`
(source row M273.007) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U007.Statements`.
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

The statement then introduces, as `let` bindings, the closed subgroup
`H₀ := closedFixingSubgroup K Ω i.fieldRange` of `Gal(Ω / K)`, its finiteness
witness (the published theorem `ambientEmbeddedAbsoluteQuotientFinite`), its
fixed field `F₀ := abstractFixedField K Ω H₀`, the equality
`F₀ = i.fieldRange`, the ring isomorphism `phi : F ≃+* F₀` and the automorphism
`rho : Gal(Ω / F₀)` whose underlying map is `x ↦ e (tau.1 (e.symm x))`. It
asserts

```lean
intrinsicBaseEquivAmbientEmbeddedField K F i e tau =
  (abstractSubgroupEquivGaloisGroup K Ω H₀).symm rho
```

as elements of `H₀.toSubgroup`.

## Implemented proof

```lean
  intro K F _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e tau
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  -- local copies of H₀, F₀, FiniteDimensional K F₀, the separability and
  -- IsSepClosure instances, the F₀-algebra on SeparableClosure F₀ and e₀
  ...
  show e₀ (e₀.symm (e (tau.1 (e.symm (e₀ (e₀.symm x)))))) =
    e (tau.1 (e.symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
```

1. After introducing the binders, the `F`-algebra structure on `Ω` induced
   by `i` is installed as in the statement.
2. Both sides are elements of the subgroup `H₀.toSubgroup` of `Gal(Ω / K)`.
   `Subtype.ext` reduces the goal to equality of the underlying automorphisms
   and `AlgEquiv.ext` to equality of their values at every `x : Ω`.
3. The proof rebuilds, as local `let` bindings, the data that the body of
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
4. Unfolding the definitions, the value of
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
   The right-hand side at `x` is `rho x = e (tau.1 (e.symm x))`, again
   because `(abstractSubgroupEquivGaloisGroup K Ω H₀).symm` only restricts
   scalars. The `show` step checks both identifications by definitional
   unfolding.
5. Two rewrites with Mathlib's `AlgEquiv.apply_symm_apply`
   (`e₀ (e₀.symm y) = y`) close the goal.

The instance `FiniteDimensional K F₀` is a proposition, so its proof does not
affect the definitional computation. The proof uses only Mathlib and the
declarations the statement already imports. No hypothesis, global instance or
auxiliary declaration is added.

## Relation to the original proof

The original proof (lines 375–496) rebuilds the same data, defines the
conjugate `thetaTau` of `tau` in `Gal(SeparableClosure F₀ / F₀)`, proves
`AlgEquiv.autCongr e₀ thetaTau = rho` by extensionality, and then rewrites the
goal with `change` steps that use `closedFixingSubgroup_bot_eq_baseField`.
Its instance `FiniteDimensional K F₀` comes from
`abstractFixedField_finiteDimensional` (source row M099.005). When Worker 57
prepared the shared draft on 13 November 2026, that theorem was available
only as a statement. The current Library also publishes its proof in
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs`.
The implemented proof uses the Mathlib proof already present in the
published definition body and checks the same pointwise identity directly,
so it needs no import of the M099.005 proof.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean>),
SHA-256 `0c4403626ce06952a02d1bd927112542e4f69466ca939a1d0896195d94ef5800`.
The theorem `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply`
has its docstring at lines 309–311, its signature at lines 312–374 and its proof
at lines 375–496. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply` | Published `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_applyStatement` (U007 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the proof is replaced as
described above; the source imports are replaced by the single U007
Statements import; all other declarations of the source file are omitted.

Worker 695 reused Worker 57's shared draft revision 1 for Task 6440,
checked its computation against the published U004 definition and the
pinned original, and updated the historical dependency description on
14 November 2026. The Lean proof body is unchanged from that draft.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M273.007 proof.
