# Normality of embedded extension subgroups

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normalStatement`
(source row M274.003) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U003.Statements`.
That published Lean/Markdown pair and everything it imports stay unchanged.

## Target

Unfolded, the target is

```lean
∀ (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K),
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let _e := e
      let H₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      (J₀.toSubgroup.subgroupOf H₀.toSubgroup).Normal
```

`closedFixingSubgroup K Ω M` is the closed subgroup whose underlying
subgroup is `M.fixingSubgroup`. So, with `G = Gal(SeparableClosure K / K)`,
the target says: the subgroup of `G` fixing `j(E)`, intersected with the
subgroup `H₀` of `G` fixing `i(F)` and viewed as a subgroup of `H₀`, is
normal in `H₀`.

## Implemented proof

The proof introduces the binders
`K F E`, the eleven instance arguments, `j`, `i`, `e`, `_e`, `H₀` and `J₀`.
The two `letI` algebra instances of the statement are inlined into the goal,
so they are not introduced. The proof does not use `e`.

### Key step: `H₀` maps `j(E)` into itself

```lean
  have hmaps : ∀ h ∈ (AlgHom.fieldRange i).fixingSubgroup,
      ∀ x ∈ AlgHom.fieldRange j, h x ∈ AlgHom.fieldRange j := by
    intro h hh x hx
    let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
    let jF : E →ₐ[F] SeparableClosure K :=
      { j.toRingHom with commutes' := fun _ => rfl }
    let EF : IntermediateField F (SeparableClosure K) := jF.fieldRange
    have : Normal F EF := Normal.of_algEquiv (AlgEquiv.ofInjectiveField jF)
    let hF : SeparableClosure K →ₐ[F] SeparableClosure K :=
      { (h : SeparableClosure K ≃ₐ[K] SeparableClosure K).toRingHom with
        commutes' := fun y =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _ ⟨y, rfl⟩ }
    have hrange := AlgHom.fieldRange_of_normal (hF.comp EF.val)
    obtain ⟨y, rfl⟩ := hx
    have hmem : h (j y) ∈ (hF.comp EF.val).fieldRange := ⟨⟨j y, y, rfl⟩, rfl⟩
    rw [hrange] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, hz⟩
```

Let `h` fix `i(F)` pointwise and let `x = j y` lie in `j(E)`.

1. Give `SeparableClosure K` the `F`-algebra structure through `i`, as the
   statement does. Since `i y = j (algebraMap F E y)` by definition, the map
   `j` is then an `F`-algebra map `jF`, and its image `EF` is an
   intermediate field of `SeparableClosure K` over `F` with the same
   elements as `j(E)`.
2. `EF` is `F`-isomorphic to `E` (Mathlib's `AlgEquiv.ofInjectiveField`),
   and `E / F` is normal because it is Galois. So `EF / F` is normal
   (`Normal.of_algEquiv`).
3. Because `h` fixes every `i y`, it is an `F`-algebra endomorphism `hF` of
   `SeparableClosure K` (Mathlib's `IntermediateField.mem_fixingSubgroup_iff`
   gives `h (i y) = i y`).
4. Mathlib's `AlgHom.fieldRange_of_normal`
   (`Mathlib/FieldTheory/Normal/Basic.lean`) says that every `F`-algebra
   map from a normal intermediate field `EF` into the ambient field has image
   `EF`. Applied to `hF` restricted to `EF`, it shows that `h x` lies in
   `EF`, so `h x = j z` for some `z : E`.

### Normality

```lean
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : Gal(SeparableClosure K / K)) ∈ (AlgHom.fieldRange j).fixingSubgroup := hn
  have hg : (g : Gal(SeparableClosure K / K))⁻¹ ∈
      (AlgHom.fieldRange i).fixingSubgroup := (g⁻¹).2
  change ((g * n * g⁻¹ : H₀.toSubgroup) : Gal(SeparableClosure K / K)) ∈
    (AlgHom.fieldRange j).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hn' ⊢
  intro x hx
  have hy := hmaps _ hg x hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
  rw [hn' _ hy, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
```

Take `n` in the relative subgroup and `g` in `H₀`; the goal is that
`g n g⁻¹` fixes every `x` in `j(E)`. The membership statements are unfolded
through `Subgroup.mem_subgroupOf` and `change` (which unfolds
`closedFixingSubgroup`). By the key step applied to `g⁻¹ ∈ H₀`, the element
`g⁻¹ x` lies in `j(E)`, so `n` fixes it. Hence
`g (n (g⁻¹ x)) = g (g⁻¹ x) = x`.

The proof uses only Mathlib and the definitions the statement already
imports. No hypothesis or public auxiliary declaration is added. The proof uses only
local algebra and normality instances; the key step is a local `have`.

## Relation to the original proof

The original source (lines 251–296) proves the theorem by transport: it
builds the abstract finite Galois extension
`finiteGaloisAbstractExtensionOfEmbedding F E jI` over the intrinsic base of
`F`, takes its normality field `EI.normal`, and maps it to the ambient
subgroups along the isomorphism `intrinsicBaseEquivAmbientEmbeddedField`,
using `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField` and
`Subgroup.Normal.map`. The implemented proof avoids these source
constructions and argues directly inside `SeparableClosure K`. The source
also uses `e` only through those constructions; the implemented proof does
not need it.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>),
SHA-256 `6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The theorem `LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal`
has its docstring at lines 219–220, its signature at lines 221–250 and its
proof at lines 251–296. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` | Published `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normalStatement` (U003 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the proof is replaced as
described above; the source imports are replaced by the single U003
Statements import; all other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

Worker 218 prepared this contribution from Worker 57's shared draft, checked
its source correspondence and clarified the documentation of local instances
and the module's scope. The Lean proof is unchanged from that draft.

This module contains only the M274.003 proof. The separate M274.004
finiteness target is outside this contribution.
