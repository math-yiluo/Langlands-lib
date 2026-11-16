# Frobenius action remainders have degree zero

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusActionRemainder_mem_degreeKernel`, the proof phase of
M053.004 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m049-m072.md#m053).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusActionRemainder_mem_degreeKernelStatement` applied to the
theorem's parameters:

```lean
theorem frobeniusActionRemainder_mem_degreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    frobeniusActionRemainder_mem_degreeKernelStatement D K L hLK φ σ hφ
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]`. The theorem then takes `D`, `K`, `L`, `hLK`, the instance binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]`, the Frobenius elements `φ σ` and `hφ : D.frobeniusExponent K L hLK φ = 1`, exactly as the published target and the source theorem. `extensionSubgroup` is the published `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation `L.toSubgroup.subgroupOf K.field.toSubgroup`.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder.Statements`, the target is the proposition

```lean
D.frobeniusActionRemainder K L hLK φ σ ∈
  (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker
```

Here `D : DegreeData G` (M010.002), `K` is a finite-residue abstract field (M010.021) and `L ≤ K` a closed subgroup with `G_L` normal in `G_K`. The elements `φ σ` are Frobenius elements (M012.009): elements of `G_K ⧸ (G_L ⊓ I_K)` whose normalized degree (M012.005) is `(Multiplicative.ofAdd 1) ^ n` for some natural `n > 0`, and `frobeniusExponent` (M014.012) is the chosen such `n`. `frobeniusActionRemainder` (M053.003) is the element `φⁿ σ⁻¹` with `n` the Frobenius exponent of `σ`, and `extensionNormalizedDegreeContinuous` (M014.016) is the normalized degree M012.005 as a continuous monoid homomorphism. So the target says: if `φ` has Frobenius exponent one, then `φⁿ σ⁻¹` has normalized degree zero (the identity of `Multiplicative ZHat`). No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder.Statements`, which defines the target and, through its imports, every name used in the proof.

The module opens `CyclicCohomology`, for `extensionSubgroup`, as the source does.

## Implemented proof

The proof is the source proof, with one prerequisite inlined. The source's first step `change D.extensionNormalizedDegree K L hLK (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) = 1` is kept; it also unfolds the published proposition, the remainder M053.003 and the kernel membership. The source then rewrites with `map_mul`, `map_pow` and `map_inv` and twice with M014.014 `extensionNormalizedDegree_frobenius_eq_pow` (normalized degree of a Frobenius element `τ` is `(ofAdd 1) ^ frobeniusExponent τ`), at `σ` and at `φ`. The proof of M014.014 is not in the Library; its source proof is the term `(Exists.choose_spec τ.2).2`, the second half of the defining property of the chosen exponent. The module states these two instances as the local facts `hσ` and `hφpow`, proved by that term, and rewrites with them in the source's order. The source's remaining rewrites `hφ` and `pow_one` leave `x * x⁻¹ = 1` with `x = (ofAdd 1) ^ n`, `n` the exponent of `σ`, which `mul_inv_cancel` closes.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`, lines 142–157](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean#L142-L157):
the docstring at lines 142–143 and the theorem at lines 144–157. It lies in `namespace ClassFormation` (line 22), after `universe u` (line 20), with `open KummerTheory` (line 24), `open CyclicCohomology` (line 25), its `noncomputable section` (line 27), `open CategoryTheory` (line 29), `section actionRemainderAlgebra` (line 126), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 128) and `namespace DegreeData` (line 130). The inlined prerequisite M014.014 is at [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`, lines 319–327](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean#L319-L327) (SHA-256 `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`). The source is:

```lean
/-- If `φ` has Frobenius exponent one, its action remainder has normalized
degree zero. -/
theorem frobeniusActionRemainder_mem_degreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    D.frobeniusActionRemainder K L hLK φ σ ∈
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  change D.extensionNormalizedDegree K L hLK
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) = 1
  rw [map_mul, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ,
    pow_one, mul_inv_cancel]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`;
its SHA-256 is `913562295296948d960ad31a3f03b201046ba2089b481705109cd238619c3445`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `frobeniusActionRemainder_mem_degreeKernelStatement D K L hLK φ σ hφ` as its type; the source's initial `change` unfolds it;
- replace the source's two rewrites with M014.014 `D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ` and `… φ` (not proved in the Library) by rewrites with the local facts `hσ` and `hφpow`, proved by the source proof `(Exists.choose_spec _.2).2` of M014.014, with comments;
- omit `open KummerTheory`, `open CategoryTheory`, the `noncomputable section`, the section header and all other source declarations; keep `universe u`, `open CyclicCohomology`, the variable line and `namespace DegreeData`.

The theorem name, docstring, binders, the source `change` and the source rewrite order are kept. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

The module was written by Worker 5264 and shared as revision 1 of the draft of
Task 7075 (`0454080b-e432-4027-b99d-a958401cb38d`). Worker 745 checked it
against the pinned original and the published statement module, recompiled it
over Library commit `72480b70c88adff84a438bd7029d64ee3977469c` on 16 November
2026 (no errors or warnings; axioms `propext`, `Classical.choice`,
`Quot.sound`) and staged it without changing the Lean file.

This module proves only M053.004. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
