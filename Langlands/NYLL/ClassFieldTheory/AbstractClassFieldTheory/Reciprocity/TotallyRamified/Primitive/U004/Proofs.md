# The H⁻¹ primitive of a difference with equal norms

This module proves the theorem
`Langlands.NYLL.ClassFormation.ValuationData.abstractReciprocity_exists_hMinusOne_primitive`, the proof phase of
M083.004 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m083).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.ValuationData.abstractReciprocity_exists_hMinusOne_primitiveStatement` applied to the
theorem's parameters:

```lean
theorem abstractReciprocity_exists_hMinusOne_primitive
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    abstractReciprocity_exists_hMinusOne_primitiveStatement
      hcf E hnormal g hg u w hnorm
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, where `Langlands.NYLL.IntegralRepGroupType` is `Type 0` (Mathlib's `Rep ℤ G` fixes the acting group to universe zero), and, in `namespace ValuationData`, `{D : DegreeData G} {A : Rep ℤ G}`; `D` does not occur in the theorem. The theorem then takes `hcf`, `E`, `hnormal`, `g`, `hg`, `u`, `w` and `hnorm`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.Primitive.Statements`, the target is the proposition

```lean
let M := extensionFixedRepresentation A E.base.field E.field.field
  E.below hnormal
∃ a : M.V,
  M.ρ g a - a =
    (extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal).symm
      (w - u)
```

Write `K = E.base.field` and `L = E.field.field` for the finite abstract field extension `E` (M010.130), with `G_L ≤ G_K` (`E.below`), `G_L` normal in `G_K` (`hnormal`) and `g` a generator of the finite quotient `G_K ⧸ G_L` (`hg`). The representation `M` is `A^{G_L}` as a representation of `G_K ⧸ G_L` (`CyclicCohomology.extensionFixedRepresentation`, M004.003), and `extensionFixedRepresentationEquiv` (M073.001) identifies its carrier with the additive subgroup `A^{G_L}` (`KummerTheory.ambientFixedAddSubgroup`, M023.001). The target says: if `u w ∈ A^{G_L}` have equal relative norms `N_{L/K}` (`relativeNorm`, M024.009) and `A` satisfies the class-field axiom (`SatisfiesClassFieldAxiom`, M072.002), then `w - u` is `g a - a` for some `a ∈ A^{G_L}`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.Primitive.Statements`, which defines the target;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.U005.Proofs`, the published proof of M072.005 `SatisfiesClassFieldAxiom.tateHMinusOne_isZero`: under the class-field axiom, `Ĥ⁻¹` of the fixed representation of every finite cyclic subextension (M032.001) vanishes;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs`, the published proof of M073.004 `extensionFixedRepresentation_action_coe`: the action of a coset on the descended representation is the relative coset action `relativeCosetAction` (M024.001) on the underlying coefficient;
- `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U007.Proofs`, the published proof of M004.007 `CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero`: for a representation of a finite cyclic group with generator `g` and vanishing `Ĥ⁻¹`, every element of norm zero has the form `g a - a`.

The module opens `KummerTheory` (for `ambientFixedAddSubgroup`), `CyclicCohomology` (for `extensionSubgroup` and `extensionFixedRepresentation`) and `CategoryTheory` (for `Limits.IsZero`), as the source does.

## Implemented proof

After `show` restates the published proposition in its unfolded form (the `let M` and the existential), the proof is the source proof with one prerequisite reproduced. It installs `hnormal`, the finiteness `E.finiteQuotient` and a `Fintype` structure on `G_K ⧸ G_L` as local instances, sets `z := e.symm (w - u)` with `e` the equivalence M073.001, and proves `hzNorm : M.norm.hom z = 0` by the source `calc`: by `Subtype.ext` it suffices that the coefficient of the norm of `z` (Mathlib's `Rep.norm`, the sum of the action over the finite group) is zero; it is the coefficient of `N_{L/K}(w - u)`, which by `map_sub` and `hnorm` is `0`. The first step of this `calc` is M073.005 `extensionFixedRepresentation_norm_coe`, whose proof is not in the Library, so the module reproduces its source proof as the private theorem `extensionFixedRepresentation_norm_coe_aux`, with the same binders and statement. That proof unfolds `Rep.norm`, `Representation.norm` and the relative norm value `relativeNormValue` (M024.005), writes the sum of linear maps applied to `a` as a sum (`LinearMap.sum_apply`), pushes the coercion to `A.V`, written as an additive homomorphism, through the sum (`map_sum`), and compares the sums termwise with the published M073.004. Its own first step, the source rewrite with M024.010 `relativeNorm_apply_coe` (not proved in the Library), becomes a rewrite with the local equation `hcoe`, proved by the source proof `rfl` of M024.010. The main proof then packages `L | K` with the generator `g` as a finite cyclic subextension `Ecf` (M032.001) of `E.base`, obtains `hzero : Limits.IsZero (tateCohomology M (-1))` from the published M072.005 by `simpa`, which unfolds `Ecf`, `FiniteCyclicSubextension.fixedRepresentation` (M032.016) and the Statement proposition `SatisfiesClassFieldAxiom.tateHMinusOne_isZeroStatement` of M072.005, and applies the published M004.007 to `M`, `g`, `hg`, `hzero`, `z` and `hzNorm`, which yields the required `a`. `tateCohomology` is Mathlib's (`Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean`, line 145).

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`, lines 237–294](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean#L237-L294):
the docstring at lines 237–238 and the theorem at lines 239–294. It lies in `namespace ClassFormation` (line 27), with `open KummerTheory` (line 29), `open CyclicCohomology` (line 31), its `noncomputable section` (line 35), `open CategoryTheory` (line 37), the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 40), `namespace ValuationData` (line 89) and the variables `{D : DegreeData G} {A : Rep ℤ G}` (line 91). The reproduced M073.005 is at [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`, lines 102–139](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean#L102-L139) (docstring 102–103; SHA-256 `8124bbdd42702e1dba3060f8a2f14c6d66ead33c113d0b4310bc6157fea19bb9`), in `namespace ClassFormation` with the same variable line; the inlined M024.010 is at [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`, lines 163–171](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean#L163-L171) (SHA-256 `5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`), whose proof is `rfl`. The source is:

```lean
/-- The class-field axiom, in representative form: equality of two actual relative
norms yields the element `a` for which `a^σ-a = v-u`. -/
theorem abstractReciprocity_exists_hMinusOne_primitive
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let z : M.V :=
    (extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal).symm (w - u)
  have hzNorm : M.norm.hom z = 0 := by
    apply Subtype.ext
    calc
      (M.norm.hom z).1 =
          ((relativeNorm A E.base.field E.field.field E.below (w - u) :
            ambientFixedAddSubgroup A E.base.field) : A.V) :=
        extensionFixedRepresentation_norm_coe A E.base.field E.field.field
          E.below hnormal z
      _ = ((relativeNorm A E.base.field E.field.field E.below w -
          relativeNorm A E.base.field E.field.field E.below u :
            ambientFixedAddSubgroup A E.base.field) : A.V) := by
        rw [map_sub]
      _ = 0 := by rw [hnorm, sub_self]; rfl
  let Ecf : FiniteCyclicSubextension E.base :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  have hzero : Limits.IsZero (tateCohomology M (-1)) := by
    simpa [Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using
        hcf.tateHMinusOne_isZero E.base Ecf
  obtain ⟨a, ha⟩ :=
    CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      M g hg hzero z hzNorm
  exact ⟨a, ha⟩
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`;
its SHA-256 is `0294844f85bffa1a3b4bc255c93c644b01f9e43dcd863a5e64718af4abcc0cc2`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `abstractReciprocity_exists_hMinusOne_primitiveStatement hcf E hnormal g hg u w hnorm` as its type, unfolded by an initial `show`;
- reproduce the source theorem M073.005 `extensionFixedRepresentation_norm_coe` (not proved in the Library) as the private theorem `extensionFixedRepresentation_norm_coe_aux` with its source docstring adapted, binders, statement and proof, except that its rewrite with M024.010 `relativeNorm_apply_coe` (not proved in the Library) becomes a rewrite with the local equation `hcoe`, proved by `rfl`; use it in place of M073.005 in the `calc`, with a comment;
- add the Statement proposition `SatisfiesClassFieldAxiom.tateHMinusOne_isZeroStatement` to the `simpa` set that derives `hzero` from M072.005, since the published theorem has that proposition as its type;
- omit the `noncomputable section` and all other source declarations; keep the three `open` lines, the variable lines and the source comment on `IntegralRepGroupType`.

The theorem name, docstring, binders and every other source proof step are kept. The retained original belongs to registered source
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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

The module was written by Worker 5264 and shared as revision 1 of the draft of
Task 7075 (`0454080b-e432-4027-b99d-a958401cb38d`). Worker 745 checked it
against the pinned original and the published statement module, recompiled it
over Library commit `72480b70c88adff84a438bd7029d64ee3977469c` on 16 November
2026 (no errors or warnings; axioms `propext`, `Classical.choice`,
`Quot.sound`) and staged it without changing the Lean file.

This module proves only M083.004. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
