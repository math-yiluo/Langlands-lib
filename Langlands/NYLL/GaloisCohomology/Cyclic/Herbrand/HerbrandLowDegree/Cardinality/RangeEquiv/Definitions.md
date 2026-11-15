# NYLL M117.013: ranges of conjugate `ModuleCat ℤ` morphisms

The paired Lean file adapts one definition of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`.
The pinned source file has SHA-256
`2757f501b1f901072b2292af5db735cc54db7f11b2403c3354a37f82fdda8226`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `CyclicCohomology.ProfiniteCohomology.Herbrand.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.` |
| --- | --- | --- | --- | --- | --- |
| M117.013 | `moduleCatRangeEquivOfConjugate` | 234–235 | 236–242 | 243–277 | `moduleCatRangeEquivOfConjugate` |

The source imports
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison` and
`Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`
(lines 7–8). The context of the definition is `namespace CyclicCohomology`
(line 19), `noncomputable section` (line 21), `namespace ProfiniteCohomology`
and `namespace Herbrand` (lines 23–24), `open CategoryTheory` (line 26), the
variable line `variable {G A B C : Type}` (line 28) and an anonymous
`section` (lines 30–365) with the instance variables
`[CommGroup G] [Fintype G]`, `[CommGroup A] [CommGroup B] [CommGroup C]` and
the three `MulDistribMulAction` instances (lines 32–35).

The definition binds its own objects `X Y X' Y'` of `ModuleCat.{0} ℤ` and
mentions none of the section variables, so Lean includes none of them; its
telescope is exactly the binders shown below. The other declarations of the
source file are not part of this module.

The definition uses only Mathlib: `ModuleCat`, morphisms `⟶`, composition
`≫`, isomorphisms `≅` with `hom`, `inv`, `inv_hom_id_assoc`,
`hom_inv_id_apply` and `inv_hom_id_apply`, `cancel_epi`, `cancel_mono`,
`Category.assoc` and `Category.comp_id` (from `CategoryTheory`), the
underlying linear map `ModuleCat.Hom.hom` with `toAddMonoidHom`,
`AddMonoidHom.toMultiplicative`, `Multiplicative.ofAdd` and `toAdd`,
`MonoidHom.range`, `Subtype.ext` and `Equiv`.

## Definition

```lean
noncomputable def moduleCatRangeEquivOfConjugate
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    MonoidHom.range f.hom.toAddMonoidHom.toMultiplicative ≃
      MonoidHom.range g.hom.toAddMonoidHom.toMultiplicative := by
  have hnat : f ≫ eY.hom = eX.hom ≫ g := by
    rw [← cancel_epi eX.inv]
    simpa only [Category.assoc, eX.inv_hom_id_assoc] using h
  have hinv : eX.inv ≫ f = g ≫ eY.inv := by
    rw [← cancel_mono eY.hom]
    simpa only [Category.assoc, eY.inv_hom_id, Category.comp_id] using h
  refine
    { toFun := fun y => ⟨Multiplicative.ofAdd (eY.hom y.1.toAdd), ?_⟩
      invFun := fun y => ⟨Multiplicative.ofAdd (eY.inv y.1.toAdd), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.hom x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change g (eX.hom x.toAdd) = eY.hom y.1.toAdd
    have hx' : f x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact (congrArg (fun k : X ⟶ Y' => k x.toAdd) hnat).symm
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.inv x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change f (eX.inv x.toAdd) = eY.inv y.1.toAdd
    have hx' : g x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact congrArg (fun k : X' ⟶ Y => k x.toAdd) hinv
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.hom_inv_id_apply y.1.toAdd
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.inv_hom_id_apply y.1.toAdd
```

Given morphisms `f : X ⟶ Y` and `g : X' ⟶ Y'` of `ℤ`-modules and
isomorphisms `eX : X ≅ X'` and `eY : Y ≅ Y'` with
`eX.inv ≫ f ≫ eY.hom = g`, the definition is an equivalence between the
range of `f` and the range of `g`, each viewed as a subgroup of the
multiplicatively tagged target. The forward map sends `y` to the image of
`y` under `eY.hom` and the inverse map uses `eY.inv`; the tactic steps prove
that these images lie in the ranges and that the two maps are mutually
inverse.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition lies in
   `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`.
2. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition. The declaration,
   its docstring and its body are copied verbatim, with the source line
   breaks.
3. Replace the two source imports by the Mathlib modules
   `Mathlib.Algebra.Category.ModuleCat.Basic` (of `ModuleCat` and its
   morphisms) and `Mathlib.Algebra.Group.TypeTags.Hom` (of
   `AddMonoidHom.toMultiplicative`). No NYLL declaration is needed.
4. Omit the source variable lines 28 and 32–35 and the anonymous section:
   the definition mentions none of their variables, so its telescope is
   unchanged. Retain the namespaces, the noncomputable section and the open
   of `CategoryTheory`. Omit the other declarations of the source file.
5. No linter option, helper declaration or instance is added.

This is a definition only. It discharges no host Herbrand-quotient,
class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
