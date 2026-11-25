/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons

/-! # Hom transport from coherent affine object comparisons
Source: Stacks Project, Tags 09RE and 0D5S. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An isomorphism can be specified by its exact value. -/
private theorem exists_iso_value {A : Type*} [Category A] {X Y : A} (e : X ≅ Y) :
    ∃ t : X ≅ Y, t = e := ⟨e, rfl⟩

/-- Keep the specified isomorphism behind the choice operation during type checking. -/
private noncomputable def pinnedIso {A : Type*} [Category A] {X Y : A} (e : X ≅ Y) :
    X ≅ Y := Classical.choose (exists_iso_value e)

/-- The pinned value is exactly the supplied isomorphism. -/
private theorem pinnedIso_eq {A : Type*} [Category A] {X Y : A} (e : X ≅ Y) :
    pinnedIso e = e := Classical.choose_spec (exists_iso_value e)

/-- Express Hom transport through an equal pinned comparison. -/
private theorem homMap_pinned {X S : Scheme.{u}} (s : X ⟶ S)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {T T' : Over S} (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s g a =
      (pinnedIso (perfectHomComparison s g)).hom.app P ≫
        (derivedPullback (baseChangeMap s g)).map a ≫
          (pinnedIso (perfectHomComparison s g)).inv.app Q := by
  rw [pinnedIso_eq]
  rfl

/-- Keep the stage arrow at the abstract Hom transport level. -/
private theorem stageMap_asHomMap
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
    {P Q : schemeDerivedCategory Y}
    (a : (derivedPullback (pullback.fst s
        (Spec.map (R.map (homOfLE j.val.property))))).obj P ⟶
      (derivedPullback (pullback.fst s
        (Spec.map (R.map (homOfLE j.val.property))))).obj Q) :
    perfectStageMap R s j.val.property hjk a =
      perfectHomMap s (affineModelStageArrow R j k hjk) a := by
  rfl

/-- The stage Hom equation follows from the natural comparison and object triangles.
Source: Stacks Project, Tag 09RE and derived pullback composition, Tag 0D5S.
(blueprint: lem-pc-affine-model-stage-hom-equation-of-coherent-objects).

Proof: Fix the finite-stage arrow j→k.
Apply naturality of the supplied full two-label comparison θ to the given chain
map a; it need not descend to the bottom. Scalar reassociation identifies
scalarExtensionHom with κE.hom followed by extension of a followed by κK.inv,
where κ is affineModelScalarAssocIso. The two object triangles express the
comparison at the target as κ, θ, pullback of the source comparison and the
inverse perfectHomComparison. Substitute these formulas and expand map_comp.
Cancel adjacent inverse pairs, use naturality of θ, then cancel its inverse
pair. The result is exactly the conjugated Hom transport written below.
Proof irrelevance identifies the generated pullback-instance proofs with the
named arrow representation. The argument includes identity arrows, zero rings,
zero complexes and coincident labelled objects.

Implementation: first rewrite the named stage transport as perfectHomMap, then
use an equal pinned copy of its comparison in both the transport and the object
triangles. The pin is chosen from a proved equality to the supplied comparison,
so its value is completely determined. Apply the already proved
`affineModel_scalarConjugation_nat`. The private transport equations prevent
kernel conversion from unfolding the large comparison construction. -/
theorem affineModelStageHomEquation_of_coherent_objects
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (m : AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) :
    ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      (m.αE k).inv ≫ (affineModelLocalizedTilde (F.obj k.val) _ (d k)).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
          (F.map (homOfLE k.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk)))
          E K a) ≫ (m.αK k).hom =
      perfectStageMap R s j.val.property hjk
        ((m.αE j).inv ≫
          (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (m.αK j).hom) := by
  intro j k hjk a
  rw [stageMap_asHomMap, homMap_pinned]
  have hs := m.hstage j k hjk
  dsimp only [affineModelStageObjectCoherence] at hs
  rw [← pinnedIso_eq (perfectHomComparison s (affineModelStageArrow R j k hjk))] at hs
  exact affineModel_scalarConjugation_nat
    (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
    (F.map (homOfLE k.property)).hom
    (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk)))
    E K (affineModelLocalizedTilde (F.obj j.val) _ (d j))
    (affineModelLocalizedTilde (F.obj k.val) _ (d k))
    (derivedPullback (baseChangeMap s (affineModelStageArrow R j k hjk)))
    (m.θ j k hjk)
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property)))))
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.val.property)))))
    P Q (m.αE j) (m.αK j) (m.αE k) (m.αK k)
    (pinnedIso (perfectHomComparison s (affineModelStageArrow R j k hjk)))
    hs.1 hs.2 a

end AlgebraicGeometry
