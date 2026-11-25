/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations

/-! # Hom transport from coherent affine object comparisons
Source: Stacks Project, Tags 09RE and 0D5S. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The limit Hom equation follows from the natural comparison and object triangles.
Source: Stacks Project, Tag 09RE and derived pullback composition, Tag 0D5S.
(blueprint: lem-pc-affine-model-limit-hom-equation-of-coherent-objects).

Proof: Fix the arrow from j to the cocone point.
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
zero complexes and coincident labelled objects. -/
theorem affineModelLimitHomEquation_of_coherent_objects
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
    ∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      m.βE.inv ≫ (affineModelLocalizedTilde C.pt _ dlim).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
          (C.ι.app ⟨i, le_rfl⟩).hom
          (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K a) ≫ m.βK.hom =
      perfectLimitMap R c s j.val.property
        ((m.αE j).inv ≫
          (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (m.αK j).hom) := by
  intro j a
  change _ = perfectHomMap s (affineModelLimitArrow R c j) _
  rw [perfectHomMap]
  have hE := (m.hlim j).1
  have hK := (m.hlim j).2
  generalize hε : perfectHomComparison s (affineModelLimitArrow R c j) = ε at hE hK ⊢
  exact affineModel_scalarConjugation_nat
    (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
    (C.ι.app ⟨i, le_rfl⟩).hom
    (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K
    (affineModelLocalizedTilde (F.obj j.val) _ (d j))
    (affineModelLocalizedTilde C.pt _ dlim)
    (derivedPullback (baseChangeMap s (affineModelLimitArrow R c j)))
    (m.θlim j)
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property)))))
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))) P Q
    (m.αE j) (m.αK j) m.βE m.βK ε hE hK a

end AlgebraicGeometry
