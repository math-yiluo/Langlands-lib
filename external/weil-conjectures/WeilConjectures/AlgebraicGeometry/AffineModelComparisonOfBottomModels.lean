/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModelComparisonData
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects
import WeilConjectures.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects

/-! # Propagation of bottom-stage affine models
Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-comparison-of-bottom-models). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Propagate two bottom-stage models through compatible affine coordinates.
Source: Stacks Project, Tag 09RE, affine calculation, and Tags 0D5S and 06Y1.
(blueprint: lem-pc-affine-model-comparison-of-bottom-models).

Proof: hE and hK are the acyclic-tensor K-flat criterion. For each stage j
pull aE and aK back along the bottom-to-j
base-change arrow, and compose with perfectHomComparison. Compute this
pullback on E and K by the K-flat affine pullback comparison, conjugated by
the localized pushforwards hd at the bottom and at j. The transition equation
for σ identifies the affine map with that base-change arrow. At the limit use
the same construction with hdlim and the limit transition equation. Extension
of scalars preserves K-flatness, so this calculation applies again to every
stage model. For a chain map at j, use naturality of the affine comparison for
the map j→k, respectively j→C.pt. Reassociation of scalar extension is exactly
the two associativity components in scalarExtensionHom. The counit
characterization of the derived composition comparisons, and its associativity
law, identify these reassociations with perfectHomComparison. Expand the
conjugations and cancel each adjacent inverse pair; this gives both Hom
equations in affineModelComparisonData. Package the supplied d and dlim and
the four constructed isomorphisms. The bottom isomorphisms are arbitrary:
their pullbacks appear on both sides of every naturality square and cancel.
No chain map is required to descend to the bottom, and no directedness or
colimit hypothesis is used. Identity arrows, zero rings, empty spectra and
zero models are covered by the same naturality and composition calculations. -/
theorem affineModelComparisonData_of_bottom_models
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hE : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ,
      L.Acyclic →
        (CochainComplex.mapBifunctor L E
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ,
      L.Acyclic →
        (CochainComplex.mapBifunctor L K
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic)
    (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i)))
    (htrans :
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom))
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      DerivedCategory.Q ⋙ (d j).functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace))
        (SheafOfModules.{u}
          (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace))
        _ _ _ _
        (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace))
        (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward τ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (aE : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj
      (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩))
        (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤
          SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
          (tilde.functor (F.obj ⟨i, le_rfl⟩)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E)) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj P)
    (aK : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj
      (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩))
        (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤
          SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
          (tilde.functor (F.obj ⟨i, le_rfl⟩)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K)) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj Q) :
    affineModelComparisonData R c i Y s P Q F C E K := by
  rename_i hD
  obtain ⟨m⟩ := @exists_affineModelCoherentObjectComparisons
    I _ R c i Y _ s hD P Q F C E K hE hK σ τ htrans d dlim hd hdlim aE aK
  apply affineModelComparisonData_of_hom_equations R c i Y s P Q F C E K d dlim
    m.αE m.αK m.βE m.βK
  · exact affineModelStageHomEquation_of_coherent_objects
      R c i Y s P Q F C E K d dlim m
  · exact affineModelLimitHomEquation_of_coherent_objects
      R c i Y s P Q F C E K d dlim m

end AlgebraicGeometry
