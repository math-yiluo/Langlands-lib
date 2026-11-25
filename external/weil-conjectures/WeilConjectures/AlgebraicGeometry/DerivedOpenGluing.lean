/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenGluingObjects
import WeilConjectures.AlgebraicGeometry.SchemeDerivedHomGluing

/-! # Gluing derived complexes and compatible morphisms on two opens

Source: literature/stacks-project/cohomology.tex, Tag 08DG (Lemma 20.45.1)
(blueprint: lem-sc-derived-open-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem compatible_composites
    {C CU CV CW : Type*} [Category C] [Category CU] [Category CV] [Category CW]
    (RU : C ⥤ CU) (RV : C ⥤ CV) (RW : C ⥤ CW)
    (SU : CU ⥤ CW) (SV : CV ⥤ CW)
    (eU : RU ⋙ SU ≅ RW) (eV : RV ⋙ SV ≅ RW)
    {F E : C} {A : CU} {B : CV}
    (iU : RU.obj F ≅ A) (iV : RV.obj F ≅ B) (c : SU.obj A ≅ SV.obj B)
    (ht : eU.inv.app F ≫ SU.map iU.hom ≫ c.hom = eV.inv.app F ≫ SV.map iV.hom)
    (a : A ⟶ RU.obj E) (b : B ⟶ RV.obj E)
    (hab : SU.map a ≫ eU.hom.app E = c.hom ≫ SV.map b ≫ eV.hom.app E) :
    eU.inv.app F ≫ SU.map (iU.hom ≫ a) ≫ eU.hom.app E =
      eV.inv.app F ≫ SV.map (iV.hom ≫ b) ≫ eV.hom.app E := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hab]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ SV.map b ≫ eV.hom.app E) ht

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
-- Additivity of the three-fold composite restriction functors exceeds the default size.
set_option maxHeartbeats 500000 in
-- Elaborating the restriction functors and their comparison isomorphisms needs this budget.
/-- Derived complexes and compatible morphisms glue across a two-open cover of a scheme.
D(O_X), D(O_U), D(O_V), D(O_(U ∩ V)) are `schemeDerivedCategory` of `X`, `U.toScheme`,
`V.toScheme`, `(U ⊓ V).toScheme`. Restriction from X to an open W is restriction to the
localized site followed by the canonical equivalence `Scheme.Modules.overEquiv W` with the
open subscheme's site; restriction from U (or V) to U ∩ V transports back along
`overEquiv U`, restricts along `U ⊓ V ⟶ U` and transports along `overEquiv (U ⊓ V)`.
The transition and compatibility equations use the canonical comparison of the iterated
restriction X → U → U ∩ V with the direct one (unit of `overEquiv U` and
`SheafOfModules.overFunctorMap`).
Source: Stacks Project, Cohomology, Tag 08DG (Lemma 20.45.1)
(blueprint: lem-sc-derived-open-gluing).
Proof:
1. Form the difference map from `Rj_U A ⊕ Rj_V B` to `Rj_W (B|W)`, using `c` on
   the U component, where `W = U ∩ V`. Complete it to a distinguished triangle with
   first term `F` (`def-weil-abstract-derived-category`).
2. Restrict to U using `lem-pc-restrict-derived-direct-image-open` (Tag 08FE), with
   the three open immersions j_U, j_V and j_W. The second arrow has an identity
   component and a section, so the split-cone calculation identifies `F|U` with A.
   Similarly `F|V` is B, and the two identifications induce exactly c on W.
3. Compose these identifications with a and b. Their restrictions agree on W by
   the transition equation and the assumed compatibility of a, b and c.
4. Apply `lem-sc-derived-hom-mayer-vietoris` to F and E to lift this compatible
   pair to a global morphism. Its two restrictions are the prescribed composites. -/
theorem derived_open_gluing
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.obj A ≅
      (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.obj B) :
    ∃ (F : schemeDerivedCategory X)
      (iU : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj F ≅ A)
      (iV : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj F ≅ B),
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).inv.app F ≫
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map iU.hom ≫ c.hom =
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv V).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).inv.app F ≫
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map iV.hom ∧
      ∀ (E : schemeDerivedCategory X)
        (a : A ⟶ (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E)
        (b : B ⟶ (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj E),
        (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map a ≫
          ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_left))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).hom.app E =
        c.hom ≫ (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V))).mapDerivedCategory.map b ≫
          ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V))
          (Equivalence.inverse
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V) ⋙
          SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
            (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv (U ⊓ V)))) ≪≫
        Functor.mapDerivedCategoryNatIso
          (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V)
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (Scheme.Modules.overEquiv V).unitIso.symm _ ≪≫
                Functor.leftUnitor _) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) (homOfLE inf_le_right))
            (Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U ⊓ V)))
              (D := SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (U ⊓ V))))).hom.app E →
        ∃ (f : F ⟶ E),
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.map f = iU.hom ≫ a ∧
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
            (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv V)).mapDerivedCategory.map f = iV.hom ≫ b := by
  set_option backward.isDefEq.respectTransparency true in
  have h := derived_open_gluing_objects.{u, w} X U V hcover A B c
  obtain ⟨F, iU, iV, ht⟩ := h
  refine ⟨F, iU, iV, ht, ?_⟩
  intro E a b hab
  apply scheme_derived_hom_gluing.{u, w} X U V hcover F E (iU.hom ≫ a) (iV.hom ≫ b)
  exact compatible_composites _ _ _ _ _ _ _ iU iV c ht a b hab

end AlgebraicGeometry
