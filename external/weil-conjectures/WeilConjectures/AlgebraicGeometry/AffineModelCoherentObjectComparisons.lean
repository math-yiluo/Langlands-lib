/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.InducedCategory
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonCoherence
import WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangle

/-! # Coherent affine object comparisons
Source: Stacks Project, Tags 09RE, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Termwise tilde on module complexes, with its zero-map proof fixed once.
Source: Mathlib's tilde.functor and Functor.mapHomologicalComplex.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelTildeComplex (A : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) ℤ :=
  @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
    (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
    _ _ _ _ (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
    ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)

/-- Localization of termwise tilde followed by the supplied coordinate equivalence.
Source: the defining affine comparison functor in Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable def affineModelLocalizedTilde (A : CommRingCat.{u}) (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory X where
  obj M := d.functor.obj (DerivedCategory.Q.obj ((affineModelTildeComplex A).obj M))
  map f := d.functor.map (DerivedCategory.Q.map ((affineModelTildeComplex A).map f))
  map_id M := by simp
  map_comp f g := by simp

/-- The map equation of the localized tilde functor, without unfolding its functor record.
Source: the explicit localized tilde construction.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
theorem affineModelLocalizedTilde_map (A : CommRingCat.{u}) (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X)
    {M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ N) :
    (affineModelLocalizedTilde A X d).map f =
      d.functor.map (DerivedCategory.Q.map ((affineModelTildeComplex A).map f)) := by
  rfl

/-- The two scalar-extended models, with labels retained when they coincide.
Source: Mathlib's induced category; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelScalarPair {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (E K : CochainComplex (ModuleCat.{u} A) ℤ) (q : Bool) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  cond q (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E)
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K)

/-- Scalar-extension reassociation, including the specified equality of ring maps.
Source: Stacks Project, Tag 09RE; `ModuleCat.extendScalarsComp`.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[irreducible]
noncomputable def affineModelScalarAssocIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj M) :=
  eqToIso (congrArg (fun t ↦
    ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≪≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).app M

/-- The forward scalar reassociation map, from its explicit construction. 
(blueprint: lem-pc-affine-model-coherent-object-comparisons)
-/
theorem affineModelScalarAssocIso_hom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineModelScalarAssocIso f g h hc M).hom =
      eqToHom (congrArg (fun t ↦
        ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≫
          (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).hom.app M := by
  unfold affineModelScalarAssocIso
  rfl

/-- The inverse scalar reassociation map, from its explicit construction. 
(blueprint: lem-pc-affine-model-coherent-object-comparisons)
-/
theorem affineModelScalarAssocIso_inv
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineModelScalarAssocIso f g h hc M).inv =
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).inv.app M ≫
        eqToHom (congrArg (fun t ↦
          ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc.symm) := by
  unfold affineModelScalarAssocIso
  rfl

/-- The finite-stage base arrow in the over category.
Source: Spec functoriality; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelStageArrow {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) {i : I}
    (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k) :
    Over.mk (Spec.map (R.map (homOfLE k.val.property))) ⟶
      Over.mk (Spec.map (R.map (homOfLE j.val.property))) :=
  Over.homMk (Spec.map (R.map (homOfLE hjk)))
    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)

/-- The arrow from the cocone spectrum to a finite-stage spectrum.
Source: Spec functoriality and cocone naturality; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelLimitArrow {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I}
    (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :
    Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE j.val.property))) :=
  Over.homMk (Spec.map (c.ι.app j.val))
    (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality transports a conjugated map through coherent object comparisons.
Source: naturality and inverse cancellation in Mathlib's category API.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem affineModel_conjugation
    {C D B : Type*} [Category C] [Category D] [Category B]
    (H : C ⥤ D) (G : C ⥤ B) (L : D ⥤ B) (δ : G ≅ H ⋙ L)
    {X Y : C} {U V : D} {Xk Yk U' V' : B}
    (κX : Xk ≅ G.obj X) (κY : Yk ≅ G.obj Y)
    (αX : H.obj X ≅ U) (αY : H.obj Y ≅ V)
    (γX : Xk ≅ U') (γY : Yk ≅ V')
    (εX : U' ≅ L.obj U) (εY : V' ≅ L.obj V)
    (hX : κX ≪≫ δ.app X ≪≫ L.mapIso αX ≪≫ εX.symm = γX)
    (hY : κY ≪≫ δ.app Y ≪≫ L.mapIso αY ≪≫ εY.symm = γY)
    (f : X ⟶ Y) :
    γX.inv ≫ κX.hom ≫ G.map f ≫ κY.inv ≫ γY.hom =
      εX.hom ≫ L.map (αX.inv ≫ H.map f ≫ αY.hom) ≫ εY.inv := by
  have hx := hX.symm
  have hy := hY.symm
  rw [hx, hy]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [δ.hom.naturality_assoc f]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension of a map is conjugation by the explicit reassociation maps.
Source: Stacks Project, Tag 09RE; ModuleCat.extendScalarsComp.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem scalarExtensionHom_assoc
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (E K : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) :
    CochainComplex.scalarExtensionHom f g h hc E K a =
      (affineModelScalarAssocIso f g h hc E).hom ≫
        ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).map a ≫
          (affineModelScalarAssocIso f g h hc K).inv := by
  rw [affineModelScalarAssocIso_hom, affineModelScalarAssocIso_inv]
  dsimp only [CochainComplex.scalarExtensionHom]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Apply naturality and inverse cancellation to scalar reassociation.
Source: Stacks, Tag 09RE, with Mathlib's naturality and scalar-extension APIs.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem affineModel_scalarConjugation
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (E K : CochainComplex (ModuleCat.{u} A) ℤ)
    {D T : Type*} [Category D] [Category T]
    (H : CochainComplex (ModuleCat.{u} B) ℤ ⥤ D)
    (G : CochainComplex (ModuleCat.{u} C) ℤ ⥤ T) (L : D ⥤ T)
    (δ : inducedFunctor (affineModelScalarPair f E K) ⋙
        (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) ⋙ G ≅
      inducedFunctor (affineModelScalarPair f E K) ⋙ H ⋙ L)
    {U V : D} {U' V' : T}
    (αE : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E) ≅ U)
    (αK : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) ≅ V)
    (βE : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj E) ≅ U')
    (βK : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj K) ≅ V')
    (εE : U' ≅ L.obj U) (εK : V' ≅ L.obj V)
    (hE : G.mapIso (affineModelScalarAssocIso f g h hc E) ≪≫ δ.app true ≪≫
      L.mapIso αE ≪≫ εE.symm = βE)
    (hK : G.mapIso (affineModelScalarAssocIso f g h hc K) ≪≫ δ.app false ≪≫
      L.mapIso αK ≪≫ εK.symm = βK)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) :
    βE.inv ≫ G.map (CochainComplex.scalarExtensionHom f g h hc E K a) ≫ βK.hom =
      εE.hom ≫ L.map (αE.inv ≫ H.map a ≫ αK.hom) ≫ εK.inv := by
  have t := affineModel_conjugation
    (inducedFunctor (affineModelScalarPair f E K) ⋙ H)
    (inducedFunctor (affineModelScalarPair f E K) ⋙
      (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) ⋙ G)
    L δ (X := true) (Y := false)
    (G.mapIso (affineModelScalarAssocIso f g h hc E))
    (G.mapIso (affineModelScalarAssocIso f g h hc K))
    αE αK βE βK εE εK hE hK (InducedCategory.homMk (X := true) (Y := false) a)
  rw [scalarExtensionHom_assoc]
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.comp_map, inducedFunctor_map, InducedCategory.homMk_hom,
    Category.assoc] using t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural-isomorphism form of scalar conjugation avoids expanding its components.
Source: naturality and scalar reassociation; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
theorem affineModel_scalarConjugation_nat
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (E K : CochainComplex (ModuleCat.{u} A) ℤ)
    {D T : Type*} [Category D] [Category T]
    (H : CochainComplex (ModuleCat.{u} B) ℤ ⥤ D)
    (G : CochainComplex (ModuleCat.{u} C) ℤ ⥤ T) (L : D ⥤ T)
    (δ : inducedFunctor (affineModelScalarPair f E K) ⋙
        (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) ⋙ G ≅
      inducedFunctor (affineModelScalarPair f E K) ⋙ H ⋙ L)
    {W : Type*} [Category W] (Ufun : W ⥤ D) (Vfun : W ⥤ T) (p q : W)
    (αE : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E) ≅ Ufun.obj p)
    (αK : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) ≅ Ufun.obj q)
    (βE : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj E) ≅ Vfun.obj p)
    (βK : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj K) ≅ Vfun.obj q)
    (ε : Vfun ≅ Ufun ⋙ L)
    (hE : G.mapIso (affineModelScalarAssocIso f g h hc E) ≪≫ δ.app true ≪≫
      L.mapIso αE ≪≫ (ε.app p).symm = βE)
    (hK : G.mapIso (affineModelScalarAssocIso f g h hc K) ≪≫ δ.app false ≪≫
      L.mapIso αK ≪≫ (ε.app q).symm = βK)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) :
    βE.inv ≫ G.map (CochainComplex.scalarExtensionHom f g h hc E K a) ≫ βK.hom =
      ε.hom.app p ≫ L.map (αE.inv ≫ H.map a ≫ αK.hom) ≫ ε.inv.app q := by
  simpa only [Iso.app_hom, Iso.app_inv] using
    affineModel_scalarConjugation f g h hc E K H G L δ
      αE αK βE βK (ε.app p) (ε.app q) hE hK a


section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I : Type u} [Preorder I]
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

/-- Object comparisons at every finite stage for one model.
Source: Stacks, Tag 09RE, affine model formula.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelStageObjects : Type _ :=
  ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
    (affineModelLocalizedTilde (F.obj j.val) _ (d j)).obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property))))).obj P

/-- Object comparison at the cocone point for one model.
Source: Stacks, Tag 09RE, affine model formula.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelLimitObject : Type _ :=
  (affineModelLocalizedTilde C.pt _ dlim).obj
      (((ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom).mapHomologicalComplex (.up ℤ)).obj E) ≅
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P

/-- Natural affine comparisons for finite-stage arrows on the two labelled models.
Source: Stacks, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelStageArrowComparisons : Type _ :=
  ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      (ModuleCat.extendScalars (F.map (homOfLE hjk)).hom).mapHomologicalComplex (.up ℤ) ⋙
        affineModelLocalizedTilde (F.obj k.val) _ (d k) ≅
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      affineModelLocalizedTilde (F.obj j.val) _ (d j) ⋙
        derivedPullback (baseChangeMap s (affineModelStageArrow R j k hjk))

/-- Natural affine comparisons for arrows to the cocone point on both labelled models.
Source: Stacks, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelLimitArrowComparisons : Type _ :=
  ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      (ModuleCat.extendScalars (C.ι.app j.val).hom).mapHomologicalComplex (.up ℤ) ⋙
        affineModelLocalizedTilde C.pt _ dlim ≅
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      affineModelLocalizedTilde (F.obj j.val) _ (d j) ⋙
        derivedPullback (baseChangeMap s (affineModelLimitArrow R c j))

/-- The finite-stage object triangles, independently of conjugated chain maps.
Source: Stacks, Tags 09RE and 0D5S, composition comparisons.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
def affineModelStageObjectCoherence
    (αE : AffineModelStageObjects R i Y s P F E d)
    (αK : AffineModelStageObjects R i Y s Q F K d)
    (θ : AffineModelStageArrowComparisons R i Y s F E K d) : Prop :=
  ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
    let B := derivedPullback (baseChangeMap s (affineModelStageArrow R j k hjk))
    let ε := perfectHomComparison s (affineModelStageArrow R j k hjk)
    let hc := congrArg CommRingCat.Hom.hom
      (F.map_comp (homOfLE j.property) (homOfLE hjk))
    ((affineModelLocalizedTilde (F.obj k.val) _ (d k)).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom hc E) ≪≫
      (θ j k hjk).app true ≪≫ B.mapIso (αE j) ≪≫ (ε.app P).symm = αE k) ∧
    ((affineModelLocalizedTilde (F.obj k.val) _ (d k)).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom hc K) ≪≫
      (θ j k hjk).app false ≪≫ B.mapIso (αK j) ≪≫ (ε.app Q).symm = αK k)

/-- The cocone object triangles, independently of conjugated chain maps.
Source: Stacks, Tags 09RE and 0D5S, composition comparisons.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
def affineModelLimitObjectCoherence
    (αE : AffineModelStageObjects R i Y s P F E d)
    (αK : AffineModelStageObjects R i Y s Q F K d)
    (βE : AffineModelLimitObject R c i Y s P F C E dlim)
    (βK : AffineModelLimitObject R c i Y s Q F C K dlim)
    (θ : AffineModelLimitArrowComparisons R c i Y s F C E K d dlim) : Prop :=
  ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
    let B := derivedPullback (baseChangeMap s (affineModelLimitArrow R c j))
    let ε := perfectHomComparison s (affineModelLimitArrow R c j)
    let hc := congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm
    ((affineModelLocalizedTilde C.pt _ dlim).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (C.ι.app j.val).hom (C.ι.app ⟨i, le_rfl⟩).hom hc E) ≪≫
      (θ j).app true ≪≫ B.mapIso (αE j) ≪≫ (ε.app P).symm = βE) ∧
    ((affineModelLocalizedTilde C.pt _ dlim).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (C.ι.app j.val).hom (C.ι.app ⟨i, le_rfl⟩).hom hc K) ≪≫
      (θ j).app false ≪≫ B.mapIso (αK j) ≪≫ (ε.app Q).symm = βK)

/-- Coherent comparison objects and their naturality data, stored without choosing a witness.
Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
structure AffineModelCoherentObjects where
  αE : AffineModelStageObjects R i Y s P F E d
  αK : AffineModelStageObjects R i Y s Q F K d
  βE : AffineModelLimitObject R c i Y s P F C E dlim
  βK : AffineModelLimitObject R c i Y s Q F C K dlim
  θ : AffineModelStageArrowComparisons R i Y s F E K d
  θlim : AffineModelLimitArrowComparisons R c i Y s F C E K d dlim
  hstage : affineModelStageObjectCoherence R i Y s P Q F E K d αE αK θ
  hlim : affineModelLimitObjectCoherence R c i Y s P Q F C E K d dlim
    αE αK βE βK θlim

end


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable abbrev affineModel_coordinate
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A : CommRingCat.{u}) (X : Scheme.{u}) (σ : Spec A ≅ X)
    (d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X)
    (hd : DerivedCategory.Q ⋙ d.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward σ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (.up ℤ)) ⋙ DerivedCategory.Q) :
    AffineComparisonCoordinate.{u, w} where
  A := A
  X := X
  σ := σ
  d := d
  hd := hd
  H := affineModelLocalizedTilde A X d
  hH := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by
      intro M N f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
        affineModelLocalizedTilde_map, Functor.comp_map])

attribute [local irreducible] perfectHomComposition

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct coherent object comparisons for the supplied stages and cocone point.
Source: Stacks Project, Tag 09RE (affine calculation), Tags 06Y1 and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons).

Proof: Extend E and K from the bottom to each j, preserving their acyclic-tensor
K-flatness by Tag 06Y1. For j→k apply the natural affine derived-pullback comparison
to the full two-label induced category on E(j),K(j). Conjugate with hd(j),hd(k),
using htrans.1 to identify the scheme arrow; this gives θ(j,k). The same construction
with hdlim and htrans.2 gives θlim(j). These natural isomorphisms include all maps
between the labelled objects, even when the two models coincide.
At the bottom, F.map_id and the tensor unitor identify identity scalar extension
with the original model. Apply the bottom-to-j affine comparison to E,K; pull back
aE,aK and compose with
the inverse of perfectHomComparison to obtain αE(j),αK(j). For the bottom-to-limit
arrow use the same construction to obtain βE,βK. In each triangle bottom→j→k or
bottom→j→limit, the underived tensor reassociation agrees with the counit-pinned
derived composition comparison, by its defining counit equation and associativity.
The ring equality is F.map_comp or C.w. Reassociation of module complexes is the
explicit affineModelScalarAssocIso. Transport this identity through hd and aE,aK;
it gives the four object-coherence equations below. Naturality cancellation for an
arbitrary chain map is a separate proved argument, not part of this statement.
Identity arrows, zero complexes, coincident labels, zero rings and empty spectra
use the same comparison; no directedness, colimit or boundedness is assumed. -/
theorem exists_affineModelCoherentObjectComparisons
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
    Nonempty (AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) := by
  classical
  obtain ⟨δ, hδ⟩ := exists_affineCoordinateComparisonTransportFamily.{u, w}
  let b : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) := ⟨⟨i, le_rfl⟩, le_rfl⟩
  let a (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :
      AffineComparisonCoordinate.{u, w} :=
    affineModel_coordinate (F.obj j.val) _ (σ j) (d j) (hd j)
  let z : AffineComparisonCoordinate.{u, w} :=
    affineModel_coordinate C.pt _ τ dlim hdlim
  let Ej (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    ((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
      (.up ℤ)).obj E
  let Kj (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    ((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
      (.up ℤ)).obj K
  have hEj (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :
      AffineComparisonKFlat (F.obj j.val) (Ej j) :=
    CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat
      (F.map (homOfLE j.property)).hom E hE
  have hKj (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :
      AffineComparisonKFlat (F.obj j.val) (Kj j) :=
    CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat
      (F.map (homOfLE j.property)).hom K hK
  let θ : AffineModelStageArrowComparisons R i Y s F E K d := fun j k hjk ↦
    δ (a j) (a k) (F.map (homOfLE hjk)).hom
      (baseChangeMap s (affineModelStageArrow R j k hjk))
      (htrans.1 j k hjk) (Ej j) (Kj j) (hEj j) (hKj j)
  let θlim : AffineModelLimitArrowComparisons R c i Y s F C E K d dlim := fun j ↦
    δ (a j) z (C.ι.app j.val).hom
      (baseChangeMap s (affineModelLimitArrow R c j))
      (htrans.2 j) (Ej j) (Kj j) (hEj j) (hKj j)
  let γ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    δ (a b) (a j) (F.map (homOfLE j.property)).hom
      (baseChangeMap s (affineModelStageArrow R b j j.property))
      (htrans.1 b j j.property) E K hE hK
  let γlim := δ (a b) z (C.ι.app b.val).hom
    (baseChangeMap s (affineModelLimitArrow R c b)) (htrans.2 b) E K hE hK
  let αE : AffineModelStageObjects R i Y s P F E d := fun j ↦
    (γ j).app true ≪≫
      (derivedPullback (baseChangeMap s (affineModelStageArrow R b j j.property))).mapIso
        aE ≪≫ ((perfectHomComparison s (affineModelStageArrow R b j j.property)).app P).symm
  let αK : AffineModelStageObjects R i Y s Q F K d := fun j ↦
    (γ j).app false ≪≫
      (derivedPullback (baseChangeMap s (affineModelStageArrow R b j j.property))).mapIso
        aK ≪≫ ((perfectHomComparison s (affineModelStageArrow R b j j.property)).app Q).symm
  let βE : AffineModelLimitObject R c i Y s P F C E dlim :=
    γlim.app true ≪≫
      (derivedPullback (baseChangeMap s (affineModelLimitArrow R c b))).mapIso aE ≪≫
        ((perfectHomComparison s (affineModelLimitArrow R c b)).app P).symm
  let βK : AffineModelLimitObject R c i Y s Q F C K dlim :=
    γlim.app false ≪≫
      (derivedPullback (baseChangeMap s (affineModelLimitArrow R c b))).mapIso aK ≪≫
        ((perfectHomComparison s (affineModelLimitArrow R c b)).app Q).symm
  have hstage : affineModelStageObjectCoherence R i Y s P Q F E K d αE αK θ := by
    intro j k hjk
    have ht : affineModelStageArrow R j k hjk ≫
        affineModelStageArrow R b j j.property =
        affineModelStageArrow R b k k.property := by
      ext
      change Spec.map (R.map (homOfLE hjk)) ≫
        Spec.map (R.map (homOfLE j.val.property)) =
        Spec.map (R.map (homOfLE k.val.property))
      rw [← Spec.map_comp, ← R.map_comp]
      rfl
    let hr := (baseChangeMap_comp s (affineModelStageArrow R j k hjk)
      (affineModelStageArrow R b j j.property)).symm.trans
        (congrArg (baseChangeMap s) ht)
    have hc := congrArg CommRingCat.Hom.hom
      (F.map_comp (homOfLE j.property) (homOfLE hjk))
    have hh := hδ (a b) (a j) (a k) (F.map (homOfLE j.property)).hom
      (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom hc
      (baseChangeMap s (affineModelStageArrow R b j j.property))
      (baseChangeMap s (affineModelStageArrow R j k hjk))
      (baseChangeMap s (affineModelStageArrow R b k k.property)) hr
      (htrans.1 b j j.property) (htrans.1 j k hjk) (htrans.1 b k k.property)
      E K hE hK
    constructor
    · have tr := hh.1 _ aE _ _
        ((perfectHomComparison s (affineModelStageArrow R b j j.property)).app P)
        ((perfectHomComparison s (affineModelStageArrow R b k k.property)).app P)
        ((perfectHomComparison s (affineModelStageArrow R j k hjk)).app P)
        (perfectHomComparison_triangle s _ _ _ ht P)
      simpa only [affineModelScalarAssocIso, Iso.trans_assoc] using tr
    · have tr := hh.2 _ aK _ _
        ((perfectHomComparison s (affineModelStageArrow R b j j.property)).app Q)
        ((perfectHomComparison s (affineModelStageArrow R b k k.property)).app Q)
        ((perfectHomComparison s (affineModelStageArrow R j k hjk)).app Q)
        (perfectHomComparison_triangle s _ _ _ ht Q)
      simpa only [affineModelScalarAssocIso, Iso.trans_assoc] using tr
  have hlim : affineModelLimitObjectCoherence R c i Y s P Q F C E K d dlim
      αE αK βE βK θlim := by
    intro j
    have ht : affineModelLimitArrow R c j ≫
        affineModelStageArrow R b j j.property = affineModelLimitArrow R c b := by
      ext
      change Spec.map (c.ι.app j.val) ≫ Spec.map (R.map (homOfLE j.val.property)) =
        Spec.map (c.ι.app i)
      rw [← Spec.map_comp, c.w (homOfLE j.val.property)]
    let hr := (baseChangeMap_comp s (affineModelLimitArrow R c j)
      (affineModelStageArrow R b j j.property)).symm.trans
        (congrArg (baseChangeMap s) ht)
    have hc := congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm
    have hh := hδ (a b) (a j) z (F.map (homOfLE j.property)).hom
      (C.ι.app j.val).hom (C.ι.app b.val).hom hc
      (baseChangeMap s (affineModelStageArrow R b j j.property))
      (baseChangeMap s (affineModelLimitArrow R c j))
      (baseChangeMap s (affineModelLimitArrow R c b)) hr
      (htrans.1 b j j.property) (htrans.2 j) (htrans.2 b) E K hE hK
    constructor
    · have tr := hh.1 _ aE _ _
        ((perfectHomComparison s (affineModelStageArrow R b j j.property)).app P)
        ((perfectHomComparison s (affineModelLimitArrow R c b)).app P)
        ((perfectHomComparison s (affineModelLimitArrow R c j)).app P)
        (perfectHomComparison_triangle s _ _ _ ht P)
      simpa only [affineModelScalarAssocIso, Iso.trans_assoc] using tr
    · have tr := hh.2 _ aK _ _
        ((perfectHomComparison s (affineModelStageArrow R b j j.property)).app Q)
        ((perfectHomComparison s (affineModelLimitArrow R c b)).app Q)
        ((perfectHomComparison s (affineModelLimitArrow R c j)).app Q)
        (perfectHomComparison_triangle s _ _ _ ht Q)
      simpa only [affineModelScalarAssocIso, Iso.trans_assoc] using tr
  exact ⟨⟨αE, αK, βE, βK, θ, θlim, hstage, hlim⟩⟩


end AlgebraicGeometry
