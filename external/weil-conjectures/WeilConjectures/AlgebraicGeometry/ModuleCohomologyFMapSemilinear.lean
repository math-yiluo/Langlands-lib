/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory TopologicalSpace Opposite
noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem homology_scalar_comm
    {R S : Type u} [Ring R] [Ring S]
    (A : ShortComplex (ModuleCat.{u} R)) (B : ShortComplex (ModuleCat.{u} S))
    (f : A.map (forget₂ _ AddCommGrpCat.{u}) ⟶
      B.map (forget₂ _ AddCommGrpCat.{u})) (r : R) (s : S)
    (hf : A.mapNatTrans (ModuleCat.smulNatTrans R r).asHom ≫ f =
      f ≫ B.mapNatTrans (ModuleCat.smulNatTrans S s).asHom) :
    (A.homology.smul r).asHom ≫ (A.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv ≫
      ShortComplex.homologyMap f ≫ (B.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).hom =
    (A.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv ≫
      ShortComplex.homologyMap f ≫ (B.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).hom ≫
        (B.homology.smul s).asHom := by
  have h := congrArg (fun g : A.map (forget₂ _ AddCommGrpCat.{u}) ⟶
    B.map (forget₂ _ AddCommGrpCat.{u}) ↦ ShortComplex.homologyMap g) hf
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp,
    ShortComplex.homologyMap_mapNatTrans, ShortComplex.homologyMap_mapNatTrans] at h
  have h' := congrArg (fun g ↦
    (A.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv ≫ g ≫
      (B.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).hom) h
  simpa [Category.assoc, ModuleCat.smulNatTrans] using h'

namespace AlgebraicGeometry.Scheme.Modules

-- The comparisons involve several nested evaluation and homology functors.
set_option backward.isDefEq.respectTransparency false in
/-- The resolution map admits a semilinear lift over the map on global functions.
Source: Stacks Project, Cohomology of Sheaves, Equation 01F9 and Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-semilinear-lift)

The lift is obtained by checking scalar compatibility on the section, cycle and
homology maps in the defining resolution comparison. -/
theorem ModuleCohomologyFMapData.map_semilinear
    {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    ∃ f : ((Y.toRingedSpace.moduleCohomology p).obj G) →ₛₗ[h.appTop.hom]
      ((X.toRingedSpace.moduleCohomology p).obj F),
      ∀ x, f x = D.map p x := by
  let ΓX := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let ΓY := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let UX := forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}
  let UY := forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}
  let A := RingedSpace.globalSectionsComplex D.I
  let B := RingedSpace.globalSectionsComplex D.J
  let C := (ΓY.mapHomologicalComplex (ComplexShape.up ℕ)).obj D.K
  let μ := D.a.hom ≫ ((ΓY ⋙ UY).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda
  let cA := (A.sc p).mapHomologyIso UX
  let cB := (B.sc p).mapHomologyIso UY
  let cC := (C.sc p).mapHomologyIso UY
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let m := cA.inv ≫ H.map μ ≫ cC.hom
  have hmIso : IsIso (H.map μ) := D.invertible p
  have : IsIso m := by dsimp [m]; infer_instance
  have ha (n : ℕ) : D.a.inv.f n = 𝟙 _ := by
    rw [D.sections]
    simp only [eqToHom_refl, op_id]
    erw [(presheaf (D.I.cocomplex.X n)).map_id]
    rfl
  have ha' (n : ℕ) : D.a.hom.f n = 𝟙 _ := by
    have w := congrArg (fun f ↦ f.f n) D.a.hom_inv_id
    change D.a.hom.f n ≫ D.a.inv.f n = 𝟙 _ at w
    rw [ha, Category.comp_id] at w
    exact w
  have hμn (n : ℕ) (r : Y.ringCatSheaf.obj.obj (op ⊤)) (x : A.X n) :
      (μ.f n) (h.appTop.hom r • x) = r • (show C.X n from (μ.f n) x) := by
    change (ΓY.map (D.lambda.f n)) (D.a.hom.f n (h.appTop.hom r • x)) =
      r • (show C.X n from (ΓY.map (D.lambda.f n)) (D.a.hom.f n x))
    rw [ha']
    exact (ΓY.map (D.lambda.f n)).hom.map_smul r x
  have hμ (r : Y.ringCatSheaf.obj.obj (op ⊤)) :
      (A.sc p).mapNatTrans (ModuleCat.smulNatTrans _ (h.appTop.hom r)).asHom ≫
        (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map μ =
      (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map μ ≫
        (C.sc p).mapNatTrans (ModuleCat.smulNatTrans _ r).asHom := by
    ext x
    all_goals exact hμn _ r x
  have hm (r : Y.ringCatSheaf.obj.obj (op ⊤)) (x : A.homology p) :
      m (h.appTop.hom r • x) = r • (show C.homology p from m x) := by
    have w := homology_scalar_comm (A.sc p) (C.sc p)
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map μ)
      (h.appTop.hom r) r (hμ r)
    exact congrArg (fun f ↦ f x) w
  have hmi (r : Y.ringCatSheaf.obj.obj (op ⊤)) (y : C.homology p) :
      inv m (r • y) = h.appTop.hom r • (show A.homology p from inv m y) := by
    apply (ConcreteCategory.bijective_of_isIso m).1
    rw [hm]
    simp
  let b := (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
    ((ΓY.mapHomologicalComplex (ComplexShape.up ℕ)).map D.β)
  have hb : cB.inv ≫ H.map
      (((ΓY ⋙ UY).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) ≫ cC.hom =
      UY.map b := by
    have w := ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
        ((ΓY.mapHomologicalComplex (ComplexShape.up ℕ)).map D.β)) UY
    change UY.map b ≫ cC.inv = cB.inv ≫ H.map
      (((ΓY ⋙ UY).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) at w
    rw [← Category.assoc, ← w]
    simp
  let j := (D.J.isoRightDerivedObj ΓY p).hom
  let i := (D.I.isoRightDerivedObj ΓX p).inv
  let fadd := UY.map j ≫ UY.map b ≫ inv m ≫ UX.map i
  have hfadd : fadd = D.map p := by
    change UY.map j ≫ UY.map b ≫ inv m ≫ UX.map i =
      UY.map j ≫ cB.inv ≫ H.map
        (((ΓY ⋙ UY).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) ≫
        inv (H.map μ) ≫ cA.hom ≫ UX.map i
    rw [← hb]
    simp only [m, IsIso.inv_comp, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv, Category.assoc,
      Iso.hom_inv_id_assoc]
  refine ⟨{ (fadd.hom) with map_smul' := ?_ }, ?_⟩
  · intro r x
    change i (inv m (b (j (r • x)))) = h.appTop.hom r • i (inv m (b (j x)))
    exact (congrArg (fun y ↦ i (inv m (b y))) (j.hom.map_smul r x)).trans
      ((congrArg (fun y ↦ i (inv m y)) (b.hom.map_smul r (j x))).trans
        ((congrArg (fun y ↦ i y) (hmi r (b (j x)))).trans
          (i.hom.map_smul (h.appTop.hom r) (inv m (b (j x))))))
  · intro x
    exact congrArg (fun f ↦ f x) hfadd

end AlgebraicGeometry.Scheme.Modules
