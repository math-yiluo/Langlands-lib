/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
import WeilConjectures.AlgebraicGeometry.ConstantModuleTransitionCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical coefficient comparison for constant-module sections

Source: Stacks Project, Tags 03DB, 03CO and 09Z1.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Forget the scalar action and compare constant sheaves, then undo the canonical
constant-sheaf pullback comparison. This uses actual natural isomorphisms, not a choice
of an equivalence family. 
(blueprint: lem-weil-pbc-constant-module-section-coefficients)
-/
noncomputable def constantModuleSectionCoefficientSheafIso
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X Z : Scheme.{u}} (f : Z ⟶ X) :
    (sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅
      (upperStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let r : ℤ →+* Λ := Int.castRingHom Λ
  let R := ModuleCat.restrictScalars.{u + 1} r
  let T := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : R.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} r).isLeftAdjoint
  have : V.IsLeftAdjoint := inferInstanceAs (R ⋙ T).IsLeftAdjoint
  have : Z.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _
      (Adjunction.ofIsLeftAdjoint V)
  exact (constantCommuteCompose Z.smallEtaleTopology V).app M ≪≫
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app (V.obj M)).symm

/-- Evaluate the coefficient comparison at the base change of the étale object. 
(blueprint: lem-weil-pbc-constant-module-section-coefficients)
-/
noncomputable def constantModuleSectionCoefficientEquiv
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X Z : Scheme.{u}} (U : X.Etale) (f : Z ⟶ X) :
    ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op U) ≃+
    ((lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)))).obj.obj
        (op U) :=
  Iso.addCommGroupIsoToAddEquiv
    (((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (f.Etale.obj U))).mapIso (constantModuleSectionCoefficientSheafIso Λ M f))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical coefficient comparison intertwines module transitions with the
adjunction-unit transition for the abelian sheaf pulled back from the base.

Source: Stacks Project, Tags 03DB and 03CO (forgetting coefficients and sheafification),
and Tag 09Z1 (canonical transition maps).
(blueprint: lem-weil-pbc-constant-module-section-coefficients).

Proof: Write C_X for the constant abelian sheaf on X. The sheaf isomorphism used here
is the constantCommuteCompose comparison followed by the inverse of the canonical
constant-sheaf pullback comparison. The former commutes with sheafification generators.
The latter is the uniqueness isomorphism of left adjoints to terminal evaluation, so
its adjoint sends each constant generator to the same generator. Naturality of the
inverse-image unit moves the coefficient comparison across the unit. The unit equation
for uniqueness of left adjoints identifies the composite constant pullback comparison
with upperStarComp. Applying lowerStar and its composition isomorphism gives the
sheaf-level commuting square. Evaluate it at U. Direct image is precomposition on
étale objects, so coefficient forgetting commutes with it definitionally. This gives
the displayed section equality. There are no restrictions on coefficients or schemes;
zero coefficients and empty pullbacks use the same unit and naturality equations. -/
theorem constantModuleSectionCoefficientEquiv_naturality
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} (U : X.Etale)
    {Z W : Scheme.{u}} (g : W ⟶ Z) (f : Z ⟶ X) (h : W ⟶ X)
    (w : g ≫ f = h)
    (z : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op U)) :
    let A := AddCommGrpCat.{u + 1}
    let G := (constantSheaf X.smallEtaleTopology A).obj
      ((forget₂ (ModuleCat.{u + 1} Λ) A).obj M)
    constantModuleSectionCoefficientEquiv Λ M U h
        ((constantModulePushforwardMap Λ M f h g w).hom.app (op U) z) =
      ((lowerStar A f).map
          ((upperStarLowerStarAdjunction A g).unit.app ((upperStar A f).obj G)) ≫
        (lowerStarComp A g f h w.symm).hom.app _ ≫
        (lowerStar A h).map ((upperStarComp A g f h w.symm).inv.app G)).hom.app
          (op U) (constantModuleSectionCoefficientEquiv Λ M U f z) := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let r : ℤ →+* Λ := Int.castRingHom Λ
  let R := ModuleCat.restrictScalars.{u + 1} r
  let T := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : R.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} r).isLeftAdjoint
  have : V.IsLeftAdjoint := inferInstanceAs (R ⋙ T).IsLeftAdjoint
  have : Z.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _ (Adjunction.ofIsLeftAdjoint V)
  have : W.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _ (Adjunction.ofIsLeftAdjoint V)
  let A := AddCommGrpCat.{u + 1}
  let G := (constantSheaf X.smallEtaleTopology A).obj (V.obj M)
  let CZ := (constantSheaf Z.smallEtaleTopology A).obj (V.obj M)
  let cf := (Scheme.upperStarConstantSheafIso A f).app (V.obj M)
  let cg := (Scheme.upperStarConstantSheafIso A g).app (V.obj M)
  let ch := (Scheme.upperStarConstantSheafIso A h).app (V.obj M)
  let c := (upperStarComp A g f h w.symm).app G
  let eZ := (constantCommuteCompose Z.smallEtaleTopology V).app M
  let eW := (constantCommuteCompose W.smallEtaleTopology V).app M
  let tM := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
    (lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)
  have hc : cg.hom ≫ ch.inv = (upperStar A g).map cf.inv ≫ c.inv := by
    have hcoh : ch.inv ≫ c.hom = cg.inv ≫ (upperStar A g).map cf.inv := by
      subst h
      exact constantPullbackCompositionCoherence g f (V.obj M)
    apply (cancel_mono c.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hcoh]
    simp
  have hk : (sheafCompose Z.smallEtaleTopology V).map tM ≫
        (lowerStar A g).map (eW.hom ≫ ch.inv) =
      (eZ.hom ≫ cf.inv) ≫
        (upperStarLowerStarAdjunction A g).unit.app ((upperStar A f).obj G) ≫
        (lowerStar A g).map c.inv := by
    rw [(lowerStar A g).map_comp, ← Category.assoc]
    have ht := constantModuleTransition_coefficients Λ M g
    change (sheafCompose Z.smallEtaleTopology V).map tM ≫
        (lowerStar A g).map eW.hom = eZ.hom ≫
        (upperStarLowerStarAdjunction A g).unit.app CZ ≫
        (lowerStar A g).map cg.hom at ht
    rw [ht]
    simp only [Category.assoc]
    rw [← (lowerStar A g).map_comp, hc, (lowerStar A g).map_comp]
    have hn := (upperStarLowerStarAdjunction A g).unit.naturality cf.inv
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← Category.assoc ((upperStarLowerStarAdjunction A g).unit.app CZ), ← hn]
    simp only [Category.assoc]
    rfl
  have hs :
      (lowerStar A f).map ((sheafCompose Z.smallEtaleTopology V).map tM) ≫
          (lowerStarComp A g f h w.symm).hom.app
            ((sheafCompose W.smallEtaleTopology V).obj
              ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≫
          (lowerStar A h).map (eW.hom ≫ ch.inv) =
        (lowerStar A f).map (eZ.hom ≫ cf.inv) ≫
          (lowerStar A f).map
            ((upperStarLowerStarAdjunction A g).unit.app ((upperStar A f).obj G)) ≫
          (lowerStarComp A g f h w.symm).hom.app _ ≫
          (lowerStar A h).map c.inv := by
    rw [← NatTrans.naturality]
    simp only [Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, hk]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (lowerStarComp A g f h w.symm).hom.naturality c.inv
    dsimp only [Functor.comp_map] at hn
    dsimp only [Functor.comp_obj, G] at hn ⊢
    rw [hn]
  have he := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u + 1})
    (congrArg (fun k ↦ k.hom.app (op U)) hs) z
  exact he

end AlgebraicGeometry.Etale
