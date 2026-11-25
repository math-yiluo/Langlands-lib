/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.LerayComplexCocycleComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

def LerayEdge (X Y : Scheme.{u}) (f : X ⟶ Y) :=
  ∀ q : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ⟶
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q ⋙
      RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat

def LerayEdgeCocycle {X Y : Scheme.{u}} (f : X ⟶ Y) (ε : LerayEdge X Y f) : Prop :=
  ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℕ)
    (hK : K = ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
    (s : (RingedSpace.globalSectionsComplex I).cycles q),
    ∃ z : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj (K.cycles q),
      (I.cocomplex.X q).val.presheaf.map
          (eqToHom (congrArg op (Opens.map_top f.base).symm))
          ((RingedSpace.globalSectionsComplex I).iCycles q s) =
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          (K.iCycles q ≫ (eqToHom hK).f q) z ∧
      (ε q).app F
          ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
            ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          ((K.homologyπ q) ≫ HomologicalComplex.homologyMap (eqToHom hK) q ≫
            (I.isoRightDerivedObj
              (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) q).inv) z

/-- Transport a comparison on complex homology to right derived functors, with
its compatibility for every injective resolution. -/
private theorem rightDerivedComparisonOfHomology
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₃]
    [Abelian C₀] [HasInjectiveResolutions C₀] [Abelian C₁] [Abelian C₂]
    (G : C₀ ⥤ C₁) (D : C₀ ⥤ C₂) (U : C₁ ⥤ C₃) (T : C₂ ⥤ C₃)
    [G.Additive] [D.Additive] (q : ℕ)
    (τ : (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ _ q ⋙ U) ⟶
      (D.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ _ q ⋙ T)) :
    ∃ ε : G.rightDerived q ⋙ U ⟶ D.rightDerived q ⋙ T,
      ∀ (F : C₀) (I : InjectiveResolution F),
        U.map (I.isoRightDerivedObj G q).inv ≫ ε.app F =
          τ.app I.cocomplex ≫ T.map (I.isoRightDerivedObj D q).inv := by
  classical
  let ε : G.rightDerived q ⋙ U ⟶ D.rightDerived q ⋙ T :=
    { app := fun F ↦
        U.map ((injectiveResolution F).isoRightDerivedObj G q).hom ≫
          τ.app (injectiveResolution F).cocomplex ≫
          T.map ((injectiveResolution F).isoRightDerivedObj D q).inv
      naturality := by
        intro F F' a
        let I := injectiveResolution F
        let J := injectiveResolution F'
        let φ := InjectiveResolution.desc a J I
        have comm : I.ι.f 0 ≫ φ.f 0 = a ≫ J.ι.f 0 := by
          simp [φ]
        have hG := InjectiveResolution.isoRightDerivedObj_hom_naturality a I J φ comm G q
        have hD := InjectiveResolution.isoRightDerivedObj_inv_naturality a I J φ comm D q
        have hG' := congrArg U.map hG
        have hD' := congrArg T.map hD
        simp only [Functor.map_comp] at hG' hD'
        change U.map ((G.rightDerived q).map a) ≫
            U.map (J.isoRightDerivedObj G q).hom ≫
            τ.app J.cocomplex ≫
            T.map (J.isoRightDerivedObj D q).inv =
          (U.map (I.isoRightDerivedObj G q).hom ≫
            τ.app I.cocomplex ≫
            T.map (I.isoRightDerivedObj D q).inv) ≫
            T.map ((D.rightDerived q).map a)
        rw [← Category.assoc, hG', Category.assoc]
        have hnat := τ.naturality φ
        change U.map
            ((G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ) ≫
            τ.app J.cocomplex =
          τ.app I.cocomplex ≫ T.map
            ((D.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ)
          at hnat
        rw [← Category.assoc _ (τ.app J.cocomplex), hnat]
        simp only [Category.assoc]
        rw [← hD'] }
  refine ⟨ε, ?_⟩
  intro F I
  let J := injectiveResolution F
  let φ := InjectiveResolution.desc (𝟙 F) J I
  have comm : I.ι.f 0 ≫ φ.f 0 = (𝟙 F) ≫ J.ι.f 0 := by simp [φ]
  have hG := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 F) I J φ comm G q
  have hD := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 F) I J φ comm D q
  rw [(G.rightDerived q).map_id, Category.comp_id] at hG
  rw [(D.rightDerived q).map_id, Category.comp_id] at hD
  have hG' := congrArg U.map hG
  have hD' := congrArg T.map hD
  simp only [Functor.map_comp] at hG' hD'
  change U.map (I.isoRightDerivedObj G q).inv ≫
      (U.map (J.isoRightDerivedObj G q).hom ≫
        τ.app J.cocomplex ≫
        T.map (J.isoRightDerivedObj D q).inv) = _
  rw [hG']
  rw [Category.assoc]
  have hc : U.map (J.isoRightDerivedObj G q).inv ≫
      U.map (J.isoRightDerivedObj G q).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id]
    exact U.map_id _
  rw [← Category.assoc _ (U.map
    (J.isoRightDerivedObj G q).hom), hc]
  erw [Category.id_comp]
  have hnat := τ.naturality φ
  change U.map
      ((G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ) ≫
      τ.app J.cocomplex =
    τ.app I.cocomplex ≫ T.map
      ((D.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ q).map φ)
    at hnat
  rw [← Category.assoc, hnat, Category.assoc, ← hD']

-- Resolution comparison unfolds both module-valued derived functors and forgetful maps.
set_option backward.isDefEq.respectTransparency false in
/-- Construction of the cocycle Leray edge.
(blueprint: lem-pc-leray-edge-cocycle-data)

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.

Proof: apply the Grothendieck spectral-sequence edge construction to direct image
followed by global sections. The resulting edge is represented on an injective
resolution by the displayed cycle and homology maps, which gives the stated
cocycle equation. More explicitly, direct images of injectives are acyclic
for sections by module_pushforward_injective_acyclic. Apply
grothendieck_left_edge_cocycle to these two additive left exact functors and
identify their composite with sections on X via restriction along Opens.map_top.
Left exactness identifies sections of the cycle sheaf with cycles of the
sections complex, so the global cocycle lifts uniquely to z. The generic edge
equation, transported by the resolution comparison isomorphisms, is the second
equality. Resolution comparison and functoriality give a single natural edge
for every coefficient module, independent of the chosen resolution. -/
theorem leray_edge_cocycle_data {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ ε : LerayEdge X Y f, LerayEdgeCocycle f ε := by
  classical
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let H := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let U := forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat
  let V := forget₂ (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat
  let T := H ⋙ V
  choose τ hτ using leray_complex_cocycle_comparison f
  choose ε hε using fun q ↦ rightDerivedComparisonOfHomology G D U T q (τ q)
  refine ⟨ε, ?_⟩
  intro q F I K hK s
  subst K
  obtain ⟨z, hz, hz'⟩ := hτ q I.cocomplex s
  refine ⟨z, ?_, ?_⟩
  · simpa only [eqToHom_refl, Category.comp_id, Functor.map_id, HomologicalComplex.id_f,
      RingedSpace.globalSectionsComplex] using hz
  · have heval := congrArg
      (fun a : U.obj
          ((RingedSpace.globalSectionsComplex I).homology q) ⟶
        T.obj ((D.rightDerived q).obj F) ↦
        a ((RingedSpace.globalSectionsComplex I).homologyπ q s)) (hε q F I)
    simp only [eqToHom_refl, HomologicalComplex.homologyMap_id]
    rw [Category.id_comp, H.map_comp]
    change (ε q).app F
        ((I.isoRightDerivedObj G q).inv
          ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
      (H.map (I.isoRightDerivedObj D q).inv)
        ((H.map ((((D.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).homologyπ q))) z)
    exact heval.trans (congrArg
      (fun t ↦ (H.map (I.isoRightDerivedObj D q).inv) t) hz')
end AlgebraicGeometry
