/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-! # Higher direct image as a sheafified cohomology presheaf
Source: literature/stacks-project/cohomology.tex, Lemma 01E4
(blueprint: lem-weil-pbc-higher-direct-image-presheaf).
-/

private theorem higherDirectImagePresheaf_universal_aux
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (A : L ⊣ R) {P : C} {H T Q : D} (c : L.obj P ⟶ H) [IsIso c]
    (e : T ≅ H) (a : P ⟶ R.obj Q) :
    ∃! b : T ⟶ Q, A.homEquiv P H c ≫ R.map (e.inv ≫ b) = a := by
  simpa only [Equiv.trans_apply, Iso.homFromEquiv_apply, Iso.symm_inv,
    Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
    A.homEquiv_naturality_right] using
    ((((asIso c) ≪≫ e.symm).symm.homFromEquiv).trans
      (A.homEquiv P Q)).bijective.existsUnique a

private theorem sectionCohomologyComparison_isIso {Y : Scheme.{u}}
    (K : CochainComplex Y.Modules ℕ) (p : ℕ) :
    IsIso (Scheme.Modules.sectionCohomologyComparison K p) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  have : IsIso ((A.counit.mapHomologicalComplex (ComplexShape.up ℕ)).app K) := by
    have : ∀ n, IsIso
        (((A.counit.mapHomologicalComplex (ComplexShape.up ℕ)).app K).f n) := by
      intro n
      change IsIso (A.counit.app (K.X n))
      dsimp [A]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  exact IsIso.comp_isIso' (inferInstance)
    ((HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℕ) p).map_isIso
      ((A.counit.mapHomologicalComplex (ComplexShape.up ℕ)).app K))

private theorem sectionCohomologyTheta_stalk_isIso {Y : Scheme.{u}}
    (K : CochainComplex Y.Modules ℕ) (p : ℕ) (y : Y) :
    IsIso ((PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj y).map
      (Scheme.Modules.sectionCohomologyTheta K p)) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let S := PresheafOfModules.moduleStalkFunctor Y.ringCatSheaf.obj y
  have : IsIso (Scheme.Modules.sectionCohomologyComparison K p) :=
    sectionCohomologyComparison_isIso K p
  have : IsIso (S.map (A.unit.app (Scheme.Modules.sectionCohomologyPresheaf K p))) := by
    rw [← isIso_iff_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{u})]
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        (A.unit.app (Scheme.Modules.sectionCohomologyPresheaf K p))))
    simp only [A, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y _ _
  change IsIso (S.map (A.homEquiv _ _ (Scheme.Modules.sectionCohomologyComparison K p)))
  rw [Adjunction.homEquiv_unit, S.map_comp]
  infer_instance

private theorem sectionCohomologyTheta_universal {Y : Scheme.{u}}
    (K : CochainComplex Y.Modules ℕ) (p : ℕ) {T : Y.Modules} (e : T ≅ K.homology p)
    (Q : Y.Modules) (a : Scheme.Modules.sectionCohomologyPresheaf K p ⟶
      (SheafOfModules.forget Y.ringCatSheaf).obj Q) :
    ∃! b : T ⟶ Q, Scheme.Modules.sectionCohomologyTheta K p ≫
      (SheafOfModules.forget Y.ringCatSheaf).map (e.inv ≫ b) = a := by
  have := sectionCohomologyComparison_isIso K p
  exact higherDirectImagePresheaf_universal_aux
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj))
    (Scheme.Modules.sectionCohomologyComparison K p) e a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Stacks 01E4 with every datum tied. For an injective resolution I of F, the presheaf
P_p is `sectionCohomologyPresheaf (f_*I) p`, V ↦ H^p(I(f⁻¹V)); theta is
`sectionCohomologyTheta (f_*I) p` followed by the resolution comparison
H^p(f_*I) ≅ R^p f_*F. The statement says:
(1) the canonical comparison P_p^# → R^p f_*F is an isomorphism;
(2) theta is universal: every map from P_p to a sheaf of modules factors uniquely
through theta;
(3) for each y, the map induced by theta on module stalks is an isomorphism;
(4) the value of P_p on V is H^p(f⁻¹V, F) (open module cohomology, through the same
resolution and exact evaluation), and under these identifications the restriction
maps of P_p are the cohomology restriction maps;
(5) the canonical map f_*F → R^0 f_*F is an isomorphism.
Source: literature/stacks-project/cohomology.tex, Lemma 01E4
(blueprint: lem-weil-pbc-higher-direct-image-presheaf).

Proof: (1) f_*I computes R^p f_*F; module sheafification is exact and commutes with
homology, and its counit on sheaves is invertible, so the comparison is invertible.
(2) theta is the adjoint of an isomorphism, hence universal. (3) sheafification
preserves stalks (Sheaves 007Z), and theta factors as the sheafification unit followed
by an isomorphism. (4) I restricted to f⁻¹V is an injective resolution (01E1), whose
sections are I(f⁻¹V); restriction of cohomology is induced by restriction of the
resolution (01E2), and the evaluation at V of f_*I is I(f⁻¹V). (5) f_* is left exact. -/
theorem higherDirectImagePresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F) (p : ℕ) :
    IsIso (Scheme.Modules.sectionCohomologyComparison
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) p ≫
      (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv) ∧
    (∀ (Q : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (a : Scheme.Modules.sectionCohomologyPresheaf
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) p ⟶
        (SheafOfModules.forget (moduleRings Y.toRingedSpace)).obj Q),
      ∃! b : ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F ⟶ Q,
        Scheme.Modules.sectionCohomologyTheta
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex) p ≫
          (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
            ((I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv ≫
              b) = a) ∧
    (∀ y : Y, IsIso ((PresheafOfModules.moduleStalkFunctor (moduleRings Y.toRingedSpace).obj y).map
      (Scheme.Modules.sectionCohomologyTheta
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) p ≫
        (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
          (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv))) ∧
    (∀ (V W : Y.Opens) (i : W ⟶ V),
      (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (f.preimage_mono (leOfHom i)))).app F ≫
        (I.isoRightDerivedObj (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ W)) p ≪≫
          ((((SheafOfModules.forget (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex)).sc p).mapHomologyIso
                  (PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj ⋙
                    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W))).hom =
      (I.isoRightDerivedObj (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) p ≪≫
          ((((SheafOfModules.forget (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex)).sc p).mapHomologyIso
                  (PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj ⋙
                    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom ≫
        (Scheme.Modules.sectionCohomologyPresheaf
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) p).presheaf.map i.op) ∧
    IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app F) := by
  let K : CochainComplex Y.Modules ℕ :=
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex
  let e := I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p
  let : PreservesFiniteLimits
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have hc : IsIso (Scheme.Modules.sectionCohomologyComparison K p) :=
    sectionCohomologyComparison_isIso K p
  refine ⟨?_, ?_, ?_, ?_, by infer_instance⟩
  · exact IsIso.comp_isIso' hc e.isIso_inv
  · intro Q a
    exact sectionCohomologyTheta_universal K p e Q a
  · intro y
    have := sectionCohomologyTheta_stalk_isIso K p y
    rw [Functor.map_comp]
    infer_instance
  · intro V W i
    let α : RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V) ⟶
        RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ W) :=
      Functor.whiskerLeft (SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj)
          ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).map
            (homOfLE (f.preimage_mono (leOfHom i))).op)
    let L := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K
    let EV := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
      (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
    let EW := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
      (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
    let τ : EV ⟶ EW := Functor.whiskerLeft
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
        ((evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).map i.op)
    let eV := I.isoRightDerivedObj
      (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) p
    let eW := I.isoRightDerivedObj
      (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ W)) p
    change (NatTrans.rightDerived α p).app F ≫
      (eW.hom ≫ ((L.sc p).mapHomologyIso EW).hom) =
        eV.hom ≫ ((L.sc p).mapHomologyIso EV).hom ≫ τ.app (L.sc p).homology
    rw [I.rightDerived_app_eq α p]
    simp only [eW, Category.assoc, Iso.inv_hom_id_assoc]
    rw [cancel_epi]
    have h := congrArg (fun t ↦ t ≫ ((L.sc p).mapHomologyIso EW).hom)
      ((L.sc p).homologyMap_mapNatTrans τ)
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using! h

end AlgebraicGeometry
