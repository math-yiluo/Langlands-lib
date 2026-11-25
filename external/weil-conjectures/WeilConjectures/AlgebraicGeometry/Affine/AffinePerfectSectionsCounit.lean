/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import all WeilConjectures.AlgebraicGeometry.AffineFreeTerminalSectionsReconstruction

/-! # A natural reconstruction counit for strictly perfect affine complexes

Source: Stacks Project, Tag 01IB.
(blueprint: new-affine-perfect-sections-counit)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Restriction along the canonical affine chart, with restriction along its inverse. -/
private noncomputable def sectionsSpecChartEquivalence (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    SheafOfModules.{v} (moduleRings (Spec Γ(W, U)).toRingedSpace) ≌ U.toScheme.Modules :=
  CategoryTheory.Equivalence.mk
    (Modules.restrictFunctor hU.isoSpec.hom) (Modules.restrictFunctor hU.isoSpec.inv)
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)

/-- The affine chart equivalence with the localized site. Named constructions keep
its unit and counit from being repeated in every complex comparison. -/
private noncomputable def sectionsChartEquivalence (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    SheafOfModules.{v} (moduleRings (Spec Γ(W, U)).toRingedSpace) ≌
      SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) :=
  (sectionsSpecChartEquivalence W U hU).trans (Modules.overEquiv U).symm

private theorem sectionsChartEquivalence_functor (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    (sectionsChartEquivalence W U hU).functor =
      Modules.restrictFunctor hU.isoSpec.hom ⋙ (Modules.overEquiv U).inverse := rfl

private theorem sectionsChartEquivalence_inverse (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    (sectionsChartEquivalence W U hU).inverse =
      (Modules.overEquiv U).functor ⋙ Modules.restrictFunctor hU.isoSpec.inv := rfl

attribute [local irreducible] sectionsChartEquivalence

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxRecDepth 2048 in
/-- Terminal-section reconstruction is a natural transformation, invertible on
strictly perfect complexes. Source: Stacks Project, Tag 01IB.
(blueprint: new-affine-perfect-sections-counit)

Proof: Transport the tilde/sections adjunction along the canonical affine-chart
equivalence. The transported sections functor is naturally terminal evaluation.
Use this identification in the adjunction counit, then apply it termwise to
complexes. Each term of a strictly perfect complex is in the essential image
of sheafification by the affine perfect module model. The fully faithful
left adjoint has invertible counit on that image. Thus every component of
the complex counit is invertible, so the complex map itself is invertible.
Boundedness is unused in this reconstruction step. -/
theorem affine_perfect_sections_counit (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    ∃ ε : F.mapHomologicalComplex (.up ℤ) ⋙
        (affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ) ⟶
          𝟭 (CochainComplex
            (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
      ∀ K, IsStrictlyPerfect W U K → IsIso (ε.app K) := by
  dsimp only
  let A := W.presheaf.obj (.op U)
  let D := SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)
  let E := sectionsChartEquivalence W U hU
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let T : ModuleCat.{v} A ⥤
      SheafOfModules.{v} (moduleRings (Spec A).toRingedSpace) := tilde.functor A
  have : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : T.Full := inferInstanceAs (tilde.functor A).Full
  have : T.Faithful := inferInstanceAs (tilde.functor A).Faithful
  have : E.functor.Full := inferInstance
  have : E.functor.Faithful := inferInstance
  let Sh := T ⋙ E.functor
  let H := E.inverse ⋙ moduleSpecΓFunctor (R := A)
  let adj : Sh ⊣ H := tilde.adjunction.comp E.toAdjunction
  have : Sh.Full := Functor.Full.comp (F := T) (G := E.functor)
  have : Sh.Faithful := Functor.Faithful.comp (F := T) (G := E.functor)
  have : Sh.Additive := inferInstanceAs (T ⋙ E.functor).Additive
  have : H.IsRightAdjoint := adj.isRightAdjoint
  have : (moduleSpecΓFunctor (R := A)).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have : H.PreservesZeroMorphisms := inferInstance
  have : H.Additive := Functor.additive_of_preserves_binary_products _
  have hSh : Sh = affinePerfectSheafification W U hU := by
    dsimp only [Sh, E, T, affinePerfectSheafification]
    rw [sectionsChartEquivalence_functor]
    rfl
  let e := sectionsSpecChartEquivalence W U hU
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let S := moduleSpecΓFunctor (R := A)
  let β : rG ≅ SheafOfModules.pushforward hU.isoSpec.hom.toRingCatSheafHom :=
    e.toAdjunction.rightAdjointUniq (Modules.restrictAdjunction hU.isoSpec.hom)
  let Fe : D ⥤ ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : Fe.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  obtain ⟨α⟩ := overChartSectionsIso W U hU
  have hH : H = (Modules.overEquiv U).functor ⋙ rG ⋙ S := by
    dsimp only [H, E]
    rw [sectionsChartEquivalence_inverse]
    rfl
  let γ : H ≅ Fe := eqToIso hH ≪≫
    Functor.isoWhiskerLeft (Modules.overEquiv U).functor
      (Functor.isoWhiskerRight β S) ≪≫ α
  let ρ : Fe ⋙ Sh ⟶ 𝟭 D := Functor.whiskerRight γ.inv Sh ≫ adj.counit
  let ε : Fe.mapHomologicalComplex (.up ℤ) ⋙ Sh.mapHomologicalComplex (.up ℤ) ⟶
      𝟭 (CochainComplex D ℤ) :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Fe ⋙ Sh)) (.up ℤ)).inv ≫
      NatTrans.mapHomologicalComplex ρ (.up ℤ) ≫
      (Functor.mapHomologicalComplexIdIso D (.up ℤ)).hom
  let a := Functor.isoWhiskerLeft (Fe.mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex (eqToIso hSh).symm (.up ℤ))
  refine ⟨a.hom ≫ ε, ?_⟩
  intro K hK
  obtain ⟨P, _, ⟨eP⟩⟩ := affine_perfect_module_model W U hU K hK
  have hcounit (n : ℤ) : IsIso (adj.counit.app (K.X n)) := by
    apply adj.isIso_counit_app_of_iso
    · rw [hSh]
      exact ((HomologicalComplex.eval D (.up ℤ) n).mapIso eP).symm
  have hρ (n : ℤ) : IsIso (ρ.app (K.X n)) := by
    dsimp only [ρ, NatTrans.comp_app, Functor.whiskerRight_app]
    have := hcounit n
    infer_instance
  have hρK : IsIso ((NatTrans.mapHomologicalComplex ρ (.up ℤ)).app K) := by
    have : ∀ n : ℤ,
        IsIso (((NatTrans.mapHomologicalComplex ρ (.up ℤ)).app K).f n) := by
      intro n
      change IsIso (ρ.app (K.X n))
      exact hρ n
    exact HomologicalComplex.Hom.isIso_of_components _
  change IsIso (a.hom.app K ≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (Fe ⋙ Sh)) (.up ℤ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex ρ (.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexIdIso D (.up ℤ)).hom.app K))
  exact IsIso.comp_isIso' (a.app K).isIso_hom
    (IsIso.comp_isIso'
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (Fe ⋙ Sh)) (.up ℤ)).app K).isIso_inv
      (IsIso.comp_isIso' hρK
        ((Functor.mapHomologicalComplexIdIso D (.up ℤ)).app K).isIso_hom))

end AlgebraicGeometry.Scheme
