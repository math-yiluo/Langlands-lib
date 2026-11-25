/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
/-! # The model ring unit presents the inverse-image ring
Source: Stacks Project, Tags 09A5, 00YV and 03D2.
(auxiliary; not a blueprint node).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable def modelSheafEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) CommRingCat.{u + 1} ≌
      Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      CommRingCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modelSheafEquivalence Y).functor ⋙ proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
      (modelSheafEquivalence X).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).restrictFullyFaithful
    (modelSheafEquivalence Y).fullyFaithfulFunctor
    (modelSheafEquivalence X).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
private theorem modelRingAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (modelRingAdjunction f).unit.app ((modelSheafEquivalence Y).inverse.obj R) =
      ⟨CategoryTheory.Functor.whiskerLeft AsSmall.down.op
        ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom⟩ := by
  apply (modelSheafEquivalence Y).functor.map_injective
  rw [modelRingAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl
/-- The actual transported ring unit is a set inverse-image unit.
Source: Stacks Project, Tags 09A5, 00YV and 03D2.
(auxiliary; not a blueprint node).
Proof: transport the original commutative-ring adjunction through the strict
AsSmall equivalences. Its unit is the stated ring unit on sections. Compare this
left adjoint with the model commutative-ring pullback, respecting units. Forgetting
rings commutes with filtered Kan extension and sheafification, and its canonical
comparison respects units too. Compose the two comparisons. -/
theorem proEtaleModelRingPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    let A := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R
    let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    ∃ p : SheafPullbackUnitPresentation (F := proEtaleModelBaseChange f)
      ((sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj A)
      ((sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj B),
      ∀ U r, p.unit.hom.app U r = (proEtaleModelRingUnit f R).hom.app U r := by
  let F := proEtaleModelBaseChange f
  let J := proEtaleModelTopology Y
  let K := proEtaleModelTopology X
  let A := (modelSheafEquivalence Y).inverse.obj R
  let B := (modelSheafEquivalence X).inverse.obj
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits F := by
    dsimp [F, proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let e := (modelRingAdjunction f).leftAdjointUniq
    (sheafAdjunctionContinuous F CommRingCat.{u + 1} J K)
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget CommRingCat.{u + 1})
  let iso : (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).obj B ≅
      (sheafPullback F (Type (u + 1)) J K).obj
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).mapIso (e.app A) ≪≫
      c.app A
  let unit :=
    (sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).map (proEtaleModelRingUnit f R)
  refine ⟨⟨unit, iso, ?_⟩, fun U r ↦ rfl⟩
  intro U r
  have he := Adjunction.unit_leftAdjointUniq_hom_app (modelRingAdjunction f)
    (sheafAdjunctionContinuous F CommRingCat.{u + 1} J K) A
  have hc := sheafPullbackForgetIso_unit J K F (CategoryTheory.forget CommRingCat.{u + 1}) A
  have ht := modelRingAdjunction_unit f R
  have ht' := congrArg (fun z ↦ z.hom.app U) ht
  have htr : ((modelRingAdjunction f).unit.app A).hom.app U r = unit.hom.app U r :=
    ConcreteCategory.congr_hom ht' r
  have he' := congrArg (fun z ↦ z.hom.app U) he
  have he0 := ConcreteCategory.congr_hom he' r
  have hc' := congrArg (fun z ↦ z.hom.app U) hc
  have hc0 := ConcreteCategory.congr_hom hc' r
  change (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) (unit.hom.app U r)) = _
  exact (congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) t)) htr.symm).trans
    ((congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U) t) he0).trans hc0)
end AlgebraicGeometry.Scheme
