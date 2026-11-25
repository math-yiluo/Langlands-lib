/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Reconstruction from terminal sections on an affine slice

Source: Stacks Project, Tag 01IB.
(blueprint: lem-sc-affine-free-terminal-sections-reconstruction)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Identifying the chart and slice module scalar actions needs more definitional checks.
private theorem overChartSectionsIso (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    Nonempty ((Modules.overEquiv U).functor ⋙
      SheafOfModules.pushforward hU.isoSpec.hom.toRingCatSheafHom ⋙
        moduleSpecΓFunctor (R := Γ(W, U)) ≅
      SheafOfModules.evaluation.{v} ((moduleRings W.toRingedSpace).over U)
        (.op (Over.mk (𝟙 U)))) := by
  let V := U.overEquivalence.inverse.obj ⊤
  let a : Over.mk (𝟙 U) ≅ V := Over.isoMk (eqToIso U.ι_image_top.symm)
  refine ⟨NatIso.ofComponents (fun M ↦ ModuleCat.isoMk
    (M.val.presheaf.mapIso a.op) ?_) ?_⟩
  · intro r
    ext x
    change ((M.val.obj (.op (Over.mk (𝟙 U)))).smul r).asHom.hom
      (M.val.presheaf.map a.hom.op x) = M.val.presheaf.map a.hom.op _
    change ((M.val.obj (.op (Over.mk (𝟙 U)))).smul r).asHom.hom
      (M.val.presheaf.map a.hom.op x) = M.val.presheaf.map a.hom.op
        (((M.val.obj (.op V)).smul
          (hU.isoSpec.hom.appTop ((ΓSpecIso Γ(W, U)).inv r))).asHom.hom x)
    rw [hU.isoSpec_hom_appTop]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    have hm := M.val.map_smul a.hom.op (U.topIso.inv r) x
    have hr : ((W.ringCatSheaf.over U).obj.map a.hom.op) (U.topIso.inv r) = r := by
      change U.topIso.hom (U.topIso.inv r) = r
      exact U.topIso.inv_hom_id_apply r
    rw [hr] at hm
    exact hm.symm
  · intro M N f
    ext x
    change N.val.presheaf.map a.hom.op (f.val.app _ x) =
      f.val.app _ (M.val.presheaf.map a.hom.op x)
    exact (PresheafOfModules.naturality_apply f.val a.hom.op x).symm
set_option backward.isDefEq.respectTransparency.types true in
/-- Sheafifying the actual terminal sections reconstructs a termwise finite free complex.
Source: Stacks Project, Tag 01IB (schemes-lemma-equivalence-quasi-coherent).
(blueprint: lem-sc-affine-free-terminal-sections-reconstruction)

Proof: Compose the affine chart restriction equivalence with the inverse slice
module equivalence, obtaining E from modules on Spec(A) to the slice site, where
A = Gamma(W,U). Set S = tilde followed by E.functor and H = E.inverse followed by
moduleSpecGamma. The fully faithful tilde adjunction composed with E.toAdjunction
makes S left adjoint to H. Tilde of a finite free module, followed by E, is the
finite free slice sheaf: use tildeFinsupp, preservation of coproducts, and the
transported structure-module isomorphism. Thus every term of K is in S's essential
image, and the adjunction counit is invertible on it.
Identify H naturally with terminal slice evaluation. Uniqueness of right adjoints
identifies inverse chart restriction with forward chart pushforward. Its section
scalar action is isoSpec_hom_appTop composed with GammaSpecIso.inv, hence U.topIso.inv.
The presheaf map from the corresponding top slice object to (U,id) cancels this
scalar map; its naturality is presheaf morphism naturality. Map the counit and this
section comparison to complexes. Counit naturality supplies differential
compatibility, and invertibility in each degree gives the desired complex
isomorphism. This also covers rank zero, the zero ring and unbounded K. -/
theorem affineFree_terminalSections_reconstruction
    (W : Scheme.{v}) (U : W.Opens) (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (r : ℤ → ℕ)
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U) (ULift.{v} (Fin (r j))))) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    Nonempty (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅ K)  := by
  dsimp only
  let R := W.presheaf.obj (.op U)
  let S := SheafOfModules.{v} (moduleRings (Spec R).toRingedSpace)
  let D := SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{v}).Modules := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [R]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let E : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : HasBinaryBiproducts S := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts E.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let T := tilde.functor R
  let H := E.inverse ⋙ moduleSpecΓFunctor (R := R)
  let F := T ⋙ E.functor
  let adj : F ⊣ H := tilde.adjunction.comp E.toAdjunction
  have : H.IsRightAdjoint := adj.isRightAdjoint
  have : (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  have : H.PreservesZeroMorphisms := inferInstance
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : H.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hfree (m : ℕ) : Nonempty (F.obj
      (ModuleCat.of R (ULift.{v} (Fin m) →₀ R)) ≅
      SheafOfModules.free (R := (moduleRings W.toRingedSpace).over U)
        (ULift.{v} (Fin m))) := by
    let unitIso := (Modules.overEquiv U).inverse.mapIso
      ((Modules.restrictUnitIso hU.isoSpec.hom) ≪≫
        Modules.overEquivFunctorObjUnitIso U) ≪≫
        ((Modules.overEquiv U).unitIso.app
          (SheafOfModules.unit ((moduleRings W.toRingedSpace).over U))).symm
    exact ⟨E.functor.mapIso (tildeFinsupp (ULift.{v} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso E.functor (ULift.{v} (Fin m)) unitIso.symm).symm⟩
  have hcounit (n : ℤ) : IsIso (adj.counit.app (K.X n)) := by
    obtain ⟨ek⟩ := hrank n
    obtain ⟨ef⟩ := hfree (r n)
    exact adj.isIso_counit_app_of_iso (ek ≪≫ ef.symm)
  let β : rG ≅ SheafOfModules.pushforward hU.isoSpec.hom.toRingCatSheafHom :=
    e.toAdjunction.rightAdjointUniq (Modules.restrictAdjunction hU.isoSpec.hom)
  let S := moduleSpecΓFunctor (R := R)
  let Fe : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : Fe.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  obtain ⟨α⟩ := overChartSectionsIso W U hU
  let γ : H ≅ Fe := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Modules.overEquiv U).functor
      (Functor.isoWhiskerRight β S) ≪≫ α
  let ε := (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K
  have : IsIso ε := by
    have : ∀ n : ℤ, IsIso (ε.f n) := hcounit
    exact HomologicalComplex.Hom.isIso_of_components ε
  let δ := (NatIso.mapHomologicalComplex γ (.up ℤ)).app K
  exact ⟨(F.mapHomologicalComplex (.up ℤ)).mapIso δ.symm ≪≫
    asIso ε ≪≫ (Functor.mapHomologicalComplexIdIso D (.up ℤ)).app K⟩

end AlgebraicGeometry.Scheme
