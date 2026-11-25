/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Module.Equiv.Basic

/-! # The constant-coefficient realization of Chern arrows is injective

## References

* Stacks Project, Tags 03FD and 03PL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace AlgebraicGeometry.Etale

@[irreducible]
private def constantModuleEvaluation (A : Type (u + 1)) [CommRing A]
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (ModuleCat.{u + 1} A)] {T : C} (hT : IsTerminal T)
    (P : Sheaf J (ModuleCat.{u + 1} A)) :
    ((constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ P) ≃
      (P.obj.obj (op T)) :=
  ((constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv (ModuleCat.of A A) P).trans
    (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf A A _).toEquiv)

@[irreducible]
private def constantAbelianEvaluation {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {T : C} (hT : IsTerminal T) (P : Sheaf J AddCommGrpCat.{u + 1}) :
    ((constantSheaf J AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ P) ≃ (P.obj.obj (op T)) :=
  ((constantSheafAdj J AddCommGrpCat.{u + 1} hT).homEquiv
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) P).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

private theorem integralGenerator_corepresents_generic
    (A : Type (u + 1)) [CommRing A] {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} A)]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.HasSheafCompose (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})]
    {T : C} (hT : IsTerminal T)
    (ι : (constantSheaf J AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
        ((constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)))
    (hι : (constantSheafAdj J AddCommGrpCat.{u + 1} hT).homEquiv _ _ ι =
      AddCommGrpCat.ofHom
        ((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T))).hom).comp
          ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom)))
    (P : Sheaf J (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f :
        (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ P ↦
      ι ≫ (sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map f) := by
  let EM := constantModuleEvaluation A J hT P
  let EZ := constantAbelianEvaluation J hT
    ((sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P)
  have h (f : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ P) :
      EZ (ι ≫ (sheafCompose J
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map f) = EM f := by
    unfold EZ EM constantAbelianEvaluation constantModuleEvaluation
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right, hι]
    rw [Adjunction.homEquiv_unit]
    change f.hom.app (op T)
        (((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T))
          ((1 : ℤ) : A)) =
      f.hom.app (op T)
        (((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of A A))).app (op T)) (1 : A))
    simp only [Int.cast_one]
  constructor
  · intro f g hfg
    apply Equiv.injective EM
    exact (h f).symm.trans ((congrArg (fun z ↦ EZ z) hfg).trans (h g))
  · intro z
    obtain ⟨f, hf⟩ := Equiv.surjective EM (EZ z)
    refine ⟨f, Equiv.injective EZ ?_⟩
    exact (h f).trans hf

private theorem integralGenerator_corepresents (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f : ordinaryFiniteConstant A T ⟶ P ↦
      ordinaryFiniteIntegralGenerator A T ≫ (RawModuleScalarComparison.forget A T).map f) := by
  exact integralGenerator_corepresents_generic A T.smallEtaleTopology
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
    (ordinaryFiniteIntegralGenerator A T)
    (by
      unfold ordinaryFiniteIntegralGenerator
      exact Equiv.apply_symm_apply _ _) P

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A module-derived class from the free constant coefficient sheaf is determined by
its realization in abelian sheaf cohomology on a quasi-compact quasi-separated scheme. -/
theorem ordinaryFiniteClass_injective (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :
    Function.Injective (ordinaryFiniteClass A T P n) := by
  have h := (bijective_extToSheafHOf A (X := T) (A := ordinaryFiniteConstant A T)
    (ordinaryFiniteIntegralGenerator A T)
    (integralGenerator_corepresents A T) n P).1
  unfold ordinaryFiniteClass
  change Function.Injective (fun c ↦ extToSheafHOf A (ordinaryFiniteIntegralGenerator A T)
    P n ((Ext.homEquiv (X := ordinaryFiniteConstant A T) (Y := P) (n := n)).symm c))
  exact Function.Injective.comp h
    (Equiv.injective (Ext.homEquiv (X := ordinaryFiniteConstant A T) (Y := P) (n := n)).symm)

end AlgebraicGeometry.Etale
