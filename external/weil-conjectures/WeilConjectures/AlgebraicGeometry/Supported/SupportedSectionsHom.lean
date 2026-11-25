/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedConstantPresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Underived supported sections as Hom

Source: Milne, Lectures on Etale Cohomology, Section 9, proof of Theorem 9.4,
p. 67; the constant-coefficient argument of lemma-sections-support-closed-subscheme--1, steps 1--4
(blueprint: lem-pur-supported-sections-hom).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private noncomputable def openConstantMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    (constantSheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj (ModuleCat.of _ (ULift.{u + 1} A)) ⟶
      (openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
        ((constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
            (ModuleCat.of _ (ULift.{u + 1} A))) :=
  Scheme.proEtaleFixedOpenConstantMap j A

private noncomputable def openConstantArrow {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
      (Scheme.proEtaleFixedConstantModule U A) ⟶ Scheme.proEtaleFixedConstantModule X A :=
  ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv _ _).symm (openConstantMap j A)

private theorem fixedConstantPresentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : openConstantArrow i.openComplement.ι A ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (ModuleCat.of _ (ULift.{u + 1} A)) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (ModuleCat.of _ (ULift.{u + 1} A))) h)) := by
  classical
  let E := Scheme.sfIntrinsicModuleEquivalence X A
  let EU := Scheme.sfIntrinsicModuleEquivalence i.openComplement.toScheme A
  let AZ := Scheme.proEtaleFixedConstantModule Z A
  let AX := Scheme.proEtaleFixedConstantModule X A
  let AU := Scheme.proEtaleFixedConstantModule i.openComplement.toScheme A
  let L := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A))
    i.openComplement.ι
  let ρ := Scheme.proEtaleConstantDirectImageMap i
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (ModuleCat.of _ (ULift.{u + 1} A))
  let k : E.functor.obj (L.obj AU) ≅
      (Scheme.sfIntrinsicExtensionByZero i.openComplement.ι A).obj
        (Scheme.proEtaleConstantModule i.openComplement.toScheme A) :=
    E.functor.mapIso (L.mapIso (EU.unitIso.app AU ≪≫
      EU.inverse.mapIso (Scheme.proEtaleConstantModuleUnit i.openComplement.toScheme A)))
  let q : E.functor.obj ((lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj AZ) ≅
        (Scheme.proEtaleConstantModuleDirectImage i A).obj
          (Scheme.proEtaleConstantModule Z A) :=
    (Scheme.sfIntrinsicDirectImageComparison i A).symm.app AZ ≪≫
      (Scheme.proEtaleConstantModuleDirectImage i A).mapIso
        (Scheme.proEtaleConstantModuleUnit Z A)
  have he : E.functor.map (openConstantArrow i.openComplement.ι A) ≫
      (Scheme.proEtaleConstantModuleUnit X A).hom =
        k.hom ≫ Scheme.proEtaleOpenConstantCounit i.openComplement.ι A := by
    dsimp [k, Scheme.proEtaleOpenConstantCounit, Scheme.sfIntrinsicExtensionByZero]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    simp [E, EU, AU, L, openConstantArrow, openConstantMap]
  have hr : E.functor.map ρ ≫ q.hom =
      (Scheme.proEtaleConstantModuleUnit X A).hom ≫
        Scheme.proEtaleClosedConstantRestriction i A := by
    dsimp [q, Scheme.proEtaleClosedConstantRestriction]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  obtain ⟨h, ⟨hc⟩⟩ := Scheme.proEtale_supported_constant_presentation A i
  have hz : openConstantArrow i.openComplement.ι A ≫ ρ = 0 := by
    apply E.functor.map_injective
    apply (cancel_mono q.hom).mp
    rw [Functor.map_comp, Functor.map_zero, zero_comp, Category.assoc, hr,
      ← Category.assoc, he, Category.assoc, h, comp_zero]
  refine ⟨hz, ⟨?_⟩⟩
  apply isColimitOfReflects E.functor
  refine (isColimitMapCoconeCoforkEquiv' E.functor hz).symm ?_
  exact IsCokernel.ofIso _ hc _ k.symm (Scheme.proEtaleConstantModuleUnit X A).symm
    q.symm (by
      apply (cancel_epi k.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← he]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]) (by
      apply (cancel_epi (Scheme.proEtaleConstantModuleUnit X A).hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, Cofork.π_ofπ]
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

private noncomputable def constantHomEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} R)) :
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶ M) ≃+
      M.obj.obj (op T) :=
  ((constantSheafAdj J (ModuleCat.{u + 1} R) hT).homAddEquiv _ M).trans
    (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toAddEquiv)

private theorem constantHomEquiv_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} R))
    (f : (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶ M) :
    constantHomEquiv J hT M f = f.hom.app (op T)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))).app (op T) (1 : R)) := by
  rfl

end AlgebraicGeometry.ProEtale
