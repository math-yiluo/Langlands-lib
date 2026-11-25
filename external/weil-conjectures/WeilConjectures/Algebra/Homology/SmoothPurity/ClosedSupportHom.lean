/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

public import WeilConjectures.AlgebraicGeometry.Closed.ClosedSupportHomSequence
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-!
# Closed support as a relative section complex

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md (blueprint: lemma-cycle-class-cartier-divisor).
-/

@[expose] public section

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleAbelian
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleLinear

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace CochainComplex
/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lemma-cycle-class-cartier-divisor). -/
noncomputable def closedConeLift
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0) :
    S ⟶ (mappingCone f)⟦(-1 : ℤ)⟧ where
  f p := a.f p ≫
    homotopyCofiber.inlX f p (p + (-1)) (ComplexShape.up_mk _ _ (by omega))
  comm' p q hpq := by
    obtain rfl : q = p + 1 := by simpa using hpq.symm
    rw [shiftFunctor_obj_d', Category.assoc]
    change a.f p ≫ homotopyCofiber.inlX f p (p + (-1)) _ ≫
      ((-1 : ℤ).negOnePow • (mappingCone f).d (p + (-1)) (p + 1 + (-1))) =
      S.d p (p + 1) ≫ a.f (p + 1) ≫
        homotopyCofiber.inlX f (p + 1) (p + 1 + (-1)) (ComplexShape.up_mk _ _ (by omega))
    dsimp only [mappingCone, homotopyCofiber_d]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
    have h : -( a.f p ≫ homotopyCofiber.inlX f p (p + (-1))
        (ComplexShape.up_mk _ _ (by omega)) ≫ homotopyCofiber.d f (p + (-1)) p) =
        S.d p (p + 1) ≫ a.f (p + 1) ≫
          homotopyCofiber.inlX f (p + 1) p (ComplexShape.up_mk _ _ rfl) := by
      rw [homotopyCofiber.inlX_d f (p + (-1)) p (p + 1)
        (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)]
      simp only [Preadditive.comp_add, Preadditive.comp_neg]
      have hz : a.f p ≫ f.f p = 0 := by
        simpa only [comp_f, zero_f] using congrArg (fun g ↦ g.f p) ha
      simp only [reassoc_of% hz, zero_comp, add_zero, neg_neg]
      rw [reassoc_of% (a.comm p (p + 1))]
    convert h using 1
    · simp only [show p + 1 + (-1) = p by omega, homotopyCofiber_X]
    · congr! 10 <;> omega
    · congr! 10 <;> omega

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lemma-cycle-class-cartier-divisor). -/
lemma closedConeLift_projections
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0)
    (p r : ℤ) (hr : r = p + (-1)) :
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.sndX f r = 0 ∧
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.fstX f r p (by change r + 1 = p; omega) = a.f p := by
  subst r
  dsimp only [closedConeLift, shiftFunctorObjXIso]
  simp

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lemma-cycle-class-cartier-divisor). -/
lemma closedConeLift_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) :
    QuasiIso (closedConeLift S.g S.f S.zero) := by
  classical
  have hf (p : ℤ) : Epi (S.g.f p) := by
    have := hS.epi_g
    infer_instance
  obtain ⟨κ, hκ, hqκ, _⟩ := exists_kernel_to_shifted_mappingCone_of_degreewise_epi S.g hf
  let e := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = S.f :=
    hS.fIsKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel S.g) WalkingParallelPair.zero
  have h : closedConeLift S.g S.f S.zero = e.hom ≫ κ := by
    ext p
    apply (cancel_mono
      ((mappingCone S.g).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom).mp
    apply homotopyCofiber.ext_to_X S.g (p - 1) p (by change p - 1 + 1 = p; omega)
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.2, hκ p |>.2]
      exact congrArg (fun t ↦ t.f p) he.symm
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.1, hκ p |>.1, comp_zero]
  rw [h]
  have := hqκ
  infer_instance

end CochainComplex

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]


end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lemma-cycle-class-cartier-divisor). -/
theorem closedSupportHom_globalSections_natural {A : Type (u + 1)} [CommRing A]
    {L K : Scheme.{u}} (m : K ⟶ L)
    {F F' : Sheaf L.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ L.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ K.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections L.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).hom.naturality_assoc k]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m).unit.naturality k
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.app ((upperStar (ModuleCat.{u + 1} A) m).obj F')) hu.symm

/-- Pullback of global sections as a natural transformation on sheaves.
Source: Stacks, Tag 03Q1 (blueprint: lemma-cycle-class-cartier-divisor). -/
noncomputable def closedSupportSectionsPullback (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A) where
  app J := globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J
  naturality _ _ f := closedSupportHom_globalSections_natural v f

end AlgebraicGeometry.Etale
