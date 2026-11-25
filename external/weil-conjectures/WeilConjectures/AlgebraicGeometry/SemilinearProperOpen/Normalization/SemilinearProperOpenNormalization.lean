/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaPullback
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting

/-! # Normalization of the intrinsic semilinear proper/open mate

## References

* Stacks Project, Tags 015F, 07A7 and 0F7B
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
attribute [local irreducible] alpha gamma

-- Reuse the ordinary/derived normalization calculations of the ambient comparison.
-- These private calculations precede the transfer of proper/open mate identities.
namespace Normalization
attribute [local instance] VaryingRing.push_isRightAdjoint VaryingRing.push_additive
  VaryingRing.modules_kInjective VaryingRing.pullAdditive VaryingRing.pullLimits
  VaryingRing.pullColimits VaryingRing.extensionAdditive VaryingRing.extensionLimits
  VaryingRing.extensionColimits

attribute [local instance] SemilinearProperOpen.openPull_isRightAdjoint
  SemilinearProperOpen.pull_additive SemilinearProperOpen.pull_limits
  SemilinearProperOpen.pull_colimits SemilinearProperOpen.extension_additive
  SemilinearProperOpen.extension_limits SemilinearProperOpen.extension_colimits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe v₁ v₂ w₁ w₂ h₁ h₂

private theorem system_push_comp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (SemilinearProperOpen.pushComp.{u} C τ f g) (VaryingRing.modulePComp.{u} C τ f g) := by
  unfold SemilinearProperOpen.pushComp VaryingRing.modulePComp
  congr 1
  · simp only [SemilinearProperOpen.push_eq]; rfl
  · unfold SemilinearProperOpen.push
    rw [SemilinearProperOpen.coefficientMap_forget_eq,
      SemilinearProperOpen.coefficientMap_forget_eq,
      SemilinearProperOpen.coefficientMap_forget_eq]
    rfl
  · exact proof_irrel_heq _ _

private theorem system_pull_comp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (SemilinearProperOpen.pullComp.{u} C τ f g) (VaryingRing.moduleGComp.{u} C τ f g) := by
  have := VaryingRing.push_isRightAdjoint.{u} C τ f
  have := VaryingRing.push_isRightAdjoint.{u} C τ g
  have := VaryingRing.push_isRightAdjoint.{u} C τ (f ≫ g)
  unfold SemilinearProperOpen.pullComp VaryingRing.moduleGComp
  have he := system_push_comp_heq C τ f g
  have haf : HEq (SemilinearProperOpen.ordinaryAdj.{u} C τ f) (VaryingRing.moduleAdj.{u} C τ f) :=
    chosen_adj_congr (push C τ f) (VaryingRing.push.{u} C τ f)
      (SemilinearProperOpen.push_eq.{u} C τ f)
      (rP := push_isRightAdjoint C τ f)
      (rQ := VaryingRing.push_isRightAdjoint.{u} C τ f)
  have hag : HEq (SemilinearProperOpen.ordinaryAdj.{u} C τ g) (VaryingRing.moduleAdj.{u} C τ g) :=
    chosen_adj_congr (push C τ g) (VaryingRing.push.{u} C τ g)
      (SemilinearProperOpen.push_eq.{u} C τ g)
      (rP := push_isRightAdjoint C τ g)
      (rQ := VaryingRing.push_isRightAdjoint.{u} C τ g)
  have hafg : HEq (SemilinearProperOpen.ordinaryAdj.{u} C τ (f ≫ g))
      (VaryingRing.moduleAdj.{u} C τ (f ≫ g)) :=
    chosen_adj_congr (push C τ (f ≫ g)) (VaryingRing.push.{u} C τ (f ≫ g))
      (SemilinearProperOpen.push_eq.{u} C τ (f ≫ g))
      (rP := push_isRightAdjoint C τ (f ≫ g))
      (rQ := VaryingRing.push_isRightAdjoint.{u} C τ (f ≫ g))
  have hcomp := left_comp_heq
    (SemilinearProperOpen.ordinaryAdj.{u} C τ g) (VaryingRing.moduleAdj.{u} C τ g)
    (SemilinearProperOpen.ordinaryAdj.{u} C τ f) (VaryingRing.moduleAdj.{u} C τ f)
    (SemilinearProperOpen.ordinaryAdj.{u} C τ (f ≫ g)) (VaryingRing.moduleAdj.{u} C τ (f ≫ g))
    (SemilinearProperOpen.pushComp.{u} C τ f g) (VaryingRing.modulePComp.{u} C τ f g)
    (SemilinearProperOpen.pull_eq.{u} C τ g) (SemilinearProperOpen.push_eq.{u} C τ g)
    (SemilinearProperOpen.pull_eq.{u} C τ f) (SemilinearProperOpen.push_eq.{u} C τ f)
    (SemilinearProperOpen.pull_eq.{u} C τ (f ≫ g))
    (SemilinearProperOpen.push_eq.{u} C τ (f ≫ g)) hag haf hafg he
  congr 1 <;> (simp only [SemilinearProperOpen.pull_eq]; rfl)

private theorem pcomp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (SemilinearProperOpen.pComp.{u} C τ f g) (VaryingRing.gComp.{u} C τ f g) := by
  have := VaryingRing.pullAdditive.{u} C τ f
  have := VaryingRing.pullAdditive.{u} C τ g
  have := VaryingRing.pullAdditive.{u} C τ (f ≫ g)
  have := VaryingRing.pullLimits.{u} C τ f
  have := VaryingRing.pullLimits.{u} C τ g
  have := VaryingRing.pullLimits.{u} C τ (f ≫ g)
  have := VaryingRing.pullColimits.{u} C τ f
  have := VaryingRing.pullColimits.{u} C τ g
  have := VaryingRing.pullColimits.{u} C τ (f ≫ g)
  unfold SemilinearProperOpen.pComp VaryingRing.gComp
  have hd := derived_iso_heq
    (SemilinearProperOpen.pull.{u} C τ (f ≫ g)) (VaryingRing.pull.{u} C τ (f ≫ g))
    (SemilinearProperOpen.pull.{u} C τ g ⋙ SemilinearProperOpen.pull.{u} C τ f)
    (VaryingRing.pull.{u} C τ g ⋙ VaryingRing.pull.{u} C τ f)
    (SemilinearProperOpen.pullComp.{u} C τ f g) (VaryingRing.moduleGComp.{u} C τ f g)
    (SemilinearProperOpen.pull_eq.{u} C τ (f ≫ g))
    (by simp only [SemilinearProperOpen.pull_eq]; rfl) (system_pull_comp_heq C τ f g)
    (aFp := VaryingRing.pullAdditive.{u} C τ (f ≫ g))
    (lFp := VaryingRing.pullLimits.{u} C τ (f ≫ g))
    (cFp := VaryingRing.pullColimits.{u} C τ (f ≫ g))
    (aGp := inferInstanceAs
      (VaryingRing.pull.{u} C τ g ⋙ VaryingRing.pull.{u} C τ f).Additive)
    (lGp := @comp_preservesFiniteLimits _ _ _ _ _ _
      (VaryingRing.pull.{u} C τ g) (VaryingRing.pull.{u} C τ f)
      (VaryingRing.pullLimits.{u} C τ g) (VaryingRing.pullLimits.{u} C τ f))
    (cGp := @comp_preservesFiniteColimits _ _ _ _ _ _
      (VaryingRing.pull.{u} C τ g) (VaryingRing.pull.{u} C τ f)
      (VaryingRing.pullColimits.{u} C τ g) (VaryingRing.pullColimits.{u} C τ f))
  have hc := comp_iso_heq (SemilinearProperOpen.pull.{u} C τ g) (VaryingRing.pull.{u} C τ g)
    (SemilinearProperOpen.pull.{u} C τ f) (VaryingRing.pull.{u} C τ f)
    (SemilinearProperOpen.pull_eq.{u} C τ g) (SemilinearProperOpen.pull_eq.{u} C τ f)
    (aFp := VaryingRing.pullAdditive.{u} C τ g)
    (lFp := VaryingRing.pullLimits.{u} C τ g)
    (cFp := VaryingRing.pullColimits.{u} C τ g)
    (aGp := VaryingRing.pullAdditive.{u} C τ f)
    (lGp := VaryingRing.pullLimits.{u} C τ f)
    (cGp := VaryingRing.pullColimits.{u} C τ f)
  exact trans_iso_heq _ _ _ _ (SemilinearProperOpen.P_eq.{u} C τ (f ≫ g))
    (derived_functor_eq
      (pull C τ g ⋙ pull C τ f)
      (VaryingRing.pull.{u} C τ g ⋙ VaryingRing.pull.{u} C τ f)
      (by simp only [pull_eq]; rfl)
      (aG := inferInstanceAs
        (VaryingRing.pull.{u} C τ g ⋙ VaryingRing.pull.{u} C τ f).Additive)
    (lG := @comp_preservesFiniteLimits _ _ _ _ _ _
      (VaryingRing.pull.{u} C τ g) (VaryingRing.pull.{u} C τ f)
      (VaryingRing.pullLimits.{u} C τ g) (VaryingRing.pullLimits.{u} C τ f))
    (cG := @comp_preservesFiniteColimits _ _ _ _ _ _
      (VaryingRing.pull.{u} C τ g) (VaryingRing.pull.{u} C τ f)
      (VaryingRing.pullColimits.{u} C τ g) (VaryingRing.pullColimits.{u} C τ f)))
    (by simp only [SemilinearProperOpen.P_eq]; rfl) hd
    (symm_iso_heq _ _ (by simp only [pull_eq]; rfl) (by simp only [pull_eq]; rfl) hc)

private theorem system_square_localization
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    Functor.mapDerivedCategorySquareIso (VaryingRing.moduleSquareG.{u} C τ k r p i h) =
      (VaryingRing.gComp.{u} C τ r i).symm ≪≫
        eqToIso (congrArg (VaryingRing.G.{u} C τ) h.symm) ≪≫ VaryingRing.gComp.{u} C τ k p := by
  rw [VaryingRing.moduleSquareG_eq]
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, VaryingRing.gComp,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [map_derived_transport (fun f : U ⟶ Z ↦ VaryingRing.pull.{u} C τ f) h.symm]

private theorem system_square_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    HEq (SemilinearProperOpen.squareP.{u} C τ k r p i h)
      (Functor.mapDerivedCategorySquareIso (VaryingRing.moduleSquareG.{u} C τ k r p i h)) := by
  rw [system_square_localization]
  unfold SemilinearProperOpen.squareP
  exact iso_word_heq (SemilinearProperOpen.P.{u} C τ) (VaryingRing.G.{u} C τ) h.symm
    (SemilinearProperOpen.pComp.{u} C τ r i) (VaryingRing.gComp.{u} C τ r i)
    (SemilinearProperOpen.pComp.{u} C τ k p) (VaryingRing.gComp.{u} C τ k p)
    (funext fun f ↦ SemilinearProperOpen.P_eq.{u} C τ f)
    (by simp only [SemilinearProperOpen.P_eq]; rfl)
    (by simp only [SemilinearProperOpen.P_eq]; rfl) (pcomp_heq C τ r i) (pcomp_heq C τ k p)

private theorem system_open_adjunction_exact
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    HEq (exactLocalizationDerivedAdjunction
      (VaryingRing.moduleJAdj.{u} C τ j)) (SemilinearProperOpen.jAdj.{u} C τ j) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ j
  have := SemilinearProperOpen.pull_additive.{u} C τ j
  have := SemilinearProperOpen.pull_limits.{u} C τ j
  have := SemilinearProperOpen.pull_colimits.{u} C τ j
  have := SemilinearProperOpen.extension_additive.{u} C τ j
  have := SemilinearProperOpen.extension_limits.{u} C τ j
  have := SemilinearProperOpen.extension_colimits.{u} C τ j
  unfold SemilinearProperOpen.jAdj SemilinearProperOpen.J SemilinearProperOpen.P
    SemilinearProperOpen.ordinaryOpenAdj VaryingRing.moduleJAdj
    exactLocalizationDerivedAdjunction
  exact chosen_exact_adjunction_congr (VaryingRing.pull.{u} C τ j)
    (SemilinearProperOpen.pull.{u} C τ j) (SemilinearProperOpen.pull_eq.{u} C τ j).symm
    (rP := VaryingRing.pull_isRightAdjoint.{u} C τ j)
    (rQ := openPull_isRightAdjoint C τ j)
    (aP := VaryingRing.pullAdditive.{u} C τ j)
    (aQ := pull_additive C τ j)
    (lP := VaryingRing.pullLimits.{u} C τ j)
    (cP := VaryingRing.pullColimits.{u} C τ j)
    (lQ := pull_limits C τ j)
    (cQ := pull_colimits C τ j)
    (aLP := VaryingRing.extensionAdditive.{u} C τ j)
    (aLQ := extension_additive C τ j)
    (lLP := VaryingRing.extensionLimits.{u} C τ j)
    (cLP := VaryingRing.extensionColimits.{u} C τ j)
    (lLQ := extension_limits C τ j)
    (cLQ := extension_colimits C τ j)

private theorem intrinsic_beta_inverse_mate
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (h : a ≫ i = b ≫ p) :
    ((mateEquiv (SemilinearProperOpen.jAdj.{u} C τ i) (SemilinearProperOpen.jAdj.{u} C τ b)).symm
      (TwoSquare.mk _ _ _ _ (SemilinearProperOpen.squareP.{u} C τ a b i p h).inv)) =
      SemilinearProperOpen.betaInv.{u} C τ a b i p h := by
  apply NatTrans.ext
  funext M
  exact inverse_mate_app (SemilinearProperOpen.jAdj.{u} C τ i)
    (SemilinearProperOpen.jAdj.{u} C τ b)
    (TwoSquare.mk _ _ _ _ (SemilinearProperOpen.squareP.{u} C τ a b i p h).inv) M

/-- Ambient SystemBetaLocalization. -/
private theorem system_beta_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (h : a ≫ i = b ≫ p) (sq : IsPullback a b i p) :
    HEq (localizeSquare _ _ _ _ (VaryingRing.moduleBeta.{u} C τ a b i p h sq).hom)
      (SemilinearProperOpen.beta.{u} C τ a b i p h sq).hom := by
  have hl := inverse_mate_localized
    (VaryingRing.moduleJAdj.{u} C τ i) (VaryingRing.moduleJAdj.{u} C τ b)
    (VaryingRing.moduleSquareG.{u} C τ a b i p h).symm
    (VaryingRing.moduleBeta.{u} C τ a b i p h sq).symm (fun M ↦ by
      change (VaryingRing.moduleJAdj.{u} C τ b).unit.app _ ≫
        (VaryingRing.pull.{u} C τ b).map
          (((VaryingRing.moduleJAdj.{u} C τ b).homEquiv _ _).symm _) = _
      exact unit_homEquiv_symm (VaryingRing.moduleJAdj.{u} C τ b) _)
  have hs : HEq
      (Functor.mapDerivedCategorySquareIso
        (VaryingRing.moduleSquareG.{u} C τ a b i p h).symm).hom
      (SemilinearProperOpen.squareP.{u} C τ a b i p h).inv := by
    rw [square_symm_hom]
    exact iso_inv_heq _ _ (by simp only [SemilinearProperOpen.P_eq]; rfl)
      (by simp only [SemilinearProperOpen.P_eq]; rfl) (system_square_heq C τ a b i p h).symm
  have hm := inverse_mate_heq
    (exactLocalizationDerivedAdjunction (VaryingRing.moduleJAdj.{u} C τ i))
    (SemilinearProperOpen.jAdj.{u} C τ i)
    (exactLocalizationDerivedAdjunction (VaryingRing.moduleJAdj.{u} C τ b))
    (SemilinearProperOpen.jAdj.{u} C τ b)
    (Functor.mapDerivedCategorySquareIso
      (VaryingRing.moduleSquareG.{u} C τ a b i p h).symm).hom
    (SemilinearProperOpen.squareP.{u} C τ a b i p h).inv
    (SemilinearProperOpen.J_eq.{u} C τ i).symm (SemilinearProperOpen.P_eq.{u} C τ i).symm
    (SemilinearProperOpen.J_eq.{u} C τ b).symm (SemilinearProperOpen.P_eq.{u} C τ b).symm
    (SemilinearProperOpen.P_eq.{u} C τ a).symm (SemilinearProperOpen.P_eq.{u} C τ p).symm
    (system_open_adjunction_exact C τ i) (system_open_adjunction_exact C τ b) hs
  have hm' := hm.trans (intrinsic_beta_inverse_mate C τ a b i p h).heq
  have hi := HEq.trans hl.symm.heq hm'
  rw [square_symm_hom] at hi
  change HEq (Functor.mapDerivedCategorySquareIso
    (VaryingRing.moduleBeta.{u} C τ a b i p h sq)).inv
    (SemilinearProperOpen.beta.{u} C τ a b i p h sq).inv at hi
  have hn := iso_hom_of_inv_heq _ _
    (by simp only [SemilinearProperOpen.J_eq, SemilinearProperOpen.P_eq]; rfl)
    (by simp only [SemilinearProperOpen.J_eq, SemilinearProperOpen.P_eq]; rfl) hi
  simp only [localizeSquare, localize, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso, Iso.trans_hom, Iso.symm_hom,
    Localization.liftNatIso, Functor.isoWhiskerRight_hom, NatIso.mapHomologicalComplex] at hn ⊢
  convert hn using 1; rfl

private theorem squareLift_fst {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (h : k ≫ p = r ≫ i) :
    StrictTower.squareLift k r p i h ≫ pullback.fst p i = k :=
  pullback.lift_fst k r h

private theorem squareLift_snd {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (h : k ≫ p = r ≫ i) :
    StrictTower.squareLift k r p i h ≫ pullback.snd p i = r :=
  pullback.lift_snd k r h

private theorem pi_open {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Derived C τ X) :
    (P C τ s).map ((pi C τ s).app M) =
      (jAdj C τ s).unit.app ((P C τ s).obj M) := by
  have hu := jAdj_unit_isIso C τ s
  let t : Adjunction.Triple (J C τ s) (P C τ s) (R C τ s) :=
    ⟨jAdj C τ s, adj C τ s⟩
  let ff := (jAdj C τ s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he : openToS C τ s = t.leftToRight := by
    ext N
    simp [openToS, t, Adjunction.Triple.leftToRight]
  have ho := openToS_isIso C τ s
  simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app]
  rw [Functor.map_comp]
  apply (cancel_mono ((P C τ s).map ((openToS C τ s).app ((P C τ s).obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    Category.comp_id]
  rw [he, t.leftToRight_app_obj, Functor.map_comp]
  change _ = (jAdj C τ s).unit.app _ ≫
    (P C τ s).map ((jAdj C τ s).counit.app M) ≫ _
  rw [← Category.assoc, (jAdj C τ s).right_triangle_components]
  exact (Category.id_comp _).symm

private theorem system_projector_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U X D : Scheme.{u}} (s : U ⟶ X) (c : D ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) :
    HEq ((Functor.mapDerivedCategoryIdIso (VaryingRing.Modules.{u} C τ X)).inv ≫
      localize (VaryingRing.modulePi.{u} C τ s) ≫
      (Functor.mapDerivedCategoryCompIso (VaryingRing.pull.{u} C τ s)
        (VaryingRing.extension.{u} C τ s)).inv) (SemilinearProperOpen.pi.{u} C τ s) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ s
  have := SemilinearProperOpen.pull_additive.{u} C τ s
  have := SemilinearProperOpen.pull_limits.{u} C τ s
  have := SemilinearProperOpen.pull_colimits.{u} C τ s
  have := SemilinearProperOpen.extension_additive.{u} C τ s
  have := SemilinearProperOpen.extension_limits.{u} C τ s
  have := SemilinearProperOpen.extension_colimits.{u} C τ s
  have := SemilinearProperOpen.openToS_isIso.{u} C τ s
  exact localized_projector_heq
    (VaryingRing.pull.{u} C τ s) (SemilinearProperOpen.pull.{u} C τ s)
    (VaryingRing.extension.{u} C τ s) (SemilinearProperOpen.extension.{u} C τ s)
    (VaryingRing.moduleJAdj.{u} C τ s) (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ s)
    (SemilinearProperOpen.R.{u} C τ s) (SemilinearProperOpen.adj.{u} C τ s)
    (SemilinearProperOpen.openToS.{u} C τ s) (VaryingRing.modulePi.{u} C τ s)
    (SemilinearProperOpen.pi.{u} C τ s) (SemilinearProperOpen.pull_eq.{u} C τ s).symm
    (SemilinearProperOpen.extension_eq.{u} C τ s).symm
    (chosen_adj_congr (VaryingRing.pull.{u} C τ s) (pull C τ s)
      (SemilinearProperOpen.pull_eq.{u} C τ s).symm
      (rP := VaryingRing.pull_isRightAdjoint.{u} C τ s)
      (rQ := openPull_isRightAdjoint C τ s))
    (fun M ↦ (VaryingRing.modulePi_components.{u} C τ s c hc M).1)
    (fun M ↦ pi_open C τ s M)
    (dA := derived C τ X) (dD := derived C τ U)
    (inst := openToS_isIso C τ s)
    (aF := VaryingRing.pullAdditive.{u} C τ s)
    (aFp := pull_additive C τ s)
    (aH := VaryingRing.extensionAdditive.{u} C τ s)
    (aHp := extension_additive C τ s)
    (lF := VaryingRing.pullLimits.{u} C τ s)
    (cF := VaryingRing.pullColimits.{u} C τ s)
    (lFp := pull_limits C τ s) (cFp := pull_colimits C τ s)
    (lH := VaryingRing.extensionLimits.{u} C τ s)
    (cH := VaryingRing.extensionColimits.{u} C τ s)
    (lHp := extension_limits C τ s) (cHp := extension_colimits C τ s)

private theorem ordinary_open_comp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    HEq (VaryingRing.moduleJComp.{u} C τ j b)
      (Adjunction.leftAdjointCompIso (ordinaryOpenAdj C τ j)
        (ordinaryOpenAdj C τ b) (ordinaryOpenAdj C τ (j ≫ b))
        (pullComp C τ j b).symm) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ j
  have := SemilinearProperOpen.pull_additive.{u} C τ j
  have := SemilinearProperOpen.pull_limits.{u} C τ j
  have := SemilinearProperOpen.pull_colimits.{u} C τ j
  have := SemilinearProperOpen.extension_additive.{u} C τ j
  have := SemilinearProperOpen.extension_limits.{u} C τ j
  have := SemilinearProperOpen.extension_colimits.{u} C τ j
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ b
  have := SemilinearProperOpen.pull_additive.{u} C τ b
  have := SemilinearProperOpen.pull_limits.{u} C τ b
  have := SemilinearProperOpen.pull_colimits.{u} C τ b
  have := SemilinearProperOpen.extension_additive.{u} C τ b
  have := SemilinearProperOpen.extension_limits.{u} C τ b
  have := SemilinearProperOpen.extension_colimits.{u} C τ b
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.pull_additive.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.pull_limits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.pull_colimits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_additive.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_limits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_colimits.{u} C τ (j ≫ b)
  have hj : HEq (VaryingRing.moduleJAdj.{u} C τ j)
      (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ j) :=
    chosen_adj_congr (VaryingRing.pull.{u} C τ j) (pull C τ j)
      (SemilinearProperOpen.pull_eq.{u} C τ j).symm
      (rP := VaryingRing.pull_isRightAdjoint.{u} C τ j)
      (rQ := openPull_isRightAdjoint C τ j)
  have hb : HEq (VaryingRing.moduleJAdj.{u} C τ b)
      (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ b) :=
    chosen_adj_congr (VaryingRing.pull.{u} C τ b) (pull C τ b)
      (SemilinearProperOpen.pull_eq.{u} C τ b).symm
      (rP := VaryingRing.pull_isRightAdjoint.{u} C τ b)
      (rQ := openPull_isRightAdjoint C τ b)
  have hjb : HEq (VaryingRing.moduleJAdj.{u} C τ (j ≫ b))
      (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ (j ≫ b)) :=
    chosen_adj_congr (VaryingRing.pull.{u} C τ (j ≫ b)) (pull C τ (j ≫ b))
      (SemilinearProperOpen.pull_eq.{u} C τ (j ≫ b)).symm
      (rP := VaryingRing.pull_isRightAdjoint.{u} C τ (j ≫ b))
      (rQ := openPull_isRightAdjoint C τ (j ≫ b))
  exact left_comp_heq
    (VaryingRing.moduleJAdj.{u} C τ j) (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ j)
    (VaryingRing.moduleJAdj.{u} C τ b) (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ b)
    (VaryingRing.moduleJAdj.{u} C τ (j ≫ b))
      (SemilinearProperOpen.ordinaryOpenAdj.{u} C τ (j ≫ b))
    (VaryingRing.moduleGComp.{u} C τ j b).symm (SemilinearProperOpen.pullComp.{u} C τ j b).symm
    (SemilinearProperOpen.extension_eq.{u} C τ j).symm
    (SemilinearProperOpen.pull_eq.{u} C τ j).symm
    (SemilinearProperOpen.extension_eq.{u} C τ b).symm
    (SemilinearProperOpen.pull_eq.{u} C τ b).symm
    (SemilinearProperOpen.extension_eq.{u} C τ (j ≫ b)).symm
    (SemilinearProperOpen.pull_eq.{u} C τ (j ≫ b)).symm hj hb hjb
    (symm_iso_heq _ _ (SemilinearProperOpen.pull_eq.{u} C τ (j ≫ b)).symm
      (congrArg₂ Functor.comp (SemilinearProperOpen.pull_eq.{u} C τ b).symm
        (SemilinearProperOpen.pull_eq.{u} C τ j).symm)
      (system_pull_comp_heq C τ j b).symm)

private theorem system_open_comp_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    HEq (Functor.mapDerivedCategoryCompIso (VaryingRing.extension.{u} C τ j)
      (VaryingRing.extension.{u} C τ b) ≪≫
      Functor.mapDerivedCategoryNatIso (VaryingRing.moduleJComp.{u} C τ j b))
      (SemilinearProperOpen.jComp.{u} C τ j b) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ j
  have := SemilinearProperOpen.pull_additive.{u} C τ j
  have := SemilinearProperOpen.pull_limits.{u} C τ j
  have := SemilinearProperOpen.pull_colimits.{u} C τ j
  have := SemilinearProperOpen.extension_additive.{u} C τ j
  have := SemilinearProperOpen.extension_limits.{u} C τ j
  have := SemilinearProperOpen.extension_colimits.{u} C τ j
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ b
  have := SemilinearProperOpen.pull_additive.{u} C τ b
  have := SemilinearProperOpen.pull_limits.{u} C τ b
  have := SemilinearProperOpen.pull_colimits.{u} C τ b
  have := SemilinearProperOpen.extension_additive.{u} C τ b
  have := SemilinearProperOpen.extension_limits.{u} C τ b
  have := SemilinearProperOpen.extension_colimits.{u} C τ b
  have := SemilinearProperOpen.openPull_isRightAdjoint.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.pull_additive.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.pull_limits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.pull_colimits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_additive.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_limits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_colimits.{u} C τ (j ≫ b)
  let o := Adjunction.leftAdjointCompIso (ordinaryOpenAdj C τ j)
    (ordinaryOpenAdj C τ b) (ordinaryOpenAdj C τ (j ≫ b)) (pullComp C τ j b).symm
  have he := localized_comp_iso_heq
    (VaryingRing.extension.{u} C τ j) (extension C τ j)
    (VaryingRing.extension.{u} C τ b) (extension C τ b)
    (VaryingRing.extension.{u} C τ (j ≫ b)) (extension C τ (j ≫ b))
    (VaryingRing.moduleJComp.{u} C τ j b) o
    (extension_eq C τ j).symm (extension_eq C τ b).symm
    (extension_eq C τ (j ≫ b)).symm (ordinary_open_comp_heq C τ j b)
    (aF := VaryingRing.extensionAdditive.{u} C τ j)
    (lF := VaryingRing.extensionLimits.{u} C τ j)
    (cF := VaryingRing.extensionColimits.{u} C τ j)
    (aFp := extension_additive C τ j)
    (lFp := extension_limits C τ j)
    (cFp := extension_colimits C τ j)
    (aG := VaryingRing.extensionAdditive.{u} C τ b)
    (lG := VaryingRing.extensionLimits.{u} C τ b)
    (cG := VaryingRing.extensionColimits.{u} C τ b)
    (aGp := extension_additive C τ b)
    (lGp := extension_limits C τ b)
    (cGp := extension_colimits C τ b)
    (aH := VaryingRing.extensionAdditive.{u} C τ (j ≫ b))
    (lH := VaryingRing.extensionLimits.{u} C τ (j ≫ b))
    (cH := VaryingRing.extensionColimits.{u} C τ (j ≫ b))
    (aHp := extension_additive C τ (j ≫ b))
    (lHp := extension_limits C τ (j ≫ b))
    (cHp := extension_colimits C τ (j ≫ b))
  have hl := open_comp_localized (ordinaryOpenAdj C τ j) (ordinaryOpenAdj C τ b)
    (ordinaryOpenAdj C τ (j ≫ b)) (pullComp C τ j b).symm
  have ho : jComp C τ j b =
      Functor.mapDerivedCategoryCompIso (extension C τ j) (extension C τ b) ≪≫
        Functor.mapDerivedCategoryNatIso o := by
    have hs : Functor.mapDerivedCategoryNatIso (pullComp C τ j b).symm =
        (Functor.mapDerivedCategoryNatIso (pullComp C τ j b)).symm :=
      Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
    dsimp only [J, pComp, jComp, jAdj]
    erw [Iso.trans_symm]
    simp only [Functor.exactDerivedRestrictionComposition, hs] at hl
    convert hl using 1; rfl
  exact he.trans ho.symm.heq

private theorem system_open_cell_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion k] (h : j ≫ b = k) :
    HEq ((Functor.mapDerivedCategoryCompIso (VaryingRing.extension.{u} C τ j)
      (VaryingRing.extension.{u} C τ b)).hom ≫ localize
        ((VaryingRing.moduleJComp.{u} C τ j b).hom ≫ (VaryingRing.moduleJCongr.{u} C τ h).hom))
      ((SemilinearProperOpen.jComp.{u} C τ j b).hom ≫
        (SemilinearProperOpen.jCongr.{u} C τ h).hom) := by
  subst k
  have := SemilinearProperOpen.extension_additive.{u} C τ j
  have := SemilinearProperOpen.extension_limits.{u} C τ j
  have := SemilinearProperOpen.extension_colimits.{u} C τ j
  have := SemilinearProperOpen.extension_additive.{u} C τ b
  have := SemilinearProperOpen.extension_limits.{u} C τ b
  have := SemilinearProperOpen.extension_colimits.{u} C τ b
  have := SemilinearProperOpen.extension_additive.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_limits.{u} C τ (j ≫ b)
  have := SemilinearProperOpen.extension_colimits.{u} C τ (j ≫ b)
  have hn := hom_iso_heq _ _
    (congrArg₂ Functor.comp (SemilinearProperOpen.J_eq.{u} C τ j).symm
      (SemilinearProperOpen.J_eq.{u} C τ b).symm)
    (SemilinearProperOpen.J_eq.{u} C τ (j ≫ b)).symm (system_open_comp_localized C τ j b)
  simp only [VaryingRing.moduleJCongr, SemilinearProperOpen.jCongr,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso,
    Functor.isoWhiskerRight_hom, NatIso.mapHomologicalComplex, localize] at hn ⊢
  convert hn using 1; rfl

private theorem system_pull_cell_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    (h : j ≫ b = k) :
    HEq ((Functor.mapDerivedCategoryCompIso (VaryingRing.pull.{u} C τ b)
      (VaryingRing.pull.{u} C τ j)).hom ≫ localize
        ((VaryingRing.moduleGComp.{u} C τ j b).inv ≫
          (eqToIso (congrArg (VaryingRing.pull.{u} C τ) h)).hom))
      ((SemilinearProperOpen.pComp.{u} C τ j b).inv ≫
        (eqToIso (congrArg (SemilinearProperOpen.P.{u} C τ) h)).hom) := by
  subst k
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  have he := iso_inv_heq _ _
    (SemilinearProperOpen.P_eq.{u} C τ (j ≫ b)).symm
    (congrArg₂ Functor.comp (SemilinearProperOpen.P_eq.{u} C τ b).symm
      (SemilinearProperOpen.P_eq.{u} C τ j).symm) (pcomp_heq C τ j b).symm
  dsimp only [VaryingRing.G] at he
  simp only [pComp, VaryingRing.gComp, Iso.trans_inv,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso,
    NatIso.mapHomologicalComplex, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv] at he
  convert he using 1; rfl

/-- Ambient SystemClopenLocalization. -/
private theorem system_alpha_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    HEq (localizeSquare _ _ _ _ (VaryingRing.moduleAlpha.{u} C τ k r p i h))
      (SemilinearProperOpen.alpha.{u} C τ k r p i h) := by
  let s := StrictTower.squareLift k r p i h
  have : IsOpenImmersion s := (StrictTower.squareLift_clopen k r p i h).1
  have : IsClosedImmersion s := (StrictTower.squareLift_clopen k r p i h).2
  let a := pullback.snd p i
  let b := pullback.fst p i
  let c : (pullback p i).Opens :=
    ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hc : Set.range c.ι = (Set.range s)ᶜ := Scheme.Opens.range_ι c
  let X : Fin 5 → Scheme.{u} := ![W, pullback p i, U, V, Z]
  let D (n : Fin 5) := VaryingRing.Modules.{u} C τ (X n)
  let cD : ∀ n, Category.{u + 1} (D n) := fun n ↦ inferInstance
  let aD : ∀ n, Abelian (D n) := fun n ↦ inferInstance
  let dD : ∀ n, HasDerivedCategory.{u + 2} (D n) := fun n ↦ inferInstance
  let eI := ExactFunctor.of (VaryingRing.extension.{u} C τ i)
  let eP := ExactFunctor.of (VaryingRing.pull.{u} C τ p)
  let eQ := ExactFunctor.of (VaryingRing.pull.{u} C τ a)
  let eS := ExactFunctor.of (VaryingRing.pull.{u} C τ s)
  let eJ := ExactFunctor.of (VaryingRing.extension.{u} C τ s)
  let eB := ExactFunctor.of (VaryingRing.extension.{u} C τ b)
  let eK := ExactFunctor.of (VaryingRing.extension.{u} C τ k)
  let eR := ExactFunctor.of (VaryingRing.pull.{u} C τ r)
  have hl := clopen_composite_localized D eI eP eQ eS eJ eB eK eR
    (VaryingRing.moduleBeta.{u} C τ a b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip).hom
    (VaryingRing.modulePi.{u} C τ s)
    ((VaryingRing.moduleJComp.{u} C τ s b).hom ≫
      (VaryingRing.moduleJCongr.{u} C τ (squareLift_fst k r p i h)).hom)
    ((VaryingRing.moduleGComp.{u} C τ s a).inv ≫
      (eqToIso (congrArg (VaryingRing.pull.{u} C τ) (squareLift_snd k r p i h))).hom)
    (aI := VaryingRing.extensionAdditive.{u} C τ i)
    (aP := VaryingRing.pullAdditive.{u} C τ p)
    (aQ := VaryingRing.pullAdditive.{u} C τ a)
    (aS := VaryingRing.pullAdditive.{u} C τ s)
    (aJ := VaryingRing.extensionAdditive.{u} C τ s)
    (aB := VaryingRing.extensionAdditive.{u} C τ b)
    (aK := VaryingRing.extensionAdditive.{u} C τ k)
    (aR := VaryingRing.pullAdditive.{u} C τ r)
  have ho : VaryingRing.moduleAlpha.{u} C τ k r p i h =
      clopenMateComposite _ _ _ _ _ _ _ _
        (VaryingRing.moduleBeta.{u} C τ a b i p pullback.condition.symm
          (IsPullback.of_hasPullback p i).flip).hom
        (VaryingRing.modulePi.{u} C τ s)
        ((VaryingRing.moduleJComp.{u} C τ s b).hom ≫
          (VaryingRing.moduleJCongr.{u} C τ (squareLift_fst k r p i h)).hom)
        ((VaryingRing.moduleGComp.{u} C τ s a).inv ≫
          (eqToIso (congrArg (VaryingRing.pull.{u} C τ) (squareLift_snd k r p i h))).hom) :=
    expanded_clopen_composite _ _ _ _ _ _ _ _ _ _ _ _
  dsimp only [eI, eP, eQ, eS, eJ, eB, eK, eR, ExactFunctor.of_fst] at hl
  dsimp only [D, X, cD, aD, dD] at hl
  erw [← ho] at hl
  apply HEq.trans hl.heq
  have ht := clopen_composite_heq
    (VaryingRing.J.{u} C τ i) (SemilinearProperOpen.J.{u} C τ i)
    (VaryingRing.G.{u} C τ p) (SemilinearProperOpen.P.{u} C τ p)
    (VaryingRing.G.{u} C τ a) (SemilinearProperOpen.P.{u} C τ a)
    (VaryingRing.G.{u} C τ s) (SemilinearProperOpen.P.{u} C τ s)
    (VaryingRing.J.{u} C τ s) (SemilinearProperOpen.J.{u} C τ s)
    (VaryingRing.J.{u} C τ b) (SemilinearProperOpen.J.{u} C τ b)
    (VaryingRing.J.{u} C τ k) (SemilinearProperOpen.J.{u} C τ k)
    (VaryingRing.G.{u} C τ r) (SemilinearProperOpen.P.{u} C τ r)
    _ _ _ _ _ _ _ _
    (SemilinearProperOpen.J_eq.{u} C τ i).symm (SemilinearProperOpen.P_eq.{u} C τ p).symm
    (SemilinearProperOpen.P_eq.{u} C τ a).symm (SemilinearProperOpen.P_eq.{u} C τ s).symm
    (SemilinearProperOpen.J_eq.{u} C τ s).symm (SemilinearProperOpen.J_eq.{u} C τ b).symm
    (SemilinearProperOpen.J_eq.{u} C τ k).symm (SemilinearProperOpen.P_eq.{u} C τ r).symm
    (system_beta_localized C τ a b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip)
    (system_projector_localized C τ s c.ι hc)
    (system_open_cell_localized C τ s b k (squareLift_fst k r p i h))
    (system_pull_cell_localized C τ s a r (squareLift_snd k r p i h))
  apply ht.trans
  unfold SemilinearProperOpen.alpha
  exact (expanded_clopen_composite (J C τ i) (P C τ p) (P C τ a) (P C τ s)
    (J C τ s) (J C τ b) (J C τ k) (P C τ r) _ _ _ _).symm.heq

private theorem adj_heq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (adj C τ f) (VaryingRing.adj.{u} C τ f) := by
  have := VaryingRing.push_isRightAdjoint.{u} C τ f
  have := VaryingRing.push_additive.{u} C τ f
  have := VaryingRing.pullAdditive.{u} C τ f
  have := VaryingRing.pullLimits.{u} C τ f
  have := VaryingRing.pullColimits.{u} C τ f
  unfold adj VaryingRing.adj
  exact derived_adj_heq (ordinaryAdj C τ f) (VaryingRing.moduleAdj.{u} C τ f)
    (pull_eq C τ f) (push_eq C τ f)
    (chosen_adj_congr (push C τ f) (VaryingRing.push.{u} C τ f) (push_eq C τ f)
      (rP := push_isRightAdjoint C τ f)
      (rQ := VaryingRing.push_isRightAdjoint.{u} C τ f))
    (aL := pull_additive C τ f)
    (aR := push_additive C τ f)
    (lL := pull_limits C τ f) (cL := pull_colimits C τ f)
    (aLp := VaryingRing.pullAdditive.{u} C τ f)
    (lLp := VaryingRing.pullLimits.{u} C τ f)
    (cLp := VaryingRing.pullColimits.{u} C τ f)
    (aRp := VaryingRing.push_additive.{u} C τ f)

/-- The intrinsic proper/open mate agrees with the varying-ring mate before evaluation. -/
theorem gamma_normalization {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    HEq (gamma C τ k r p i h) (VaryingRing.gamma.{u} C τ k r p i h) := by
  unfold gamma VaryingRing.gamma
  have ha : HEq (alpha C τ k r p i h) (VaryingRing.alpha.{u} C τ k r p i h) :=
    (system_alpha_localized C τ k r p i h).symm
  exact mate_heq (adj C τ r) (VaryingRing.adj.{u} C τ r)
    (adj C τ p) (VaryingRing.adj.{u} C τ p) _ _
    (P_eq C τ r) (R_eq C τ r) (P_eq C τ p) (R_eq C τ p)
    (J_eq C τ i) (J_eq C τ k) (adj_heq C τ r) (adj_heq C τ p) ha

private theorem push_id_heq (X : Scheme.{u}) :
    HEq (pushId_existsUnique C τ X).choose (VaryingRing.modulePId.{u} C τ X) := by
  unfold VaryingRing.modulePId
  congr 1
  · simp only [push_eq]
    rfl
  · unfold push
    rw [coefficientMap_forget_eq]
    rfl
  · exact proof_irrel_heq _ _

private theorem pid_heq (X : Scheme.{u}) :
    HEq (pId C τ X) (VaryingRing.gId.{u} C τ X) := by
  have := VaryingRing.push_isRightAdjoint.{u} C τ (𝟙 X)
  have := VaryingRing.push_additive.{u} C τ (𝟙 X)
  have := VaryingRing.pullAdditive.{u} C τ (𝟙 X)
  have := VaryingRing.pullLimits.{u} C τ (𝟙 X)
  have := VaryingRing.pullColimits.{u} C τ (𝟙 X)
  have hi := left_id_heq (ordinaryAdj C τ (𝟙 X)) (VaryingRing.moduleAdj.{u} C τ (𝟙 X))
    (pushId_existsUnique C τ X).choose (VaryingRing.modulePId.{u} C τ X)
    (pull_eq C τ (𝟙 X)) (push_eq C τ (𝟙 X))
    (chosen_adj_congr (push C τ (𝟙 X)) (VaryingRing.push.{u} C τ (𝟙 X))
      (push_eq C τ (𝟙 X)) (rP := push_isRightAdjoint C τ (𝟙 X))
      (rQ := VaryingRing.push_isRightAdjoint.{u} C τ (𝟙 X))) (push_id_heq C τ X)
  have hd := derived_iso_heq (pull C τ (𝟙 X)) (VaryingRing.pull.{u} C τ (𝟙 X))
    (𝟭 (Modules C τ X)) (𝟭 (Modules C τ X)) _ _ (pull_eq C τ (𝟙 X)) rfl hi
    (aFp := VaryingRing.pullAdditive.{u} C τ (𝟙 X))
    (lFp := VaryingRing.pullLimits.{u} C τ (𝟙 X))
    (cFp := VaryingRing.pullColimits.{u} C τ (𝟙 X))
  exact trans_iso_heq _ _ (Functor.mapDerivedCategoryIdIso (Modules C τ X))
    (Functor.mapDerivedCategoryIdIso (Modules C τ X)) (P_eq C τ (𝟙 X)) rfl rfl hd HEq.rfl

private theorem sid_heq (X : Scheme.{u}) :
    HEq (sId C τ X) (VaryingRing.pId.{u} C τ X) := by
  have h := conjugate_iso_heq Adjunction.id Adjunction.id
    (adj C τ (𝟙 X)) (VaryingRing.adj.{u} C τ (𝟙 X))
    (pId C τ X) (VaryingRing.gId.{u} C τ X) rfl rfl
    (P_eq C τ (𝟙 X)) (R_eq C τ (𝟙 X)) HEq.rfl
    (adj_heq C τ (𝟙 X)) (pid_heq C τ X)
  exact symm_iso_heq _ _ rfl (R_eq C τ (𝟙 X)) h

private theorem jadj_heq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    HEq (jAdj C τ j) (VaryingRing.jAdj.{u} C τ j) := by
  have h := exact_adjunction_eq (VaryingRing.moduleJAdj.{u} C τ j)
  exact (system_open_adjunction_exact C τ j).symm.trans h.symm.heq

private theorem jid_heq (X : Scheme.{u}) :
    HEq (jId C τ X) (VaryingRing.jId.{u} C τ X) := by
  exact left_id_heq (jAdj C τ (𝟙 X)) (VaryingRing.jAdj.{u} C τ (𝟙 X))
    (pId C τ X) (VaryingRing.gId.{u} C τ X) (J_eq C τ (𝟙 X)) (P_eq C τ (𝟙 X))
    (jadj_heq C τ (𝟙 X)) (pid_heq C τ X)
private theorem scomp_heq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (sComp C τ f g) (VaryingRing.pComp.{u} C τ f g) := by
  unfold sComp VaryingRing.pComp
  exact conjugate_iso_heq ((adj C τ g).comp (adj C τ f))
    ((VaryingRing.adj.{u} C τ g).comp (VaryingRing.adj.{u} C τ f))
    (adj C τ (f ≫ g)) (VaryingRing.adj.{u} C τ (f ≫ g)) _ _
    (by simp only [P_eq]; rfl) (by simp only [R_eq]; rfl) (P_eq C τ (f ≫ g))
    (R_eq C τ (f ≫ g))
    (adj_comp_heq _ _ _ _ (P_eq C τ g) (R_eq C τ g) (P_eq C τ f) (R_eq C τ f)
      (adj_heq C τ g) (adj_heq C τ f))
    (adj_heq C τ (f ≫ g)) (pcomp_heq C τ f g)

private theorem jcomp_heq {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    HEq (jComp C τ j b) (VaryingRing.jComp.{u} C τ j b) :=
  (system_open_comp_localized C τ j b).symm

private theorem beta_heq {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    HEq (beta C τ a j' j g h sq) (VaryingRing.alphaPullbackBeta.{u} C τ a j' j g h sq) := by
  apply iso_heq_of_hom_heq _ _
    (by simp only [J_eq, P_eq]; rfl) (by simp only [J_eq, P_eq]; rfl)
  dsimp only [VaryingRing.J, VaryingRing.G]
  have hn := (system_beta_localized C τ a j' j g h sq).symm
  simp only [VaryingRing.alphaPullbackBeta,
    localizeSquare, localize,
    Functor.mapDerivedCategoryNatIso, Iso.trans_hom, Iso.symm_hom,
    Localization.liftNatIso, Functor.isoWhiskerRight_hom, NatIso.mapHomologicalComplex] at hn ⊢
  convert hn using 1; rfl

private def varyingExchange {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    VaryingRing.P.{u} C τ p ⋙ VaryingRing.G.{u} C τ i ⟶
      VaryingRing.G.{u} C τ k ⋙ VaryingRing.P.{u} C τ r :=
  mateEquiv (VaryingRing.adj.{u} C τ p) (VaryingRing.adj.{u} C τ r)
    (VaryingRing.alphaPullbackSquareG.{u} C τ k r p i h).hom

private theorem exchange_heq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    HEq (exchange C τ k r p i h) (varyingExchange C τ k r p i h) := by
  unfold exchange varyingExchange
  exact mate_heq (adj C τ p) (VaryingRing.adj.{u} C τ p)
    (adj C τ r) (VaryingRing.adj.{u} C τ r) _ _
    (P_eq C τ p) (R_eq C τ p) (P_eq C τ r) (R_eq C τ r)
    (P_eq C τ i) (P_eq C τ k) (adj_heq C τ p) (adj_heq C τ r)
    (hom_iso_heq _ _ (by simp only [P_eq]; rfl) (by simp only [P_eq]; rfl)
      (system_square_heq C τ k r p i h))

private theorem varying_cube :
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (_sp : IsPullback a p₁ p b) (_sr : IsPullback d r₁ r c) (M : Derived C τ V),
      (VaryingRing.G.{u} C τ b).map ((VaryingRing.gamma.{u} C τ k r p i h).app M) ≫
          (varyingExchange C τ a p₁ p b wp).app ((VaryingRing.J.{u} C τ k).obj M) ≫
          (VaryingRing.P.{u} C τ p₁).map
            ((VaryingRing.alphaPullbackBeta.{u} C τ d k₁ k a wk sk).hom.app M) =
        (VaryingRing.alphaPullbackBeta.{u} C τ c i₁ i b wi si).hom.app
          ((VaryingRing.P.{u} C τ r).obj M) ≫
          (VaryingRing.J.{u} C τ i₁).map ((varyingExchange C τ d r₁ r c wr).app M) ≫
          (VaryingRing.gamma.{u} C τ k₁ r₁ p₁ i₁ h₁).app ((VaryingRing.G.{u} C τ d).obj M)) := by
  intro V W S T V₁ W₁ S₁ T₁ k i r p k₁ i₁ r₁ p₁ a b c d
    _ _ _ _ _ _ _ _ _ _ _ _ h h₁ wk wi wp wr sk si sp sr M
  exact forward_cube (VaryingRing.adj.{u} C τ r) (VaryingRing.adj.{u} C τ p)
    (VaryingRing.adj.{u} C τ r₁) (VaryingRing.adj.{u} C τ p₁)
    (VaryingRing.G.{u} C τ c) (VaryingRing.G.{u} C τ d)
    (VaryingRing.G.{u} C τ b) (VaryingRing.G.{u} C τ a)
    (VaryingRing.alphaPullbackSquareG.{u} C τ d r₁ r c wr).symm
    (VaryingRing.alphaPullbackBeta.{u} C τ c i₁ i b wi si)
    (VaryingRing.alphaPullbackBeta.{u} C τ d k₁ k a wk sk)
    (VaryingRing.alphaPullbackSquareG.{u} C τ a p₁ p b wp).symm
    (VaryingRing.alpha.{u} C τ k r p i h) (VaryingRing.alpha.{u} C τ k₁ r₁ p₁ i₁ h₁)
    (VaryingRing.alpha_baseChange.{u} C τ k i r p k₁ i₁ r₁ p₁ a b c d
      h h₁ wk wi wp wr sk si sp sr) M

end Normalization

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
