/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionSystem
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionFlatExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

set_option linter.privateModule false

/-! Compatibility of the normalized comparison with successive coefficient reduction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u vC vD vH uC uD uH
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.FiniteReduction

attribute [local irreducible] extend

private theorem conj_id {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (a₁ : L₁ ⊣ R) (a₂ : L₂ ⊣ R) :
    conjugateEquiv a₂ a₁ (Adjunction.leftAdjointUniq a₁ a₂).hom = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv]
private theorem conj_iso {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv a₁ a₂ (Adjunction.leftAdjointUniq (a₁.ofNatIsoRight e) a₂).inv = e.hom := by
  ext X
  rw [conjugateEquiv_apply_app]
  rw [Adjunction.leftAdjointUniq_inv_app, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality, ← Category.assoc,
    a₁.right_triangle_components, Category.id_comp]

private theorem ordinary_coherence (T : Scheme.{u}) (l : ℕ)
    (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) :
    (ordinaryComparison T (quotient l hnm)).hom.app
        ((extend T.smallEtaleTopology (quotient l hmr)).obj Q) ≫
      (extend (Scheme.ProEt.topology T) (quotient l hnm)).map
        ((ordinaryComparison T (quotient l hmr)).hom.app Q) ≫
      (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T).obj Q) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l n)) T).map
        ((ordinaryAssociator T.smallEtaleTopology l hmr hnm).hom.app Q) ≫
      (ordinaryComparison T (quotient l (hnm.trans hmr))).hom.app Q := by
  have hq : quotient.{u} l (hnm.trans hmr) =
      (quotient.{u} l hnm).comp (quotient.{u} l hmr) := by
    apply RingHom.ext
    intro x
    change (⟨⟨ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n))
        x.down.down⟩⟩ : Coeff.{u} l n) =
      ⟨⟨ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))
        (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m)) x.down.down)⟩⟩
    congr 2
    exact DFunLike.congr_fun (Subsingleton.elim
      (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
      ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
        (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down
  have hE := conj_iso
    ((extendAdjunction T.smallEtaleTopology (quotient l hmr)).comp
      (extendAdjunction T.smallEtaleTopology (quotient l hnm)))
    (extendAdjunction T.smallEtaleTopology (quotient l (hnm.trans hmr)))
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology (quotient l hmr) (quotient l hnm)
      (quotient l (hnm.trans hmr)) hq)
  change conjugateEquiv _ _
    (ordinaryAssociator T.smallEtaleTopology l hmr hnm).inv = _ at hE
  have hP := conj_iso
    ((extendAdjunction (Scheme.ProEt.topology T) (quotient l hmr)).comp
      (extendAdjunction (Scheme.ProEt.topology T) (quotient l hnm)))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l (hnm.trans hmr)))
    (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) (quotient l hmr) (quotient l hnm)
      (quotient l (hnm.trans hmr)) hq)
  change conjugateEquiv _ _
    (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).inv = _ at hP
  have hC (s t : ℕ) (h : t ≤ s) :
      conjugateEquiv
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l s)) T).comp
          (extendAdjunction (Scheme.ProEt.topology T) (quotient l h)))
        ((extendAdjunction T.smallEtaleTopology (quotient l h)).comp
          (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l t)) T))
        (ordinaryComparison T (quotient l h)).hom = 𝟙 _ := by
    exact conj_id _ _
  have hp := conjugateEquiv_paste
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l r)) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l m)) T)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (Coeff.{u} l n)) T)
    (extendAdjunction T.smallEtaleTopology (quotient l hmr))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l hmr))
    (extendAdjunction T.smallEtaleTopology (quotient l hnm))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l hnm))
    (extendAdjunction T.smallEtaleTopology (quotient l (hnm.trans hmr)))
    (extendAdjunction (Scheme.ProEt.topology T) (quotient l (hnm.trans hmr)))
    (ordinaryComparison T (quotient l hmr)).hom
    (ordinaryComparison T (quotient l hnm)).hom
    (ordinaryComparison T (quotient l (hnm.trans hmr))).hom
    (ordinaryAssociator T.smallEtaleTopology l hmr hnm).inv
    (ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).inv (by
      rw [hE, hP]
      rw [hC, hC, hC]
      simp only [Category.comp_id]
      ext F U x
      rfl)
  have hQ := congr_app hp Q
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hQ
  apply (Iso.cancel_iso_inv_left
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l n)) T).mapIso
      ((ordinaryAssociator T.smallEtaleTopology l hmr hnm).app Q)) _ _).mp
  simp only [Functor.mapIso_inv, Iso.app_inv,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  apply (Iso.cancel_iso_inv_right _ _
    ((ordinaryAssociator (Scheme.ProEt.topology T) l hmr hnm).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T).obj Q))).mp
  simp only [Iso.app_inv, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hQ

attribute [local irreducible] ordinaryComparison ordinaryAssociator

end AlgebraicGeometry.FiniteReduction
