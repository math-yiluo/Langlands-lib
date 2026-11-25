/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Tactic.IrreducibleDef

/-!
# Constant-coefficient pro-etale pullback comparison
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

-- Reuse the adjunction calculation from ProfiniteCoefficientInverseImage.
private theorem constantRing_adjunct_comp_comparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ R)
    (e : Rf ⋙ Rg ≅ R) {A : C} {B : D} {T : E}
    (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k ≫ e.hom.app T) =
      ((conjugateEquiv (adjg.comp adjf) adj).symm e.hom).app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A ≫ R.map _) ≫ R.map _
  rw [← unit_conjugateEquiv_symm (adjg.comp adjf) adj e.hom A,
    Category.assoc, ← e.hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]

namespace AlgebraicGeometry.Scheme

/--
The composite of the canonical constant-section coefficient comparisons is the
canonical comparison for the composite morphism.
-/
theorem proEtaleConstantRingCompositeCoefficients_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleRingCompositeCoefficients h k
      (proEtaleConstantRing V A) (proEtaleConstantRing W A)
      (proEtaleConstantRing Z A)
      (proEtaleConstantRingComparison k A)
      (proEtaleConstantRingComparison h A) =
      proEtaleConstantRingComparison (h ≫ k) A := by
  apply Iso.ext
  change (proEtaleRingInverseImageComp h k).hom.app (proEtaleConstantRing V A) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (proEtaleCoefficientInverseImageMap k A) ≫
      proEtaleCoefficientInverseImageMap h A = proEtaleCoefficientInverseImageMap (h ≫ k) A
  symm
  let B := CommRingCat.of (ULift.{u + 1, u} A)
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) h k).symm) CommRingCat.{u + 1}
        (ProEt.topology V) (ProEt.topology W) (ProEt.topology Z)
  have hρ : proEtaleConstantDirectImageMap (h ≫ k) CommRingCat.{u + 1} B =
      proEtaleConstantDirectImageMap k CommRingCat.{u + 1} B ≫
        (proEtaleSheafDirectImage k CommRingCat.{u + 1}).map
          (proEtaleConstantDirectImageMap h CommRingCat.{u + 1} B) ≫
            e.hom.app ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).obj B) := by
    apply ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{u + 1}).homEquiv
      ((Functor.const V.ProEtᵒᵖ).obj B) _).injective
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    have hf := Equiv.apply_symm_apply
      ((sheafificationAdjunction (ProEt.topology W) CommRingCat.{u + 1}).homEquiv
        ((Functor.const W.ProEtᵒᵖ).obj B)
          ((proEtaleSheafDirectImage h CommRingCat.{u + 1}).obj
            ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).obj B)))
      (Functor.whiskerLeft (proEtaleBaseChange h).op
        (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj B)))
    have hfU := congrArg (fun t ↦ t.app ((proEtaleBaseChange k).op.obj U)) hf
    change (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj B)).app
        ((proEtaleBaseChange k).op.obj U) ≫
      (proEtaleConstantDirectImageMap h CommRingCat.{u + 1} B).hom.app
        ((proEtaleBaseChange k).op.obj U) =
          (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj B)).app
            ((proEtaleBaseChange h).op.obj ((proEtaleBaseChange k).op.obj U)) at hfU
    change (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj B)).app
        ((proEtaleBaseChange (h ≫ k)).op.obj U) =
      ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj B)).app
          ((proEtaleBaseChange k).op.obj U) ≫
        (proEtaleConstantDirectImageMap h CommRingCat.{u + 1} B).hom.app
          ((proEtaleBaseChange k).op.obj U)) ≫
            ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).obj B).obj.map
              ((MorphismProperty.Over.pullbackComp
                (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U.unop).op
    rw [hfU]
    have h := (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj B)).naturality
      ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U.unop).op
    change 𝟙 B ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  change ((proEtaleSheafAdjunction (h ≫ k) CommRingCat.{u + 1}).homEquiv _ _).symm _ = _
  rw [hρ]
  exact constantRing_adjunct_comp_comparison (proEtaleSheafAdjunction k CommRingCat.{u + 1})
    (proEtaleSheafAdjunction h CommRingCat.{u + 1})
    (proEtaleSheafAdjunction (h ≫ k) CommRingCat.{u + 1}) e
    (proEtaleConstantDirectImageMap k CommRingCat.{u + 1} B)
    (proEtaleConstantDirectImageMap h CommRingCat.{u + 1} B)

/--
The canonical derived comparison for two composable morphisms with constant
coefficients, in the direction from the iterated pullback to the pullback of
the composite.
-/
noncomputable irreducible_def proEtaleConstantRingPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A k ⋙
        proEtaleConstantRingDerivedPullback A h ≅
      proEtaleConstantRingDerivedPullback A (h ≫ k) :=
  (proEtaleCanonicalPullbackComposition h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A)
    (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A)
    (proEtaleConstantRingComparison h A)).symm ≪≫
    eqToIso (congrArg (fun c ↦
      proEtaleRingDerivedPullback (h ≫ k)
        (proEtaleConstantRing V A) (proEtaleConstantRing Z A) c)
      (proEtaleConstantRingCompositeCoefficients_eq h k A))

/-- The normalized coefficient compositor, characterized by the canonical ring-sheaf
comparison and the constant-section coefficient transport. -/
theorem proEtaleConstantRingPullbackComposition_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullbackComposition h k A =
  (proEtaleCanonicalPullbackComposition h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A)
    (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A)
    (proEtaleConstantRingComparison h A)).symm ≪≫
    eqToIso (congrArg (fun c ↦
      proEtaleRingDerivedPullback (h ≫ k)
        (proEtaleConstantRing V A) (proEtaleConstantRing Z A) c)
      (proEtaleConstantRingCompositeCoefficients_eq h k A)) := by
  exact proEtaleConstantRingPullbackComposition_def h k A

end AlgebraicGeometry.Scheme

end
