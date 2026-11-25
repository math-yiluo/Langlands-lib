/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarGeometricAdjunctions
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullback
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence

/-! # The fixed finite realization, inverse image and the consecutive scalar squares

The fixed sheaf realization commutes with inverse image through the mate of the
identity on sections of direct images. This comparison is compatible with the
section-normalized consecutive scalar squares and the restriction/pullback mates.

## References

* Stacks Project, Modules on Sites, Tags 03CY, 03D8 and 03DA
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The fixed sheaf realization is an equivalence. -/
instance lisseTowerFixedSheafRealization_isEquivalence {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFixedSheafRealization f d n).IsEquivalence := by
  let e := RingEquiv.ofBijective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n)
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (constantAdicQuotientMap d.ideal n)).IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars e.toRingHom).IsEquivalence
  have : (sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (constantAdicQuotientMap d.ideal n))).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ _
  unfold lisseTowerFixedSheafRealization
  infer_instance

/- Chaining an elementwise equation through two further maps. -/
private theorem chain3_eq {α β γ δ : Type*} {f₁ : α → β} {f₂ : β → γ} {f₃ : γ → δ}
    {x : α} {y : β} {z : δ} (h₁ : f₁ x = y) (h : f₃ (f₂ y) = z) : f₃ (f₂ (f₁ x)) = z := by
  rw [h₁, h]

/- Chaining an elementwise equation through a further map. -/
private theorem chain2_eq {α β γ : Type*} {f₁ : α → β} {f₂ : β → γ}
    {x : α} {y : β} {z : γ} (h₁ : f₁ x = y) (h : f₂ y = z) : f₂ (f₁ x) = z := by
  rw [h₁, h]

/- Rewriting the argument of a composite. -/
private theorem congr_apply_eq {α β γ : Type*} {F : β → γ} {G : α → β}
    {a a' : α} {z : γ} (h : a = a') (h' : F (G a') = z) : F (G a) = z := by
  rw [h, h']

section Pullback

variable {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)

/-- The coefficient sheaf after inverse image along `g`. -/
abbrev lisseTowerPulledRing (g : Y ⟶ X) (j : ℕ) :=
  (adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op j))

/-- Module inverse image along `f`, with the composite coefficient identification. -/
abbrev lisseTowerStepPullback :=
  proEtaleRingModulePullback f (lisseTowerPulledRing d g j) (lisseTowerPulledRing d (f ≫ g) j)
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j)))

/-- Module direct image along `f`, with the composite coefficient identification. -/
abbrev lisseTowerStepDirectImage :=
  proEtaleRingModuleDirectImage f (lisseTowerPulledRing d g j)
    (lisseTowerPulledRing d (f ≫ g) j)
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j)))

/-- The canonical adjunction for `lisseTowerStepPullback`. -/
abbrev lisseTowerStepAdjunction :
    lisseTowerStepPullback f g d j ⊣ lisseTowerStepDirectImage f g d j :=
  proEtaleRingModuleAdjunction f (lisseTowerPulledRing d g j)
    (lisseTowerPulledRing d (f ≫ g) j)
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j)))

/-- The finite realization commutes with direct image, by the identity on sections. -/
def lisseTowerFiniteDirectImageIso :
    lisseTowerFiniteSheafRealization (f ≫ g) d j ⋙ lisseTowerStepDirectImage f g d j ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) f ⋙
        lisseTowerFiniteSheafRealization g d j := by
  let Q := A ⧸ d.ideal ^ (j + 1)
  let P := PresheafOfModules.pushforward₀ (proEtaleBaseChange f)
    ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of Q))
  have : (coefficientRestriction g d j).Full :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap g d j)).fullyFaithfulROfIsIsoCounit.full
  have : (coefficientRestriction g d j).Faithful :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap g d j)).fullyFaithfulROfIsIsoCounit.faithful
  exact Functor.fullyFaithfulCancelRight (coefficientRestriction g d j)
    (Functor.associator (lisseTowerFiniteSheafRealization (f ≫ g) d j)
      (proEtaleRingModuleDirectImage f (lisseTowerPulledRing d g j)
        (lisseTowerPulledRing d (f ≫ g) j)
        ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op j))))
      (coefficientRestriction g d j) ≪≫
      Functor.isoWhiskerLeft (lisseTowerFiniteSheafRealization (f ≫ g) d j)
        (restrictionDirectImageIso f g d j) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (coefficientUnitIso (f ≫ g) d j).symm P ≪≫
      (Iso.refl _ : coefficientEmbedding W Q ⋙ P ≅
        ProEtale.lowerStar (ModuleCat.{u + 1} Q) f ⋙ coefficientEmbedding Y Q) ≪≫
      Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} Q) f)
        (coefficientUnitIso g d j) ≪≫ (Functor.associator _ _ _).symm)

/-- Direct image commutes with restriction of coefficients, by the identity. -/
def lisseTowerLowerStarRestrictIso :
    ProEtale.lowerStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j)) ≅
      sheafCompose (ProEt.topology W)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j)) ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))) f :=
  Iso.refl _

/-- Direct image followed by the fixed realization is the fixed realization followed by
module direct image; the comparison is the identity on sections. -/
def lisseTowerFixedDirectImageIso :
    ProEtale.lowerStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f ⋙
        lisseTowerFixedSheafRealization g d j ≅
      lisseTowerFixedSheafRealization (f ≫ g) d j ⋙ lisseTowerStepDirectImage f g d j :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (lisseTowerLowerStarRestrictIso f d j)
      (lisseTowerFiniteSheafRealization g d j) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (lisseTowerFiniteDirectImageIso f g d j).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The fixed realization commutes with inverse image: the left adjoint mate of
`lisseTowerFixedDirectImageIso`. -/
def lisseTowerFixedPullbackIso :
    ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f ⋙
        lisseTowerFixedSheafRealization (f ≫ g) d j ≅
      lisseTowerFixedSheafRealization g d j ⋙ lisseTowerStepPullback f g d j :=
  (adjunctionSquare (lisseTowerFixedSheafRealization g d j)
    (lisseTowerFixedSheafRealization (f ≫ g) d j)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f)
    (lisseTowerStepAdjunction f g d j) (lisseTowerFixedDirectImageIso f g d j)).choose

/-- The adjunct of the inverse pullback comparison is the unit followed by the direct
image comparison. -/
theorem lisseTowerFixedPullbackIso_inv_homEquiv
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :
    (lisseTowerStepAdjunction f g d j).homEquiv _ _
        ((lisseTowerFixedPullbackIso f g d j).inv.app P) =
      (lisseTowerFixedSheafRealization g d j).map
          ((ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f).unit.app P) ≫
        (lisseTowerFixedDirectImageIso f g d j).hom.app _ := by
  have h := (adjunctionSquare (lisseTowerFixedSheafRealization g d j)
    (lisseTowerFixedSheafRealization (f ≫ g) d j)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f)
    (lisseTowerStepAdjunction f g d j)
      (lisseTowerFixedDirectImageIso f g d j)).choose_spec.1 P _ (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_id] at h
  exact h

private theorem coefficientUnitIso_inv_fsrSection
    (K : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))))
    (V : Y.ProEtᵒᵖ) (y : K.obj.obj V) :
    ((coefficientUnitIso g d j).inv.app K).app V (fsrSection g d j K V y) = y := by
  have h := congrArg (fun φ => φ.app V y) ((coefficientUnitIso g d j).hom_inv_id_app K)
  change ((coefficientUnitIso g d j).inv.app K).app V
    (((coefficientUnitIso g d j).hom.app K).app V y) = y
  simpa only [PresheafOfModules.comp_app, ModuleCat.comp_apply, PresheafOfModules.id_app,
    ModuleCat.id_apply] using h

private theorem finiteDirectImageIso_inv_section
    (N : Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (j + 1))))
    (V : Y.ProEtᵒᵖ) (y : N.obj.obj (op ((proEtaleBaseChange f).obj V.unop))) :
    ((lisseTowerFiniteDirectImageIso f g d j).inv.app N).val.app V
        (fsrSection g d j ((ProEtale.lowerStar _ f).obj N) V y) =
      fsrSection (f ≫ g) d j N (op ((proEtaleBaseChange f).obj V.unop)) y := by
  have : (coefficientRestriction g d j).Full :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap g d j)).fullyFaithfulROfIsIsoCounit.full
  have : (coefficientRestriction g d j).Faithful :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (lisseTowerFiniteScalarMap g d j)).fullyFaithfulROfIsIsoCounit.faithful
  unfold lisseTowerFiniteDirectImageIso
  rw [Functor.fullyFaithfulCancelRight_inv_app]
  change ((coefficientRestriction g d j).map ((coefficientRestriction g d j).preimage _)).app V
    _ = _
  rw [Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.refl_inv,
    Category.id_comp, Category.comp_id, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact chain3_eq (coefficientUnitIso_inv_fsrSection g d j ((ProEtale.lowerStar _ f).obj N) V y)
    rfl

private theorem fixedDirectImageIso_hom_section
    (N : Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)))
    (V : Y.ProEtᵒᵖ) (y : N.obj.obj (op ((proEtaleBaseChange f).obj V.unop))) :
    ((lisseTowerFixedDirectImageIso f g d j).hom.app N).val.app V
        (fixedSection g d j ((ProEtale.lowerStar _ f).obj N) V y) =
      fixedSection (f ≫ g) d j N (op ((proEtaleBaseChange f).obj V.unop)) y := by
  simp only [lisseTowerFixedDirectImageIso, lisseTowerLowerStarRestrictIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  simp only [SheafOfModules.comp_val, SheafOfModules.id_val, PresheafOfModules.comp_app,
    PresheafOfModules.id_app, ModuleCat.comp_apply]
  exact finiteDirectImageIso_inv_section f g d j ((sheafCompose (ProEt.topology W)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal j))).obj N) V
    (sheafRestrictElem _ N _ y)

private theorem fixedRealization_hom_ext
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)))
    {M : pbcModules Y (lisseTowerPulledRing d g j)}
    (φ ψ : (lisseTowerFixedSheafRealization g d j).obj P ⟶ M)
    (h : ∀ (V : Y.ProEtᵒᵖ) (y : P.obj.obj V),
      φ.val.app V (fixedSection g d j P V y) = ψ.val.app V (fixedSection g d j P V y)) :
    φ = ψ := by
  apply ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (lisseTowerFiniteScalarMap g d j)).homEquiv _ _).injective
  refine PresheafOfModules.hom_ext (fun V ↦ ?_)
  ext y
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h V y

/- The inverse-image coefficient interchange sends unit sections to unit sections. -/
private theorem normalizationPullbackIso_unit
    (n : ℕ) (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    letI := ProEt.isContinuous_overPullback f
    ((normalizationPullbackIso (ProEt.topology Y)
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology W)
        (lisseTowerEtaleQuotient d n)).hom.app P).hom.app
        (op ((proEtaleBaseChange f).obj V.unop))
      (((ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) f).unit.app
          ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj P)).hom.app V (sheafRestrictElem _ P V y)) =
      sheafRestrictElem _ _ _ (((ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).unit.app P).hom.app V y) := by
  let := ProEt.isContinuous_overPullback f
  have h := unit_mateEquiv_symm
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) f)
    (TwoSquare.mk (ProEtale.lowerStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f)
      (sheafCompose (ProEt.topology W) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (lisseTowerEtaleQuotient d n)))
      (sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (lisseTowerEtaleQuotient d n)))
      (ProEtale.lowerStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) f)
      (𝟙 _)) P
  have e := congrArg (fun φ ↦ φ.hom.app V y) h
  exact e.symm

private theorem fixedPullbackIso_inv_unit
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    ((lisseTowerFixedPullbackIso f g d j).inv.app P).val.app
        (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerStepAdjunction f g d j).unit.app
          ((lisseTowerFixedSheafRealization g d j).obj P)).val.app V
            (fixedSection g d j P V y)) =
      fixedSection (f ≫ g) d j
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f).obj P)
        (op ((proEtaleBaseChange f).obj V.unop))
        (((ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f).unit.app P).hom.app V y) := by
  have h := congrArg (fun φ ↦ φ.val.app V (fixedSection g d j P V y))
    (lisseTowerFixedPullbackIso_inv_homEquiv f g d j P)
  rw [Adjunction.homEquiv_unit] at h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  exact h.trans (chain2_eq (fixedSection_naturality g d j _ V y)
    (fixedDirectImageIso_hom_section f g d j _ V _))

/-- The composite coefficient identification is natural in the quotient map. -/
theorem lisseTowerStep_comm (n : ℕ) :
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op (n + 1)))).hom ≫
        (adicTowerInverseImage (f ≫ g)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ≫
        ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op n))).hom :=
  ((proEtaleRingInverseImageComp f g).inv.naturality
    (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).symm

/-- The restriction/pullback comparison for the step inverse image. -/
def lisseTowerStepRestriction (n : ℕ) :
    pbcRestrict ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙
        lisseTowerStepPullback f g d (n + 1) ⟶
      lisseTowerStepPullback f g d n ⋙
        pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) :=
  proEtaleRingRestrictionPullbackInv f (lisseTowerPulledRing d g (n + 1))
    (lisseTowerPulledRing d g n) (lisseTowerPulledRing d (f ≫ g) (n + 1))
    (lisseTowerPulledRing d (f ≫ g) n)
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    ((adicTowerInverseImage (f ≫ g)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op (n + 1))))
    ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op n)))
    (lisseTowerStep_comm f g d n)

/-- The step restriction/pullback comparison is invertible. -/
instance lisseTowerStepRestriction_isIso (n : ℕ) : IsIso (lisseTowerStepRestriction f g d n) :=
  proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _

private theorem scalar_lhs_inner (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    letI := ProEt.isContinuous_overPullback f
    ((lisseTowerNormalizedScalarSquare (f ≫ g) d n).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P)).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (fixedSection (f ≫ g) d (n + 1) ((sheafCompose (ProEt.topology W)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).obj
            ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (((normalizationPullbackIso (ProEt.topology Y)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology W)
          (lisseTowerEtaleQuotient d n)).hom.app P).hom.app
          (op ((proEtaleBaseChange f).obj V.unop))
          (((ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) f).unit.app
            ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P)).hom.app V (sheafRestrictElem _ P V y)))) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerFixedSheafRealization (f ≫ g) d n).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (fixedSection (f ≫ g) d n
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P)
          (op ((proEtaleBaseChange f).obj V.unop))
          (((ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).unit.app P).hom.app V y)) :=
  congr_apply_eq (normalizationPullbackIso_unit f d n P V y)
        (normalizedScalarSquare_fixedSection (f ≫ g) d n _ _ _)

private theorem scalar_lhs_section (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    letI := ProEt.isContinuous_overPullback f
    ((lisseTowerNormalizedScalarSquare (f ≫ g) d n).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P)).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (((lisseTowerFixedSheafRealization (f ≫ g) d (n + 1)).map
        ((normalizationPullbackIso (ProEt.topology Y)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology W)
          (lisseTowerEtaleQuotient d n)).hom.app P)).val.app
        (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerFixedPullbackIso f g d (n + 1)).inv.app
          ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj P)).val.app
          (op ((proEtaleBaseChange f).obj V.unop))
          (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
            ((lisseTowerFixedSheafRealization g d (n + 1)).obj
              ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
                (lisseTowerEtaleQuotient d n))).obj P))).val.app V
            (fixedSection g d (n + 1)
              ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
                (lisseTowerEtaleQuotient d n))).obj P) V (sheafRestrictElem _ P V y))))) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerFixedSheafRealization (f ≫ g) d n).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (fixedSection (f ≫ g) d n
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P)
          (op ((proEtaleBaseChange f).obj V.unop))
          (((ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).unit.app P).hom.app V y)) :=
  chain3_eq (fixedPullbackIso_inv_unit f g d (n + 1) _ V _)
    (chain2_eq (fixedSection_naturality (f ≫ g) d (n + 1) _ _ _) (scalar_lhs_inner f g d n P V y))


private theorem scalar_rhs_unit (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    ((lisseTowerStepPullback f g d (n + 1)).map
        ((lisseTowerNormalizedScalarSquare g d n).hom.app P)).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
        ((lisseTowerFixedSheafRealization g d (n + 1)).obj
          ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj P))).val.app V
        (fixedSection g d (n + 1)
          ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj P) V (sheafRestrictElem _ P V y))) =
      ((lisseTowerStepAdjunction f g d (n + 1)).unit.app
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
            ((lisseTowerFixedSheafRealization g d n).obj P))).val.app V
        (restrictElem ((adicLisseForget Y).map ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
          ((lisseTowerFixedSheafRealization g d n).obj P) V (fixedSection g d n P V y)) := by
  have hn := congrArg (fun φ ↦ φ.val.app V (fixedSection g d (n + 1)
      ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (lisseTowerEtaleQuotient d n))).obj P) V (sheafRestrictElem _ P V y)))
    ((lisseTowerStepAdjunction f g d (n + 1)).unit_naturality
      ((lisseTowerNormalizedScalarSquare g d n).hom.app P))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hn
  exact hn.trans (congrArg _ (normalizedScalarSquare_fixedSection g d n P V y))

private theorem scalar_rhs_restriction (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ)
    (z : ((lisseTowerFixedSheafRealization g d n).obj P).val.obj V) :
    ((lisseTowerStepRestriction f g d n).app
        ((lisseTowerFixedSheafRealization g d n).obj P)).val.app
        (op ((proEtaleBaseChange f).obj V.unop))
      (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
            ((lisseTowerFixedSheafRealization g d n).obj P))).val.app V
        (restrictElem ((adicLisseForget Y).map ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
          ((lisseTowerFixedSheafRealization g d n).obj P) V z)) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerStepPullback f g d n).obj ((lisseTowerFixedSheafRealization g d n).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerStepAdjunction f g d n).unit.app
          ((lisseTowerFixedSheafRealization g d n).obj P)).val.app V z) :=
  pullbackInv_unit f (lisseTowerPulledRing d g (n + 1))
      (lisseTowerPulledRing d g n) (lisseTowerPulledRing d (f ≫ g) (n + 1))
      (lisseTowerPulledRing d (f ≫ g) n)
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      ((adicTowerInverseImage (f ≫ g)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op (n + 1))))
      ((proEtaleRingInverseImageComp f g).symm.app ((pbcAdicRings X d).obj (op n)))
      (lisseTowerStep_comm f g d n) ((lisseTowerFixedSheafRealization g d n).obj P) V z

private theorem restrictScalars_map_restrictElem {C : Type*} [Category C]
    {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (φ : R ⟶ S) {M N : SheafOfModules.{u + 1} S} (x : M ⟶ N)
    (V : Cᵒᵖ) (z : M.val.obj V) :
    ((SheafOfModules.restrictScalars.{u + 1} φ).map x).val.app V (restrictElem φ M V z) =
      restrictElem φ N V (x.val.app V z) := rfl

private theorem scalar_rhs_pullback (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    ((pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
        ((lisseTowerFixedPullbackIso f g d n).inv.app P)).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerStepPullback f g d n).obj ((lisseTowerFixedSheafRealization g d n).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerStepAdjunction f g d n).unit.app
          ((lisseTowerFixedSheafRealization g d n).obj P)).val.app V
            (fixedSection g d n P V y))) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerFixedSheafRealization (f ≫ g) d n).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (fixedSection (f ≫ g) d n
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P)
          (op ((proEtaleBaseChange f).obj V.unop))
          (((ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).unit.app P).hom.app V y)) :=
  (restrictScalars_map_restrictElem _ _ _ _).trans
    (congrArg (restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerFixedSheafRealization (f ≫ g) d n).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))) (fixedPullbackIso_inv_unit f g d n P V y))

private theorem scalar_rhs_section (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (V : Y.ProEtᵒᵖ) (y : P.obj.obj V) :
    ((pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
        ((lisseTowerFixedPullbackIso f g d n).inv.app P)).val.app
      (op ((proEtaleBaseChange f).obj V.unop))
      (((lisseTowerStepRestriction f g d n).app
          ((lisseTowerFixedSheafRealization g d n).obj P)).val.app
        (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerStepPullback f g d (n + 1)).map
            ((lisseTowerNormalizedScalarSquare g d n).hom.app P)).val.app
          (op ((proEtaleBaseChange f).obj V.unop))
          (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
            ((lisseTowerFixedSheafRealization g d (n + 1)).obj
              ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
                (lisseTowerEtaleQuotient d n))).obj P))).val.app V
            (fixedSection g d (n + 1)
              ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
                (lisseTowerEtaleQuotient d n))).obj P) V (sheafRestrictElem _ P V y))))) =
      restrictElem ((adicLisseForget W).map ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
        ((lisseTowerFixedSheafRealization (f ≫ g) d n).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P))
        (op ((proEtaleBaseChange f).obj V.unop))
        (fixedSection (f ≫ g) d n
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P)
          (op ((proEtaleBaseChange f).obj V.unop))
          (((ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).unit.app P).hom.app V y)) :=
  chain3_eq (scalar_rhs_unit f g d n P V y)
    (chain2_eq (scalar_rhs_restriction f g d n P V _) (scalar_rhs_pullback f g d n P V y))

private theorem adj_ext {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B : D} (x y : L.obj A ⟶ B)
    (h : adj.unit.app A ≫ R.map x = adj.unit.app A ≫ R.map y) : x = y := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h]

private theorem scalar_ext (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    {M : pbcModules W (lisseTowerPulledRing d (f ≫ g) (n + 1))}
    (x y : (lisseTowerStepPullback f g d (n + 1)).obj
      ((lisseTowerFixedSheafRealization g d (n + 1)).obj ((sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))).obj
          P)) ⟶ M)
    (h : ∀ (V : Y.ProEtᵒᵖ) (z : P.obj.obj V),
      x.val.app (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
          ((lisseTowerFixedSheafRealization g d (n + 1)).obj
            ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P))).val.app V
          (fixedSection g d (n + 1)
            ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P) V (sheafRestrictElem _ P V z))) =
      y.val.app (op ((proEtaleBaseChange f).obj V.unop))
        (((lisseTowerStepAdjunction f g d (n + 1)).unit.app
          ((lisseTowerFixedSheafRealization g d (n + 1)).obj
            ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P))).val.app V
          (fixedSection g d (n + 1)
            ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P) V (sheafRestrictElem _ P V z)))) :
    x = y :=
  adj_ext (lisseTowerStepAdjunction f g d (n + 1)) _ _
    (fixedRealization_hom_ext g d (n + 1) _ _ _ h)

/-- The fixed pullback comparison is compatible with the normalized consecutive scalar
squares, the coefficient interchange of inverse image and the restriction/pullback mate. -/
theorem lisseTowerFixedPullbackIso_scalar (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) :
    letI := ProEt.isContinuous_overPullback f
    (lisseTowerFixedPullbackIso f g d (n + 1)).inv.app
        ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (lisseTowerEtaleQuotient d n))).obj P) ≫
      (lisseTowerFixedSheafRealization (f ≫ g) d (n + 1)).map
        ((normalizationPullbackIso (ProEt.topology Y)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology W)
          (lisseTowerEtaleQuotient d n)).hom.app P) ≫
      (lisseTowerNormalizedScalarSquare (f ≫ g) d n).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P) =
    (lisseTowerStepPullback f g d (n + 1)).map
        ((lisseTowerNormalizedScalarSquare g d n).hom.app P) ≫
      (lisseTowerStepRestriction f g d n).app ((lisseTowerFixedSheafRealization g d n).obj P) ≫
      (pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
        ((lisseTowerFixedPullbackIso f g d n).inv.app P) := by
  let := ProEt.isContinuous_overPullback f
  refine scalar_ext f g d n P _ _ (fun V y ↦ ?_)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact (scalar_lhs_section f g d n P V y).trans (scalar_rhs_section f g d n P V y).symm

/-- `lisseTowerFixedPullbackIso_scalar`, stated with the forward comparisons. -/
theorem lisseTowerFixedPullbackIso_scalar_hom (n : ℕ)
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) :
    letI := ProEt.isContinuous_overPullback f
    (lisseTowerFixedSheafRealization (f ≫ g) d (n + 1)).map
        ((normalizationPullbackIso (ProEt.topology Y)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology W)
          (lisseTowerEtaleQuotient d n)).hom.app P) ≫
      (lisseTowerNormalizedScalarSquare (f ≫ g) d n).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f).obj P) ≫
      (pbcRestrict ((adicTowerInverseImage (f ≫ g)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
        ((lisseTowerFixedPullbackIso f g d n).hom.app P) =
    (lisseTowerFixedPullbackIso f g d (n + 1)).hom.app
        ((sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (lisseTowerEtaleQuotient d n))).obj P) ≫
      (lisseTowerStepPullback f g d (n + 1)).map
        ((lisseTowerNormalizedScalarSquare g d n).hom.app P) ≫
      (lisseTowerStepRestriction f g d n).app ((lisseTowerFixedSheafRealization g d n).obj P) := by
  let := ProEt.isContinuous_overPullback f
  have h := lisseTowerFixedPullbackIso_scalar f g d n P
  rw [← cancel_epi ((lisseTowerFixedPullbackIso f g d (n + 1)).inv.app _), reassoc_of% h,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end Pullback

end AlgebraicGeometry.Scheme
