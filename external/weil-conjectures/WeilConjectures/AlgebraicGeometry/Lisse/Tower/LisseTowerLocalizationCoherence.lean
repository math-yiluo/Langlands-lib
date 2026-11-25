/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationTransport
public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPullbackCompositionScalar
public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentationPaste
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation

/-! # The localized inverse image through the fixed realization

The inverse image `lisseTowerLocalizationPull` along `a` followed by `b` is identified
with the ringed inverse images along `b` and `a`, compatibly with the scalar faces. The
ringed inverse images compose to the ringed inverse image along the composite,
compatibly with the restriction/pullback comparisons.

## References

* Stacks Project, Modules on Sites, Tags 03CY, 03D2, 03D3 and 03DA
* Cohomology on Sites, Tag 0D6D
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace LisseTowerLocalizationTransport

/-- Identify a functor through an equivalence with a target functor, using the counit. -/
def realizationTarget {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) [F.IsEquivalence] (K : C ⥤ E) (P : D ⥤ E) (ω : K ≅ F ⋙ P) :
    F.inv ⋙ K ≅ P :=
  Functor.isoWhiskerLeft F.inv ω ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.asEquivalence.counitIso P ≪≫ Functor.leftUnitor P

/-- The unit comparison followed by the counit comparison recovers `ω`. -/
lemma realizationLevel_hom_app_comp_realizationTarget_hom_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) [F.IsEquivalence] (K : C ⥤ E) (P : D ⥤ E) (ω : K ≅ F ⋙ P) (X : C) :
    (realizationLevel F K).hom.app X ≫ (realizationTarget F K P ω).hom.app (F.obj X) =
      ω.hom.app X := by
  have hn := ω.hom.naturality (F.asEquivalence.unit.app X)
  simp only [Functor.comp_map] at hn
  simp only [realizationLevel, realizationTarget, Iso.symm_hom, Equivalence.funInvIdAssoc_inv_app,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  erw [reassoc_of% hn]
  erw [Category.comp_id, ← P.map_comp, F.asEquivalence.functor_unit_comp X, P.map_id,
    Category.comp_id]

/-- The transported scalar face against target functors, from the scalar face before
transport. -/
lemma realizationScalar_hom_app_comp
    {C₀ C₁ D₀ D₁ E₀ E₁ B : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Category E₀] [Category E₁] [Category B]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) [F₀.IsEquivalence] [F₁.IsEquivalence]
    (K₀ : C₀ ⥤ E₀) (K₁ : C₁ ⥤ E₁) (H₀ : E₀ ⥤ B) (H₁ : E₁ ⥤ B)
    (q : C₀ ⥤ C₁) (Q : D₀ ⥤ D₁)
    (r : q ⋙ F₁ ≅ F₀ ⋙ Q) (k : q ⋙ K₁ ⋙ H₁ ≅ K₀ ⋙ H₀)
    (P₀ : D₀ ⥤ E₀) (P₁ : D₁ ⥤ E₁) (ω₀ : K₀ ≅ F₀ ⋙ P₀) (ω₁ : K₁ ≅ F₁ ⋙ P₁)
    (σ : Q ⋙ P₁ ⋙ H₁ ≅ P₀ ⋙ H₀)
    (h : ∀ X : C₀, k.hom.app X ≫ H₀.map (ω₀.hom.app X) =
      H₁.map (ω₁.hom.app (q.obj X)) ≫ H₁.map (P₁.map (r.hom.app X)) ≫
        σ.hom.app (F₀.obj X))
    (M : D₀) :
    (realizationScalar F₀ F₁ K₀ K₁ H₀ H₁ q Q r k).hom.app M ≫
        H₀.map ((realizationTarget F₀ K₀ P₀ ω₀).hom.app M) =
      H₁.map ((realizationTarget F₁ K₁ P₁ ω₁).hom.app (Q.obj M)) ≫ σ.hom.app M := by
  have key : ∀ X : C₀, (realizationScalar F₀ F₁ K₀ K₁ H₀ H₁ q Q r k).hom.app (F₀.obj X) ≫
      H₀.map ((realizationTarget F₀ K₀ P₀ ω₀).hom.app (F₀.obj X)) =
      H₁.map ((realizationTarget F₁ K₁ P₁ ω₁).hom.app (Q.obj (F₀.obj X))) ≫
        σ.hom.app (F₀.obj X) := by
    intro X
    have comm := realizationScalar_comm F₀ F₁ K₀ K₁ H₀ H₁ q Q r k (𝟙 (q.obj X))
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_map] at comm
    have hθ := (realizationTarget F₁ K₁ P₁ ω₁).hom.naturality (r.hom.app X)
    simp only [Functor.comp_map] at hθ
    apply (cancel_epi (H₁.map ((realizationLevel F₁ K₁).hom.app (q.obj X)) ≫
      H₁.map ((F₁.inv ⋙ K₁).map (r.hom.app X)))).1
    simp only [Category.assoc, Functor.comp_map]
    rw [← reassoc_of% comm, ← H₀.map_comp, realizationLevel_hom_app_comp_realizationTarget_hom_app,
      h, ← H₁.map_comp_assoc, ← H₁.map_comp_assoc, ← H₁.map_comp_assoc, Category.assoc]
    erw [hθ, reassoc_of% realizationLevel_hom_app_comp_realizationTarget_hom_app]
  have hLR : (realizationScalar F₀ F₁ K₀ K₁ H₀ H₁ q Q r k).hom ≫
      Functor.whiskerRight (realizationTarget F₀ K₀ P₀ ω₀).hom H₀ =
      Functor.whiskerLeft Q (Functor.whiskerRight (realizationTarget F₁ K₁ P₁ ω₁).hom H₁) ≫
        σ.hom :=
    ((Functor.whiskeringLeft C₀ D₀ B).obj F₀).map_injective
      (NatTrans.ext (funext fun X ↦ by simpa using key X))
  simpa using congrArg (fun τ ↦ τ.app M) hLR

/-- Paste scalar squares using the naturality of the two comparison maps. -/
private lemma scalarSquare_comp_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : E ⥤ D)
    {U V W : E} {C₀ C₁ C₂ C₃ : C} {D₀ D₁ D₂ : D}
    {p : U ⟶ V} {q : V ⟶ W}
    {x : D₀ ⟶ D₁} {y : D₁ ⟶ D₂} {z : D₂ ⟶ R.obj U}
    {r : D₀ ⟶ F.obj C₀} {k : D₁ ⟶ F.obj C₁}
    {m : C₀ ⟶ C₁} {l : C₁ ⟶ C₂} {n : C₂ ⟶ C₃} {s : C₀ ⟶ C₃}
    {i : F.obj C₂ ⟶ R.obj V} {j : F.obj C₃ ⟶ R.obj W}
    (hSa : y ≫ z ≫ R.map p = k ≫ F.map l ≫ i)
    (hSb : m ≫ l ≫ n = s)
    (hφ : x ≫ k = r ≫ F.map m)
    (hI : F.map n ≫ j = i ≫ R.map q) :
    x ≫ y ≫ z ≫ R.map (p ≫ q) = r ≫ F.map s ≫ j := by
  rw [Functor.map_comp, reassoc_of% hSa, reassoc_of% hφ, ← hI,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hSb]

end LisseTowerLocalizationTransport

open LisseTowerLocalizationTransport

namespace AlgebraicGeometry.Scheme

section Chain

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j n : ℕ)

/-- Module inverse image along `b` followed by module inverse image along `a`. -/
abbrev lisseTowerChainOrdinary :=
  lisseTowerStepPullback b t d j ⋙ lisseTowerStepPullback a (b ≫ t) d j

/-- Derived module inverse image along `b` followed by derived inverse image along `a`. -/
def lisseTowerChainPull :=
  (lisseTowerStepPullback b t d j).mapDerivedCategory ⋙
    (lisseTowerStepPullback a (b ≫ t) d j).mapDerivedCategory

/-- The presentation of the chained inverse image. -/
def lisseTowerChainPresentation :
    DerivedPresentation (lisseTowerChainPull t b a d j) (lisseTowerChainOrdinary t b a d j) :=
  (DerivedPresentation.ofMap _).comp (DerivedPresentation.ofMap _)

/-- The presentation of fixed inverse images followed by fixed realization. -/
def lisseTowerFixedChainPresentation :
    DerivedPresentation (lisseTowerLocalizationFixed (a ≫ b ≫ t) a b d j)
      (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) b ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) a ⋙
          lisseTowerFixedSheafRealization (a ≫ b ≫ t) d j) :=
  (DerivedPresentation.ofMap _).comp ((DerivedPresentation.ofMap _).comp
    (lisseTowerFixedRealizationPresentation (a ≫ b ≫ t) d j))

/-- Ordinary fixed inverse images followed by realization, as realization followed by
module inverse images. -/
def lisseTowerChainOrdinaryIso :
    ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) b ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) a ⋙
          lisseTowerFixedSheafRealization (a ≫ b ≫ t) d j ≅
      lisseTowerFixedSheafRealization t d j ⋙ lisseTowerChainOrdinary t b a d j :=
  Functor.isoWhiskerLeft _ (lisseTowerFixedPullbackIso a (b ≫ t) d j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (lisseTowerFixedPullbackIso b t d j) _ ≪≫
    Functor.associator _ _ _

/-- The derived comparison represented by `lisseTowerChainOrdinaryIso`. -/
def lisseTowerChainIso :
    lisseTowerLocalizationFixed (a ≫ b ≫ t) a b d j ≅
      lisseTowerFixedRealization t d j ⋙ lisseTowerChainPull t b a d j :=
  (lisseTowerFixedChainPresentation t b a d j).liftIso
    ((lisseTowerFixedRealizationPresentation t d j).comp (lisseTowerChainPresentation t b a d j))
    (lisseTowerChainOrdinaryIso t b a d j)

/-- The localized inverse image is the chained module inverse image. -/
def lisseTowerChainPullIso :
    lisseTowerLocalizationPull t (a ≫ b ≫ t) a b d j ≅ lisseTowerChainPull t b a d j :=
  realizationTarget _ _ _ (lisseTowerChainIso t b a d j)

/-- The ordinary composition of the three module inverse images. -/
def lisseTowerChainCompOrdinary :
    proEtaleRingModulePullback t ((pbcAdicRings X d).obj (op j)) (lisseTowerPulledRing d t j)
        (Iso.refl _) ⋙ lisseTowerChainOrdinary t b a d j ≅
      proEtaleRingModulePullback (a ≫ b ≫ t) ((pbcAdicRings X d).obj (op j))
        (lisseTowerPulledRing d (a ≫ b ≫ t) j) (Iso.refl _) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (lisseTowerPullbackComp b t d j) _ ≪≫
    lisseTowerPullbackComp a (b ≫ t) d j

/-- The derived composition of the three module inverse images. -/
def lisseTowerChainComp :
    adicTowerPullback t ((pbcAdicRings X d).obj (op j)) ⋙ lisseTowerChainPull t b a d j ≅
      adicTowerPullback (a ≫ b ≫ t) ((pbcAdicRings X d).obj (op j)) :=
  ((DerivedPresentation.ofMap _).comp (lisseTowerChainPresentation t b a d j)).liftIso
    (DerivedPresentation.ofMap _) (lisseTowerChainCompOrdinary t b a d j)

/-- The ordinary restriction/pullback comparison of the chained inverse image. -/
def lisseTowerChainRestrictionOrdinary :
    pbcRestrict ((adicTowerInverseImage t).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙
        lisseTowerChainOrdinary t b a d (n + 1) ≅
      lisseTowerChainOrdinary t b a d n ⋙
        pbcRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (lisseTowerStepRestriction b t d n)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (lisseTowerStepRestriction a (b ≫ t) d n)) ≪≫
    (Functor.associator _ _ _).symm

/-- The derived restriction/pullback comparison of the chained inverse image. -/
def lisseTowerChainRestriction :
    pbcDerivedRestrict ((adicTowerInverseImage t).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙
        lisseTowerChainPull t b a d (n + 1) ≅
      lisseTowerChainPull t b a d n ⋙
        pbcDerivedRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) :=
  ((DerivedPresentation.ofMap _).comp (lisseTowerChainPresentation t b a d (n + 1))).liftIso
    ((lisseTowerChainPresentation t b a d n).comp (DerivedPresentation.ofMap _))
    (lisseTowerChainRestrictionOrdinary t b a d n)

end Chain
section Represents

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The ordinary inverse image along `g` at a level. -/
abbrev lisseTowerBasePullback (j : ℕ) :=
  proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op j)) (lisseTowerPulledRing d g j)
    (Iso.refl _)

/-- The inverse-image coefficient mate is represented by the ordinary one. -/
theorem lisseTowerInverseImageScalar_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap (pbcRestrict (pbcAdicQuotient X d (n + 1) n
        (Nat.le_succ n)))).comp (DerivedPresentation.ofMap (lisseTowerBasePullback g d (n + 1))))
      ((DerivedPresentation.ofMap (lisseTowerBasePullback g d n)).comp
        (DerivedPresentation.ofMap (pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))))
      (lisseTowerInverseImageScalar g d n).hom (lisseTowerBaseRestriction d g n) := by
  have k := ((derivedRepresents_mapDerivedCategoryCompIso_inv
      (pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (lisseTowerBasePullback g d (n + 1))).comp
    (DerivedRepresents.inv (τ := mapDerivedCategoryNatIso (asIso
      (lisseTowerBaseRestriction d g n)).symm)
      (derivedRepresents_mapDerivedCategoryNatIso (asIso
        (lisseTowerBaseRestriction d g n)).symm))).comp
    (derivedRepresents_mapDerivedCategoryCompIso (lisseTowerBasePullback g d n)
      (pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))))
  refine k.congr ?_ ?_
  · delta lisseTowerInverseImageScalar proEtaleRingRestrictionDerivedPullback
    simp only [id, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      lisseTowerBaseRestriction_eq]
  · simp

end Represents
section Ordinary

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

/-- The ordinary composition comparison is compatible with restriction of coefficients. -/
theorem lisseTowerChainRestrictionOrdinary_comp
    (N : proEtaleRingModules X ((pbcAdicRings X d).obj (op n))) :
    (lisseTowerChainOrdinary t b a d (n + 1)).map ((lisseTowerBaseRestriction d t n).app N) ≫
        (lisseTowerChainRestrictionOrdinary t b a d n).hom.app
          ((lisseTowerBasePullback t d n).obj N) ≫
        (pbcRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
          ((lisseTowerChainCompOrdinary t b a d n).hom.app N) =
      (lisseTowerChainCompOrdinary t b a d (n + 1)).hom.app
          ((pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N) ≫
        (lisseTowerBaseRestriction d (a ≫ b ≫ t) n).app N := by
  have h₁ := lisseTowerPullbackComp_restriction b t d n N
  have h₂ := lisseTowerPullbackComp_restriction a (b ≫ t) d n N
  have hn := (lisseTowerStepRestriction a (b ≫ t) d n).naturality
    ((lisseTowerPullbackComp b t d n).hom.app N)
  simp only [lisseTowerChainRestrictionOrdinary, lisseTowerChainCompOrdinary, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, asIso_hom, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.comp_map, Functor.map_comp]
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [h₁]
  rw [Functor.map_comp, Category.assoc]
  exact congrArg _ h₂

end Ordinary
section Derived

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The derived composition of the chained inverse images is compatible with the
restriction/pullback comparisons. -/
theorem lisseTowerChainComp_restriction
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))) :
    (lisseTowerChainPull t b a d (n + 1)).map ((lisseTowerInverseImageScalar t d n).hom.app N) ≫
        (lisseTowerChainRestriction t b a d n).hom.app
          ((adicTowerPullback t ((pbcAdicRings X d).obj (op n))).obj N) ≫
        (pbcDerivedRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
          ((lisseTowerChainComp t b a d n).hom.app N) =
      (lisseTowerChainComp t b a d (n + 1)).hom.app
          ((pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N) ≫
        (lisseTowerInverseImageScalar (a ≫ b ≫ t) d n).hom.app N :=
  restriction_paste_app_eq_of_represents
    (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _)
    (lisseTowerChainPresentation t b a d n) (lisseTowerChainPresentation t b a d (n + 1))
    (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _)
    (DerivedPresentation.ofMap _)
    (α' := asIso (lisseTowerBaseRestriction d t n))
    (δ' := asIso (lisseTowerBaseRestriction d (a ≫ b ≫ t) n))
    (lisseTowerInverseImageScalar_represents t d n)
    (derivedRepresents_liftIso _ _ _) (derivedRepresents_liftIso _ _ _)
    (derivedRepresents_liftIso _ _ _)
    (lisseTowerInverseImageScalar_represents (a ≫ b ≫ t) d n)
    (fun N ↦ lisseTowerChainRestrictionOrdinary_comp t b a d n N) N

end Derived
section Scalar

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The ordinary scalar face of fixed inverse images followed by realization. -/
def lisseTowerFixedScalarOrdinary :
    sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a ⋙
          lisseTowerFixedSheafRealization (a ≫ b ≫ t) d (n + 1)) ⋙
        pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1)) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a ⋙
          lisseTowerFixedSheafRealization (a ≫ b ≫ t) d n) ⋙
        pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n) :=
  letI := ProEt.isContinuous_overPullback b
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (normalizationPullbackIso (ProEt.topology Z)
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology S)
        (lisseTowerEtaleQuotient d n)) _ ≪≫
      Functor.associator _ _ _) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (lisseTowerOrdinaryPulledScalarIso (a ≫ b ≫ t) a d n
      (lisseTowerNormalizedScalarSquare (a ≫ b ≫ t) d n)) ≪≫
    (Functor.associator _ _ _).symm

/-- The fixed scalar face is represented by the ordinary one. -/
theorem lisseTowerLocalizationFixedScalar_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp ((lisseTowerFixedChainPresentation t b a d (n + 1)).comp
        (DerivedPresentation.ofMap _)))
      ((lisseTowerFixedChainPresentation t b a d n).comp (DerivedPresentation.ofMap _))
      (lisseTowerLocalizationFixedScalar (a ≫ b ≫ t) a b d n).hom
      (lisseTowerFixedScalarOrdinary t b a d n).hom := by
  let := ProEt.isContinuous_overPullback b
  have hl := localIsomorphismProEtaleCoefficients_represents b d n
  have hp := lisseTowerPulledScalarIso_represents (a ≫ b ≫ t) a d n
  have c2 := (derivedRepresents_associator_inv _ _ _).comp ((hl.whiskerRight
    ((DerivedPresentation.ofMap
      (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a)).comp
        (lisseTowerFixedRealizationPresentation (a ≫ b ≫ t) d (n + 1)))).comp
      (derivedRepresents_associator _ _ _))
  have k := (derivedRepresents_associator_inv _ _ _).comp ((c2.whiskerRight
    (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d
      (n + 1))))).comp ((derivedRepresents_associator _ _ _).comp
    (((derivedRepresents_associator _ _ _).whiskerLeft _).comp ((hp.whiskerLeft _).comp
      (derivedRepresents_associator_inv _ _ _)))))
  refine k.congr ?_ ?_
  · refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [lisseTowerLocalizationFixedScalar, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    simp only [lisseTowerLocalizationFixed, pbcDerivedRestrict, Functor.comp_obj, Category.id_comp]
  · refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [lisseTowerFixedScalarOrdinary, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- The ordinary scalar face of the chained inverse image. -/
def lisseTowerChainScalarOrdinary :
    pbcRestrict ((adicTowerInverseImage t).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙
        lisseTowerChainOrdinary t b a d (n + 1) ⋙
          pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1)) ≅
      lisseTowerChainOrdinary t b a d n ⋙
        pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (lisseTowerChainRestrictionOrdinary t b a d n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pbcRestrictComp (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))
      ((adicTowerInverseImage (a ≫ b ≫ t)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection (a ≫ b ≫ t) d n)
      (constantAdicFiniteProjection_comp (a ≫ b ≫ t) d (n + 1) n (Nat.le_succ n)))

/-- The derived scalar face of the chained inverse image. -/
def lisseTowerChainScalar :
    pbcDerivedRestrict ((adicTowerInverseImage t).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙
        lisseTowerChainPull t b a d (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1)) ≅
      lisseTowerChainPull t b a d n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (lisseTowerChainRestriction t b a d n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pbcDerivedRestrictComp
      (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))
      ((adicTowerInverseImage (a ≫ b ≫ t)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection (a ≫ b ≫ t) d n)
      (constantAdicFiniteProjection_comp (a ≫ b ≫ t) d (n + 1) n (Nat.le_succ n)))

/-- The chained scalar face is represented by the ordinary one. -/
theorem lisseTowerChainScalar_represents :
    DerivedRepresents
      ((DerivedPresentation.ofMap _).comp ((lisseTowerChainPresentation t b a d (n + 1)).comp
        (DerivedPresentation.ofMap _)))
      ((lisseTowerChainPresentation t b a d n).comp (DerivedPresentation.ofMap _))
      (lisseTowerChainScalar t b a d n).hom (lisseTowerChainScalarOrdinary t b a d n).hom := by
  have k := (derivedRepresents_associator_inv _ _ _).comp
    (((derivedRepresents_liftIso
      ((DerivedPresentation.ofMap (pbcRestrict ((adicTowerInverseImage t).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))).comp
          (lisseTowerChainPresentation t b a d (n + 1)))
      ((lisseTowerChainPresentation t b a d n).comp (DerivedPresentation.ofMap
        (pbcRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))))
      (lisseTowerChainRestrictionOrdinary t b a d n)).whiskerRight
      (DerivedPresentation.ofMap (pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d
        (n + 1))))).comp ((derivedRepresents_associator _ _ _).comp
      ((pbcDerivedRestrictComp_represents (a ≫ b ≫ t) d n).whiskerLeft
        (lisseTowerChainPresentation t b a d n))))
  refine k.congr ?_ ?_
  · refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [lisseTowerChainScalar, lisseTowerChainRestriction, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp]
    simp only [pbcDerivedRestrict, Category.id_comp]
  · refine NatTrans.ext (funext fun X ↦ ?_)
    simp [lisseTowerChainScalarOrdinary]

/-- The two fixed pullback comparisons are compatible with the scalar squares. -/
theorem lisseTowerChainScalarOrdinary_key
    (P : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) :
    letI := ProEt.isContinuous_overPullback b
    letI := ProEt.isContinuous_overPullback a
    (lisseTowerFixedSheafRealization (a ≫ b ≫ t) d (n + 1)).map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a).map
          ((normalizationPullbackIso (ProEt.topology Z)
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology S)
            (lisseTowerEtaleQuotient d n)).hom.app P)) ≫
      (lisseTowerFixedSheafRealization (a ≫ b ≫ t) d (n + 1)).map
        ((normalizationPullbackIso (ProEt.topology S)
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a) (ProEt.topology T)
          (lisseTowerEtaleQuotient d n)).hom.app
            ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).obj P)) ≫
      (lisseTowerNormalizedScalarSquare (a ≫ b ≫ t) d n).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) a).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).obj P)) ≫
      (pbcRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
        ((lisseTowerFixedPullbackIso a (b ≫ t) d n).hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).obj P) ≫
          (lisseTowerStepPullback a (b ≫ t) d n).map
            ((lisseTowerFixedPullbackIso b t d n).hom.app P)) =
    (lisseTowerFixedPullbackIso a (b ≫ t) d (n + 1)).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).obj
          ((sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj P)) ≫
      (lisseTowerStepPullback a (b ≫ t) d (n + 1)).map
        ((lisseTowerFixedPullbackIso b t d (n + 1)).hom.app
          ((sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj P) ≫
          (lisseTowerStepPullback b t d (n + 1)).map
            ((lisseTowerNormalizedScalarSquare t d n).hom.app P) ≫
          (lisseTowerStepRestriction b t d n).app ((lisseTowerFixedSheafRealization t d n).obj P)) ≫
      (lisseTowerStepRestriction a (b ≫ t) d n).app
        ((lisseTowerStepPullback b t d n).obj ((lisseTowerFixedSheafRealization t d n).obj P)) := by
  let := ProEt.isContinuous_overPullback b
  let := ProEt.isContinuous_overPullback a
  have hSa := lisseTowerFixedPullbackIso_scalar_hom a (b ≫ t) d n
    ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).obj P)
  have hSb := lisseTowerFixedPullbackIso_scalar_hom b t d n P
  have hφ : (lisseTowerFixedSheafRealization (a ≫ b ≫ t) d (n + 1)).map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) a).map
          ((normalizationPullbackIso (ProEt.topology Z)
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology S)
            (lisseTowerEtaleQuotient d n)).hom.app P)) ≫
        (lisseTowerFixedPullbackIso a (b ≫ t) d (n + 1)).hom.app
          ((sheafCompose (ProEt.topology S) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (lisseTowerEtaleQuotient d n))).obj
              ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).obj P)) =
      (lisseTowerFixedPullbackIso a (b ≫ t) d (n + 1)).hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).obj
            ((sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P)) ≫
        (lisseTowerStepPullback a (b ≫ t) d (n + 1)).map
          ((lisseTowerFixedSheafRealization (b ≫ t) d (n + 1)).map
            ((normalizationPullbackIso (ProEt.topology Z)
              (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b) (ProEt.topology S)
              (lisseTowerEtaleQuotient d n)).hom.app P)) :=
    (lisseTowerFixedPullbackIso a (b ≫ t) d (n + 1)).hom.naturality _
  have hI : (lisseTowerStepPullback a (b ≫ t) d (n + 1)).map
        ((pbcRestrict ((adicTowerInverseImage (b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
            ((lisseTowerFixedPullbackIso b t d n).hom.app P)) ≫
        (lisseTowerStepRestriction a (b ≫ t) d n).app
          ((lisseTowerStepPullback b t d n).obj ((lisseTowerFixedSheafRealization t d n).obj P)) =
      (lisseTowerStepRestriction a (b ≫ t) d n).app
          ((lisseTowerFixedSheafRealization (b ≫ t) d n).obj
            ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).obj P)) ≫
        (pbcRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map
          ((lisseTowerStepPullback a (b ≫ t) d n).map
            ((lisseTowerFixedPullbackIso b t d n).hom.app P)) :=
    (lisseTowerStepRestriction a (b ≫ t) d n).naturality _
  exact scalarSquare_comp_map (lisseTowerStepPullback a (b ≫ t) d (n + 1))
    (pbcRestrict ((adicTowerInverseImage (a ≫ b ≫ t)).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))) hSa hSb hφ hI

/-- The ordinary scalar faces are compatible with the chained comparison. -/
theorem lisseTowerChainScalarOrdinary_comp
    (P : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) :
    (lisseTowerFixedScalarOrdinary t b a d n).hom.app P ≫
        (pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n)).map
          ((lisseTowerChainOrdinaryIso t b a d n).hom.app P) =
      (pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
          ((lisseTowerChainOrdinaryIso t b a d (n + 1)).hom.app
            ((sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
              (lisseTowerEtaleQuotient d n))).obj P)) ≫
        (pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
          ((lisseTowerChainOrdinary t b a d (n + 1)).map
            ((lisseTowerNormalizedScalarSquare t d n).hom.app P)) ≫
        (lisseTowerChainScalarOrdinary t b a d n).hom.app
          ((lisseTowerFixedSheafRealization t d n).obj P) := by
  simp only [lisseTowerFixedScalarOrdinary, lisseTowerOrdinaryPulledScalarIso,
    lisseTowerChainOrdinaryIso, lisseTowerChainScalarOrdinary,
    lisseTowerChainRestrictionOrdinary, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app, asIso_hom,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.comp_map, Functor.map_comp]
  simp only [ProEtale.upperStar, Functor.comp_obj, Category.id_comp]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality]
  have h := congrArg (fun x ↦ x ≫ (pbcRestrictComp
      (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))
      ((adicTowerInverseImage (a ≫ b ≫ t)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection (a ≫ b ≫ t) d n)
      (constantAdicFiniteProjection_comp (a ≫ b ≫ t) d (n + 1) n (Nat.le_succ n))).hom.app _)
    (congrArg (pbcRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
      (lisseTowerChainScalarOrdinary_key t b a d n P))
  simp only [ProEtale.upperStar, Functor.map_comp, Category.assoc] at h
  exact h

/-- The chained comparison is compatible with the scalar faces. -/
theorem lisseTowerChainIso_scalar
    (C : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))) :
    (lisseTowerLocalizationFixedScalar (a ≫ b ≫ t) a b d n).hom.app C ≫
        (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n)).map
          ((lisseTowerChainIso t b a d n).hom.app C) =
      (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
          ((lisseTowerChainIso t b a d (n + 1)).hom.app
            ((normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n)).obj C)) ≫
        (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
          ((lisseTowerChainPull t b a d (n + 1)).map
            ((lisseTowerFixedScalarIso t d n (lisseTowerNormalizedScalarSquare t d n)).hom.app C)) ≫
        (lisseTowerChainScalar t b a d n).hom.app ((lisseTowerFixedRealization t d n).obj C) :=
  scalar_paste_app_eq_of_represents (DerivedPresentation.ofMap _)
    (lisseTowerFixedChainPresentation t b a d n) (lisseTowerFixedChainPresentation t b a d (n + 1))
    (DerivedPresentation.ofMap _) (DerivedPresentation.ofMap _)
    (lisseTowerFixedRealizationPresentation t d n)
    (lisseTowerFixedRealizationPresentation t d (n + 1))
    (lisseTowerChainPresentation t b a d n) (lisseTowerChainPresentation t b a d (n + 1))
    (DerivedPresentation.ofMap _)
    (lisseTowerLocalizationFixedScalar_represents t b a d n)
    (derivedRepresents_liftIso _ _ _) (derivedRepresents_liftIso _ _ _)
    (lisseTowerFixedScalarIso_represents t d n (lisseTowerNormalizedScalarSquare t d n))
    (lisseTowerChainScalar_represents t b a d n)
    (fun P ↦ lisseTowerChainScalarOrdinary_comp t b a d n P) C

/-- The localized inverse image is compatible with the scalar faces. -/
theorem lisseTowerChainPullIso_scalar
    (M : DerivedCategory (pbcModules Z ((adicTowerInverseImage t).obj
      ((pbcAdicRings X d).obj (op n))))) :
    (lisseTowerLocalizationScalar t (a ≫ b ≫ t) a b d n).hom.app M ≫
        (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n)).map
          ((lisseTowerChainPullIso t b a d n).hom.app M) =
      (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
          ((lisseTowerChainPullIso t b a d (n + 1)).hom.app
            ((pbcDerivedRestrict ((adicTowerInverseImage t).map
              (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj M)) ≫
        (lisseTowerChainScalar t b a d n).hom.app M :=
  realizationScalar_hom_app_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun C ↦ lisseTowerChainIso_scalar t b a d n C) M

/-- The level comparison: realized fixed inverse image after ringed inverse image along `t`,
identified with ringed inverse image along the composite. -/
def lisseTowerChainLevel (j : ℕ) :
    adicTowerPullback t ((pbcAdicRings X d).obj (op j)) ⋙
        lisseTowerLocalizationPull t (a ≫ b ≫ t) a b d j ≅
      adicTowerPullback (a ≫ b ≫ t) ((pbcAdicRings X d).obj (op j)) :=
  Functor.isoWhiskerLeft _ (lisseTowerChainPullIso t b a d j) ≪≫ lisseTowerChainComp t b a d j

/-- The coefficient component of the composition comparison. -/
theorem lisseTowerChainLevel_scalar
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))) :
    (lisseTowerLocalizationPull t (a ≫ b ≫ t) a b d (n + 1) ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
        ((lisseTowerInverseImageScalar t d n).hom.app N) ≫
      (lisseTowerLocalizationScalar t (a ≫ b ≫ t) a b d n).hom.app
        ((adicTowerPullback t ((pbcAdicRings X d).obj (op n))).obj N) ≫
      (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d n)).map
        ((lisseTowerChainLevel t b a d n).hom.app N) =
    (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
        ((lisseTowerChainLevel t b a d (n + 1)).hom.app
          ((pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)) ≫
      (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map
        ((lisseTowerInverseImageScalar (a ≫ b ≫ t) d n).hom.app N) ≫
      (pbcDerivedRestrictComp (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))
        ((adicTowerInverseImage (a ≫ b ≫ t)).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
        (constantAdicFiniteProjection (a ≫ b ≫ t) d n)
        (constantAdicFiniteProjection_comp (a ≫ b ≫ t) d (n + 1) n (Nat.le_succ n))).hom.app
          ((adicTowerPullback (a ≫ b ≫ t) ((pbcAdicRings X d).obj (op n))).obj N) := by
  have hA := lisseTowerChainPullIso_scalar t b a d n
    ((adicTowerPullback t ((pbcAdicRings X d).obj (op n))).obj N)
  have hB := lisseTowerChainComp_restriction t b a d n N
  have hθ := (lisseTowerChainPullIso t b a d (n + 1)).hom.naturality
    ((lisseTowerInverseImageScalar t d n).hom.app N)
  have hk := (pbcDerivedRestrictComp (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))
    ((adicTowerInverseImage (a ≫ b ≫ t)).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (constantAdicFiniteProjection (a ≫ b ≫ t) d n)
    (constantAdicFiniteProjection_comp (a ≫ b ≫ t) d (n + 1) n (Nat.le_succ n))).hom.naturality
      ((lisseTowerChainComp t b a d n).hom.app N)
  simp only [lisseTowerChainLevel, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.comp_map, CategoryTheory.Functor.map_comp,
    Category.assoc, Functor.comp_obj] at hθ hk ⊢
  rw [reassoc_of% hA, ← Functor.map_comp_assoc, hθ, CategoryTheory.Functor.map_comp,
    Category.assoc]
  simp only [lisseTowerChainScalar, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  rw [← hk]
  have hB' := congrArg
    (pbcDerivedRestrict (constantAdicFiniteProjection (a ≫ b ≫ t) d (n + 1))).map hB
  simp only [CategoryTheory.Functor.map_comp] at hB'
  rw [reassoc_of% hB']

end Scalar

end AlgebraicGeometry.Scheme
