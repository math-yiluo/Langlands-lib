/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels

/-!
# Strict truncation maps between extensions from coefficient levels

Source: Zheng, Construction 4.1, p. 21, truncation inclusions in the explicit formula.
(blueprint: lem-pur-coefficient-evaluation-strict-sigma).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u v w a b
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

private def adjointLift
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) {T : D ⥤ A} {H : D ⥤ B}
    (t : T ⟶ H ⋙ R) : T ⋙ L ⟶ H where
  app X := (a.homEquiv _ _).symm (t.app X)
  naturality X Y f := by
    apply (a.homEquiv _ _).injective
    dsimp only [CategoryTheory.Functor.comp_map]
    rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact t.naturality f

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem scalarTranspose_value
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    {T : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S)}
    (a : T ⊣ restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ))
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (G : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f : T.obj F ⟶ G) (U : Cᵒᵖ) (x : F.val.obj U) :
    ((a.homEquiv F G f).val.app U) x =
      f.val.app U ((a.unit.app F).val.app U x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

omit [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem transpose_component
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    {T : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S)}
    (a : T ⊣ restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ))
    {F H : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)}
    {E G : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S)}
    (b : T.obj F ⟶ E) (f : E ⟶ G) (g : F ⟶ H)
    (t : H ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj G)
    (h : a.homEquiv F G (b ≫ f) = g ≫ t) (U : Cᵒᵖ) (x : F.val.obj U) :
    f.val.app U (b.val.app U ((a.unit.app F).val.app U x)) =
      t.val.app U (g.val.app U x) := by
  have hh := congrArg (fun k : F ⟶ (restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj G ↦
      (k.val.app U) x) h
  rw [scalarTranspose_value] at hh
  exact hh

section Generic
variable {B : ℕ → Sheaf J CommRingCat.{w}}
  {φ : ∀ {m n : ℕ} (_h : n ≤ m), B m ⟶ B n}
  {Syst : Type a} [Category.{b} Syst]
  {ev : ∀ n, Syst ⥤ ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n))}
local notation "tensor" => fun {m n : ℕ} (h : n ≤ m) ↦ siteCoefficientTensor (φ h)
local notation "tensorAdj" => fun {m n : ℕ} (h : n ≤ m) ↦ siteCoefficientTensorAdj (φ h)

private structure OrdinarySiteData
    (B : ℕ → Sheaf J CommRingCat.{w})
    (φ : ∀ {m n : ℕ} (_h : n ≤ m), B m ⟶ B n)
    (Syst : Type a) [Category.{b} Syst]
    (ev : ∀ n, Syst ⥤ ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n)))
    where
  strictTransition : ∀ {m n} (h : n ≤ m), ev m ⟶ ev n ⋙ restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (φ h))
  transition_comp : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
    (toSheaf _).map ((strictTransition (h₂.trans h₁)).app M) ≫
      (siteScalarUnderlyingIso (φ (h₂.trans h₁))).hom.app ((ev n).obj M) =
    ((toSheaf _).map ((strictTransition h₁).app M) ≫
      (siteScalarUnderlyingIso (φ h₁)).hom.app ((ev m).obj M)) ≫
    ((toSheaf _).map ((strictTransition h₂).app M) ≫
      (siteScalarUnderlyingIso (φ h₂)).hom.app ((ev n).obj M))
  extension : ∀ n, ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n)) ⥤ Syst
  adj : ∀ n, extension n ⊣ ev n
  below : ∀ {n q} (h : q ≤ n), extension n ⋙ ev q ≅ siteCoefficientTensor (φ h)
  above : ∀ n q, n < q → ∀ F, IsZero ((ev q).obj ((extension n).obj F))
  hom_formula : ∀ {n q} (h : q ≤ n) F M (f : (extension n).obj F ⟶ M),
    (siteCoefficientTensorAdj (φ h)).homEquiv F ((ev q).obj M)
      ((below h).inv.app F ≫ (ev q).map f) =
        (adj n).homEquiv F M f ≫ (strictTransition h).app M

private theorem extension_component
    (ordinary : OrdinarySiteData B φ Syst ev)
    {n q : ℕ} (h : q ≤ n)
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B n)))
    (M : Syst) (f : (ordinary.extension n).obj F ⟶ M)
    (U : Cᵒᵖ) (x : F.val.obj U) :
    ((ev q).map f).val.app U (((ordinary.below h).inv.app F).val.app U
      (((tensorAdj h).unit.app F).val.app U x)) =
    ((ordinary.strictTransition h).app M).val.app U
      (((ordinary.adj n).homEquiv F M f).val.app U x) := by
  exact transpose_component (φ h) (tensorAdj h)
    ((ordinary.below h).inv.app F) ((ev q).map f)
    ((ordinary.adj n).homEquiv F M f) ((ordinary.strictTransition h).app M)
    (ordinary.hom_formula h F M f) U x

private theorem strictSigma
    (ordinary : OrdinarySiteData B φ Syst ev)
    (assoc : ∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
      tensor h₁ ⋙ tensor h₂ ≅
        tensor (h₂.trans h₁))
    (ha : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) F,
      siteTensorUnitUnderlying (φ h₁) F ≫
        siteTensorUnitUnderlying (φ h₂) ((tensor h₁).obj F) ≫
        (toSheaf _).map ((assoc h₁ h₂).hom.app F) =
          siteTensorUnitUnderlying (φ (h₂.trans h₁)) F) :
    ∃ sigma : ∀ {m n : ℕ} (h : n ≤ m),
      tensor h ⋙ ordinary.extension n ⟶
        ordinary.extension m,
      (∀ {m n q : ℕ} (h : n ≤ m) (hq : q ≤ n) F,
        (ordinary.below hq).inv.app ((tensor h).obj F) ≫
          (ev q).map ((sigma h).app F) ≫
          (ordinary.below (hq.trans h)).hom.app F = (assoc h hq).hom.app F) ∧
      (∀ {m n q : ℕ} (h : n ≤ m) (_hq : n < q) F,
        (ev q).map ((sigma h).app F) = 0) ∧
      (∀ {m n : ℕ} (h : n ≤ m) F,
        (ordinary.adj n).homEquiv _ _ ((sigma h).app F) =
          (ordinary.below h).inv.app F) := by
  let sigma {m n : ℕ} (h : n ≤ m) := adjointLift (ordinary.adj n) (ordinary.below h).inv
  refine ⟨fun {_ _} h ↦ sigma h, ?_, ?_, ?_⟩
  · intro m n q h hq F
    apply ((tensorAdj hq).homEquiv _ _).injective
    apply ((tensorAdj h).homEquiv _ _).injective
    ext U x
    rw [scalarTranspose_value, scalarTranspose_value,
      scalarTranspose_value, scalarTranspose_value]
    let M := (ordinary.extension m).obj F
    let xh := ((tensorAdj h).unit.app F).val.app U x
    let xt := ((tensorAdj (hq.trans h)).unit.app F).val.app U x
    let z := ((ordinary.adj m).unit.app F).val.app U x
    have hs := extension_component ordinary hq ((tensor h).obj F) M
      ((sigma h).app F) U xh
    have hsig : (ordinary.adj n).homEquiv ((tensor h).obj F) M ((sigma h).app F) =
        (ordinary.below h).inv.app F := by
      change (ordinary.adj n).homEquiv _ _
        (((ordinary.adj n).homEquiv _ _).symm _) = _
      exact Equiv.apply_symm_apply _ _
    rw [hsig] at hs
    have h₁ := extension_component ordinary h F M (𝟙 M) U x
    rw [Adjunction.homEquiv_id, CategoryTheory.Functor.map_id] at h₁
    change ((ordinary.below h).inv.app F).val.app U xh =
      ((ordinary.strictTransition h).app M).val.app U z at h₁
    have h₃ := extension_component ordinary (hq.trans h) F M (𝟙 M) U x
    rw [Adjunction.homEquiv_id, CategoryTheory.Functor.map_id] at h₃
    change ((ordinary.below (hq.trans h)).inv.app F).val.app U xt =
      ((ordinary.strictTransition (hq.trans h)).app M).val.app U z at h₃
    have hc := congrArg (fun f : (toSheaf _).obj ((ev m).obj M) ⟶
        (toSheaf _).obj ((ev q).obj M) ↦ (f.hom.app U) z)
      (ordinary.transition_comp h hq M)
    change ((ordinary.strictTransition (hq.trans h)).app M).val.app U z =
      ((ordinary.strictTransition hq).app M).val.app U
        (((ordinary.strictTransition h).app M).val.app U z) at hc
    have hass := congrArg (fun f : (toSheaf _).obj F ⟶
        (toSheaf _).obj ((tensor (hq.trans h)).obj F) ↦ (f.hom.app U) x) (ha h hq F)
    change ((assoc h hq).hom.app F).val.app U
      (((tensorAdj hq).unit.app ((tensor h).obj F)).val.app U xh) = xt at hass
    calc
      _ = ((ordinary.below (hq.trans h)).hom.app F).val.app U
          (((ordinary.strictTransition hq).app M).val.app U
            (((ordinary.below h).inv.app F).val.app U xh)) :=
        congrArg (fun y : ((ev q).obj M).val.obj U ↦
          ((ordinary.below (hq.trans h)).hom.app F).val.app U y) hs
      _ = ((ordinary.below (hq.trans h)).hom.app F).val.app U
          (((ordinary.strictTransition hq).app M).val.app U
            (((ordinary.strictTransition h).app M).val.app U z)) :=
        congrArg (fun y : ((ev n).obj M).val.obj U ↦
          ((ordinary.below (hq.trans h)).hom.app F).val.app U
            (((ordinary.strictTransition hq).app M).val.app U y)) h₁
      _ = ((ordinary.below (hq.trans h)).hom.app F).val.app U
          (((ordinary.strictTransition (hq.trans h)).app M).val.app U z) :=
        congrArg (fun y : ((ev q).obj M).val.obj U ↦
          ((ordinary.below (hq.trans h)).hom.app F).val.app U y) hc.symm
      _ = ((ordinary.below (hq.trans h)).hom.app F).val.app U
          (((ordinary.below (hq.trans h)).inv.app F).val.app U xt) :=
        congrArg (fun y : ((ev q).obj M).val.obj U ↦
          ((ordinary.below (hq.trans h)).hom.app F).val.app U y) h₃.symm
      _ = xt := by
        change (((ordinary.below (hq.trans h)).inv.app F ≫
          (ordinary.below (hq.trans h)).hom.app F).val.app U) xt = xt
        rw [Iso.inv_hom_id_app]
        rfl
      _ = _ := hass.symm
  · intro m n q h hq F
    exact (ordinary.above n q hq ((tensor h).obj F)).eq_of_src _ _
  · intro m n h F
    exact Equiv.apply_symm_apply _ _

end Generic

variable {O : Type w} [CommRing O] {ell : O}

/-- Ordinary truncation inclusions are tensor associators below the smaller index and
zero above it.
Source: Zheng, Construction 4.1, printed p. 21
(blueprint: lem-pur-coefficient-evaluation-strict-sigma).
Proof: define the map by transposing the inverse below-level comparison under the
ordinary evaluation adjunction. At q below n, transpose its evaluated component twice
by the scalar adjunctions. The ordinary extension Hom formula identifies this with the
two successive transitions applied to the level-m evaluation unit. Their composition
law gives the direct transition, and the same Hom formula at q identifies it with the
single scalar-extension unit. The normalized tensor associator has exactly this value
on the two successive units; the two scalar Hom bijections are injective, so the maps
agree. Above n the evaluated source is zero, so its morphism is the zero morphism. -/
theorem coefficientEvaluationStrictSigma
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    (assoc : ∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
      coefficientTensor (J := J) (O := O) (ell := ell) h₁ ⋙
        coefficientTensor (J := J) (O := O) (ell := ell) h₂ ≅
        coefficientTensor (J := J) (O := O) (ell := ell) (h₂.trans h₁))
    (ha : CoefficientTensorAssocNormalized assoc) :
    ∃ sigma : ∀ {m n : ℕ} (h : n ≤ m),
      coefficientTensor (J := J) (O := O) (ell := ell) h ⋙ ordinary.extension n ⟶
        ordinary.extension m,
      (∀ {m n q : ℕ} (h : n ≤ m) (hq : q ≤ n) F,
        (ordinary.below hq).inv.app ((coefficientTensor (J := J) (O := O) (ell := ell) h).obj F) ≫
          (coefficientEvaluation (J := J) (O := O) (ell := ell) q).map ((sigma h).app F) ≫
          (ordinary.below (hq.trans h)).hom.app F = (assoc h hq).hom.app F) ∧
      (∀ {m n q : ℕ} (h : n ≤ m) (_hq : n < q) F,
        (coefficientEvaluation (J := J) (O := O) (ell := ell) q).map ((sigma h).app F) = 0) ∧
      (∀ {m n : ℕ} (h : n ≤ m) F,
        (ordinary.adj n).homEquiv _ _ ((sigma h).app F) =
          (ordinary.below h).inv.app F) := by
  let D : OrdinarySiteData
      (fun n ↦ coefficientQuotientSheaf (J := J) O ell n)
      (fun {_ _} h ↦ coefficientQuotientMap (J := J) O ell h)
      (CoefficientSystem (J := J) O ell)
      (coefficientEvaluation (J := J) (O := O) (ell := ell)) := {
    strictTransition := ordinary.strictTransition
    transition_comp := ordinary.transitionsNormalized.2.2
    extension := ordinary.extension
    adj := ordinary.adj
    below := ordinary.below
    above := ordinary.above
    hom_formula := ordinary.hom_formula }
  exact strictSigma D (fun {_ _ _} h₁ h₂ ↦ assoc h₁ h₂) ha

end SheafOfModules
