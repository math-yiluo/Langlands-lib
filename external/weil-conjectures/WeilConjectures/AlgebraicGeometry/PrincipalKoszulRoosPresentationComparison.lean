/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.StrictRoosModel
import WeilConjectures.AlgebraicGeometry.PrincipalKoszulDualTowerComparison
import all WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison

/-! # Normalized principal Koszul Roos presentation comparison

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E;
sites-cohomology.tex, Tag 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})

-- Choose the standard degreewise product directly, avoiding recursive limit search.
local instance (priority := 1100)
    (H : ℕ → CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete ℕ)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).has_limit
        (Discrete.functor H)

/-- The zero-coordinate Roos lift of a strict augmentation of a tower of complexes.
This factors the construction through abstract tower data to avoid unfolding a concrete
Koszul tensor tower while checking its compatibility proof.
Source: Stacks Tag 0941
(auxiliary; not a blueprint node). -/
def principalTowerRoosUnit
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    P ⟶ roosF.obj (koszulTowerComplex R T) :=
  roosAugment (X := koszulTowerComplex R T) (fun n ↦ γ.app (op n))
    (fun n ↦ (γ.naturality (homOfLE (Nat.le_succ n)).op).symm.trans
      (Category.id_comp _))

/-- The strict degree-zero unit into the principal Koszul Roos complex.
Source: Stacks Tags 0A0E and 0941
(auxiliary; not a blueprint node). -/
def principalKoszulRoosUnit
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) :
    P ⟶ roosF.obj (koszulTowerComplex R (koszulTensorTower R P a)) :=
  principalTowerRoosUnit R P (koszulTensorTower R P a) (koszulStrictAugmentation R P a)

private theorem augment_limit_transport
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (f : X ⟶ Y)
    (δ : P ⟶ ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj Y)
    (hδ : ∀ (q : ℤ) (m : ℕᵒᵖ),
      δ.f q ≫ limit.π (Y.X q) m = (γ m.unop).f q ≫ (f.f q).app m) :
    roosAugmentLimit γ hγ ≫ roosLimitFunctor.map f ≫
        (strictTowerLimitIso (A := A)).hom.app Y = δ := by
  dsimp only [roosLimitFunctor, Functor.comp_map]
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro m
  have hπ := limit.isoLimitCone_hom_π
    ⟨HomologicalComplex.coneOfHasLimitEval Y.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor⟩ m
  have hlim := limMap_π
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) m
  have hαπ := roosAugmentLimit_π (X := X) γ hγ m.unop
  have hc : roosAugmentLimit γ hγ ≫ roosLimitFunctor.map f ≫
      limit.π Y.asFunctor m = γ m.unop ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app m := by
    change roosAugmentLimit γ hγ ≫
      limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) ≫ _ = _
    dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex] at hlim ⊢
    erw [hlim, ← Category.assoc, hαπ]
  have hp := congrArg (fun g ↦ g.f q) hπ
  change ((strictTowerLimitIso (A := A)).hom.app Y).f q ≫
      limit.π (Y.X q) m = (limit.π Y.asFunctor m).f q at hp
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [hp]
  have hcq := congrArg (fun g ↦ g.f q) hc
  dsimp only [roosLimitFunctor, Functor.comp_map] at hcq
  simp only [HomologicalComplex.comp_f] at hcq
  exact hcq.trans (hδ q m).symm

private theorem augment_roos_transport
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (f : X ⟶ Y) :
    roosAugment γ hγ ≫ roosF.map f =
      roosAugmentLimit γ hγ ≫ roosLimitFunctor.map f ≫ roosι Y := by
  rw [roosAugment_eq, Category.assoc, ← roosι_natural]
  rfl

private theorem normalized_roos_comparison
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (CF RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (κ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    [CF.IsRightDerivedFunctor (roosDerivedUnit κ)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))]
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))]
    (T : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.map (roosι T) ≫ κ.hom.app T ≫
      (CF.rightDerivedUnique RF (roosDerivedUnit κ) η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))).hom.app
          (DerivedCategory.Q.obj T) = η.app T := by
  have h := CF.rightDerivedNatTrans_app RF (roosDerivedUnit κ)
    η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (𝟙 _) T
  simpa only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, roosDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    roosInclusion, NatTrans.id_app, Category.id_comp, Category.assoc] using h

private theorem normalized_augmentation_transport
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (CF RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (κ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    [CF.IsRightDerivedFunctor (roosDerivedUnit κ)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))]
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))]
    {P : CochainComplex A ℤ} {X T : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (s : X ≅ T) (α : P ⟶ roosLimitFunctor.obj X) (u : P ⟶ roosF.obj X)
    (haug : u ≫ roosF.map s.hom = α ≫ roosLimitFunctor.map s.hom ≫ roosι T)
    {Z : DerivedCategory.{w} A} (τ : RF.obj (DerivedCategory.Q.{w}.obj T) ≅ Z) :
    DerivedCategory.Q.{w}.map u ≫ DerivedCategory.Q.{w}.map (roosF.map s.hom) ≫
      κ.hom.app T ≫ (CF.rightDerivedUnique RF (roosDerivedUnit κ) η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))).hom.app
          (DerivedCategory.Q.{w}.obj T) ≫ τ.hom =
      DerivedCategory.Q.{w}.map α ≫ DerivedCategory.Q.{w}.map (roosLimitFunctor.map s.hom) ≫
        η.app T ≫ τ.hom := by
  rw [← Category.assoc (DerivedCategory.Q.{w}.map u)
    (DerivedCategory.Q.{w}.map (roosF.map s.hom)), ← Functor.map_comp, haug]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% normalized_roos_comparison CF RF κ η T]

-- The unit calculation compares several large, definitionally equal tower presentations.
/-- The negative principal cone and the dual singleton Koszul system give the same
normalized strict derived completion, for every presentation of the latter.

Source: Stacks Project, algebraization.tex, proof of Tag 0A0E;
sites-cohomology.tex, Tag 0941
(auxiliary; not a blueprint node).

Proof: evaluate the dual positive two-term Koszul complex at one in each of its two
nonzero degrees. The signed Hom differential identifies it with the negative cone of
multiplication by a^(n+1). The inverse dual transitions have components (a,1), and the
dual projection is the degree-zero cone inclusion. Tensor symmetry therefore gives an
augmentation-compatible strict tower isomorphism. The normalized strict Roos comparison
identifies its cone with total derived inverse limit. The uniqueness of the right-derived
functor compares that inverse limit with D.inverseLimit, respecting the comparison units;
D.tensorFactors identifies the descended tower on the representative P. Naturality at the
specified localization representative gives D.unit at Q(P), hence the displayed equality.
Finite free Koszul factors preserve quasi-isomorphisms, so P need not be K-flat. Zero
complexes, a zero section, and an invertible section obey the same chain calculations.
-/
theorem principalKoszulRoos_presentation_comparison
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (D : RingedKoszulLimitPresentation R 1 (fun _ ↦ ⟨a.val, a.property⟩)) :
    ∃ e : DerivedCategory.Q.{w}.obj
        (roosF.obj (koszulTowerComplex R (koszulTensorTower R P a))) ≅
          D.completion.obj (DerivedCategory.Q.{w}.obj P),
      DerivedCategory.Q.{w}.map (principalKoszulRoosUnit R P a) ≫ e.hom =
        D.unit (DerivedCategory.Q.{w}.obj P) := by
  classical
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let b : Fin 1 → (R.obj ⋙ forget CommRingCat).sections := fun _ ↦ ⟨a.val, a.property⟩
  let X := koszulTowerComplex R (koszulTensorTower R P a)
  let T := ringedKoszulTensorTowerComplex R 1 b P
  obtain ⟨s, hs⟩ := principalKoszul_dual_tower_comparison R a P
  let α : P ⟶ limit X.asFunctor := roosAugmentLimit (X := X)
    (fun n ↦ (koszulStrictAugmentation R P a).app (op n))
    (fun n ↦ ((koszulStrictAugmentation R P a).naturality
      (homOfLE (Nat.le_succ n)).op).symm.trans (Category.id_comp _))
  let l := strictTowerLimitIso (A := A)
  have hα : α ≫ roosLimitFunctor.map s.hom ≫ l.hom.app T =
      ringedKoszulLimitUnit R 1 b P := by
    apply augment_limit_transport (X := X)
    intro q m
    change limit.lift _ (ringedKoszulTensorUnitCone R 1 b P q) ≫
        limit.π (T.X q) m = _
    rw [limit.lift_π]
    exact (hs m.unop q).symm
  have haug : principalKoszulRoosUnit R P a ≫ roosF.map s.hom =
      α ≫ roosLimitFunctor.map s.hom ≫ roosι T :=
    by
      dsimp only [principalKoszulRoosUnit, principalTowerRoosUnit]
      exact augment_roos_transport (X := X) (Y := T) _ _ s.hom
  obtain ⟨RF, κ, hRF, _⟩ := strictRoosDerivation.{u, u, u, w} J
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (fun U x y ↦ @mul_comm (R.obj.obj U) inferInstance x y)
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  let lQ := Functor.isoWhiskerRight l DerivedCategory.Q
  let η := lQ.hom ≫ D.comparison
  have hη : D.inverseLimit.IsRightDerivedFunctor η W := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    have := D.isRightDerived
    have h' := Functor.IsRightDerivedFunctor.isLeftKanExtension
      D.inverseLimit D.comparison W
    exact (Functor.isLeftKanExtension_iff_of_iso₂ η D.comparison lQ
      (Iso.refl _) (by simp [η])).mpr h'
  let := hRF
  let := hη
  let ρ := RF.rightDerivedUnique D.inverseLimit (roosDerivedUnit κ) η W
  let e := DerivedCategory.Q.mapIso (roosF.mapIso s) ≪≫ κ.app T ≪≫
    ρ.app (DerivedCategory.Q.obj T) ≪≫ D.inverseLimit.mapIso (D.tensorFactors.app P).symm
  refine ⟨e, ?_⟩
  rw [FlatScalarKoszul.unit_app_Q R D P]
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  erw [normalized_augmentation_transport RF D.inverseLimit κ η
    (X := X) (T := T) s α
    (principalKoszulRoosUnit R P a) haug
    (D.inverseLimit.mapIso (D.tensorFactors.app P).symm)]
  dsimp only [η, NatTrans.comp_app, lQ, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  have hαQ := congrArg (fun f ↦ DerivedCategory.Q.{w}.map f) hα
  simp only [Functor.map_comp] at hαQ
  simpa only [RingedKoszulLimitPresentation.unitOnComplex, Category.assoc,
    Functor.mapIso_hom, Iso.symm_hom] using
    congrArg (fun f ↦ f ≫ D.comparison.app T ≫
      D.inverseLimit.map (D.tensorFactors.app P).inv) hαQ

end CategoryTheory
