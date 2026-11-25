/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryClopenEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowEvaluation

/-!
# Proper/open projection and pasting for varying coefficient rings

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D, open-immersion cases; the
agent-formulated varying-ring extension extracted from the blueprint's local-pairs
construction (blueprint: lem-sp-varying-ring-proper-open-pasting).

Every map below lives on the ordinary derived category of strict semilinear systems.
The ordinary system maps and their two pasting equations are stated separately, so
these equalities precede evaluation. No invertibility of gamma on arbitrary inputs
is asserted.

## Main statements

- `modulePi_components`: identity on the image and zero on the complement.
- `moduleAlpha_vertical`, `moduleAlpha_horizontal`: intrinsic system pasting.
- `alpha_vertical`, `alpha_horizontal`, `properOpenPasting`: derived pasting laws.
- `alpha_identities`, `gamma_identities`, `gamma_evaluation`: normalization and evaluation.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u k
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

private theorem mate_whisker
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : G ⋙ L₂ ⟶ L₁ ⋙ H) (t : G' ⟶ G) (b : H ⟶ H') :
    mateEquiv adj₁ adj₂
        (Functor.whiskerRight t L₂ ≫ a ≫ Functor.whiskerLeft L₁ b) =
      Functor.whiskerLeft R₁ t ≫ mateEquiv adj₁ adj₂ a ≫
        Functor.whiskerRight b R₂ := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  dsimp [mateEquiv]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have ht := adj₂.unit.naturality (t.app (R₁.obj X))
  dsimp at ht
  rw [← reassoc_of% ht]
  slice_lhs 4 5 => rw [← R₂.map_comp, ← b.naturality, R₂.map_comp]

section DerivedMaps

variable {A₀ B₁ B₂ C₀ : Type*}
  [Category A₀] [Category B₁] [Category B₂] [Category C₀]
  [Abelian A₀] [Abelian B₁] [Abelian B₂] [Abelian C₀]
  [HasDerivedCategory A₀] [HasDerivedCategory B₁]
  [HasDerivedCategory B₂] [HasDerivedCategory C₀]
  (F₁ : A₀ ⥤ B₁) (F₂ : B₁ ⥤ C₀) (G₁ : A₀ ⥤ B₂) (G₂ : B₂ ⥤ C₀)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

private def derivedSquare (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F₁ F₂).hom ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso A₀ (.up ℤ)) _ _
      (F₁ ⋙ F₂).mapDerivedCategory (G₁ ⋙ G₂).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso G₁ G₂).inv

set_option backward.isDefEq.respectTransparency false in
private theorem derivedSquare_fac (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    (K : CochainComplex A₀ ℤ) :
    (derivedSquare F₁ F₂ G₁ G₂ t).app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ K
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ K
  dsimp only [derivedSquare, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, hG, Localization.liftNatTrans_app]
  change _ ≫ (_ ≫ _ ≫ (G₁ ⋙ G₂).mapDerivedCategoryFactors.inv.app K) ≫
      (G₁ ⋙ G₂).mapDerivedCategoryFactors.hom.app K = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change (Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app (DerivedCategory.Q.obj K) ≫
    (F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) = _
  rw [← hF]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

variable (F₀ : A₀ ⥤ C₀) [F₀.Additive]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]

private theorem derivedTriangle_fac (e : F₀ ≅ F₁ ⋙ F₂) (K : CochainComplex A₀ ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F₁ F₂).symm).hom.app (DerivedCategory.Q.obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

private theorem derivedComp_fac (e : F₁ ⋙ F₂ ≅ F₀) (K : CochainComplex A₀ ℤ) :
    (Functor.mapDerivedCategoryCompIso F₁ F₂ ≪≫
        Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) ≫
        F₀.mapDerivedCategoryFactors.hom.app K =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ K]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end DerivedMaps

section PastingTransparency
attribute [local irreducible] derivedSquare
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategory DerivedCategory.Q

section DerivedPasting

variable {A₀ : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory A₀]
variable {B₀ : Type*} [Category B₀] [Abelian B₀] [HasDerivedCategory B₀]
variable {C₀ : Type*} [Category C₀] [Abelian C₀] [HasDerivedCategory C₀]
variable {D₀ : Type*} [Category D₀] [Abelian D₀] [HasDerivedCategory D₀]
variable {E₀ : Type*} [Category E₀] [Abelian E₀] [HasDerivedCategory E₀]
variable {F₀ : Type*} [Category F₀] [Abelian F₀] [HasDerivedCategory F₀]
variable (J₀ : A₀ ⥤ B₀) (J₁ : C₀ ⥤ D₀) (J₂ : E₀ ⥤ F₀)
  (P₁ : D₀ ⥤ B₀) (P₂ : F₀ ⥤ D₀) (R₁ : C₀ ⥤ A₀) (R₂ : E₀ ⥤ C₀)
  (P : F₀ ⥤ B₀) (R : E₀ ⥤ A₀)
variable [J₀.Additive] [PreservesFiniteLimits J₀] [PreservesFiniteColimits J₀]
variable [J₁.Additive] [PreservesFiniteLimits J₁] [PreservesFiniteColimits J₁]
variable [J₂.Additive] [PreservesFiniteLimits J₂] [PreservesFiniteColimits J₂]
variable [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
variable [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
variable [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
variable [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
variable [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem derivedSquare_vertical
    (ep : P ≅ P₂ ⋙ P₁) (er : R ≅ R₂ ⋙ R₁)
    (t₁ : J₁ ⋙ P₁ ⟶ R₁ ⋙ J₀) (t₂ : J₂ ⋙ P₂ ⟶ R₂ ⋙ J₁)
    (t : J₂ ⋙ P ⟶ R ⋙ J₀)
    (ht : ∀ X, ep.hom.app (J₂.obj X) ≫ P₁.map (t₂.app X) ≫ t₁.app (R₂.obj X) =
      t.app X ≫ J₀.map (er.hom.app X)) (N : DerivedCategory E₀) :
    (Functor.mapDerivedCategoryNatIso ep ≪≫
        (Functor.mapDerivedCategoryCompIso P₂ P₁).symm).hom.app (J₂.mapDerivedCategory.obj N) ≫
        P₁.mapDerivedCategory.map ((derivedSquare J₂ P₂ R₂ J₁ t₂).app N) ≫
        (derivedSquare J₁ P₁ R₁ J₀ t₁).app (R₂.mapDerivedCategory.obj N) =
      (derivedSquare J₂ P R J₀ t).app N ≫ J₀.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso er ≪≫
          (Functor.mapDerivedCategoryCompIso R₂ R₁).symm).hom.app N) := by
  let ep' := Functor.mapDerivedCategoryNatIso ep ≪≫
    (Functor.mapDerivedCategoryCompIso P₂ P₁).symm
  let er' := Functor.mapDerivedCategoryNatIso er ≪≫
    (Functor.mapDerivedCategoryCompIso R₂ R₁).symm
  let a₁ := derivedSquare J₁ P₁ R₁ J₀ t₁
  let a₂ := derivedSquare J₂ P₂ R₂ J₁ t₂
  let a := derivedSquare J₂ P R J₀ t
  let L : J₂.mapDerivedCategory ⋙ P.mapDerivedCategory ⟶
      R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory ⋙ J₀.mapDerivedCategory :=
    Functor.whiskerLeft J₂.mapDerivedCategory ep'.hom ≫
      Functor.whiskerRight a₂ P₁.mapDerivedCategory ≫
      Functor.whiskerLeft R₂.mapDerivedCategory a₁
  let H : J₂.mapDerivedCategory ⋙ P.mapDerivedCategory ⟶
      R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory ⋙ J₀.mapDerivedCategory :=
    a ≫ Functor.whiskerRight er'.hom J₀.mapDerivedCategory
  suffices he : L = H from congr_app he N
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso E₀ (.up ℤ)) (fun K ↦ ?_)
  dsimp only [L, H, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  let K₂ := (R₂.mapHomologicalComplex (.up ℤ)).obj K
  let K₁ := (R₁.mapHomologicalComplex (.up ℤ)).obj K₂
  rw [← cancel_mono (J₀.mapDerivedCategory.map
    (R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactors.hom.app K)) ≫
    J₀.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.hom.app K₂) ≫
    J₀.mapDerivedCategoryFactors.hom.app K₁)]
  simp only [Category.assoc]
  have n₁ := a₁.naturality (R₂.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at n₁
  rw [← reassoc_of% n₁, derivedSquare_fac J₁ P₁ R₁ J₀ t₁ K₂]
  have h₂fac := congrArg P₁.mapDerivedCategory.map (derivedSquare_fac J₂ P₂ R₂ J₁ t₂ K)
  simp only [Functor.map_comp] at h₂fac
  rw [reassoc_of% h₂fac]
  have n₂ := P₁.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at n₂
  change P₁.mapDerivedCategory.map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K)) ≫
      P₁.mapDerivedCategoryFactors.hom.app ((J₁.mapHomologicalComplex (.up ℤ)).obj K₂) =
    P₁.mapDerivedCategoryFactors.hom.app
      ((P₂.mapHomologicalComplex (.up ℤ)).obj ((J₂.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((P₁.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K)) at n₂
  rw [reassoc_of% n₂]
  have n₃ := ep'.hom.naturality (J₂.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at n₃
  rw [← reassoc_of% n₃, reassoc_of% (derivedTriangle_fac P₂ P₁ P ep _)]
  have hr' := congrArg J₀.mapDerivedCategory.map (derivedTriangle_fac R₂ R₁ R er K)
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have n₄ := J₀.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at n₄
  change J₀.mapDerivedCategory.map (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K)) ≫
      J₀.mapDerivedCategoryFactors.hom.app K₁ =
    J₀.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((J₀.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K)) at n₄
  rw [n₄, reassoc_of% (derivedSquare_fac J₂ P R J₀ t K)]
  simp only [← DerivedCategory.Q.map_comp]
  have hc : (NatTrans.mapHomologicalComplex ep.hom (.up ℤ)).app
        ((J₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (P₁.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app K₂ =
    (NatTrans.mapHomologicalComplex t (.up ℤ)).app K ≫
      (J₀.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K) := by
    ext n
    change ep.hom.app (J₂.obj (K.X n)) ≫ P₁.map (t₂.app (K.X n)) ≫
      t₁.app (R₂.obj (K.X n)) = t.app (K.X n) ≫ J₀.map (er.hom.app (K.X n))
    exact ht (K.X n)
  exact congrArg (fun f ↦ P.mapDerivedCategory.map (J₂.mapDerivedCategoryFactors.hom.app K) ≫
    P.mapDerivedCategoryFactors.hom.app ((J₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map f) hc

end DerivedPasting

section DerivedHorizontal

variable {A₀ : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory A₀]
variable {B₀ : Type*} [Category B₀] [Abelian B₀] [HasDerivedCategory B₀]
variable {C₀ : Type*} [Category C₀] [Abelian C₀] [HasDerivedCategory C₀]
variable {D₀ : Type*} [Category D₀] [Abelian D₀] [HasDerivedCategory D₀]
variable {E₀ : Type*} [Category E₀] [Abelian E₀] [HasDerivedCategory E₀]
variable {F₀ : Type*} [Category F₀] [Abelian F₀] [HasDerivedCategory F₀]
variable (K : A₀ ⥤ B₀) (L : B₀ ⥤ E₀) (I : C₀ ⥤ D₀) (J : D₀ ⥤ F₀)
  (R : C₀ ⥤ A₀) (P : D₀ ⥤ B₀) (Q : F₀ ⥤ E₀) (I' : C₀ ⥤ F₀) (K' : A₀ ⥤ E₀)
variable [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
variable [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
variable [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
variable [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
variable [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
variable [I'.Additive] [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
variable [K'.Additive] [PreservesFiniteLimits K'] [PreservesFiniteColimits K']

private theorem derivedSquare_horizontal
    (ei : I ⋙ J ≅ I') (ek : K ⋙ L ≅ K')
    (t₁ : I ⋙ P ⟶ R ⋙ K) (t₂ : J ⋙ Q ⟶ P ⋙ L) (t : I' ⋙ Q ⟶ R ⋙ K')
    (ht : ∀ X, Q.map (ei.hom.app X) ≫ t.app X =
      t₂.app (I.obj X) ≫ L.map (t₁.app X) ≫ ek.hom.app (R.obj X))
    (N : DerivedCategory C₀) :
    Q.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso I J ≪≫
      Functor.mapDerivedCategoryNatIso ei).hom.app N) ≫
        (derivedSquare I' Q R K' t).app N =
      (derivedSquare J Q P L t₂).app (I.mapDerivedCategory.obj N) ≫
        L.mapDerivedCategory.map ((derivedSquare I P R K t₁).app N) ≫
        (Functor.mapDerivedCategoryCompIso K L ≪≫
          Functor.mapDerivedCategoryNatIso ek).hom.app (R.mapDerivedCategory.obj N) := by
  let ei' := Functor.mapDerivedCategoryCompIso I J ≪≫
    Functor.mapDerivedCategoryNatIso ei
  let ek' := Functor.mapDerivedCategoryCompIso K L ≪≫
    Functor.mapDerivedCategoryNatIso ek
  let a₁ := derivedSquare I P R K t₁
  let a₂ := derivedSquare J Q P L t₂
  let a := derivedSquare I' Q R K' t
  let lhs : I.mapDerivedCategory ⋙ J.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶
      R.mapDerivedCategory ⋙ K'.mapDerivedCategory :=
    Functor.whiskerRight ei'.hom Q.mapDerivedCategory ≫ a
  let rhs : I.mapDerivedCategory ⋙ J.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶
      R.mapDerivedCategory ⋙ K'.mapDerivedCategory :=
    Functor.whiskerLeft I.mapDerivedCategory a₂ ≫
      Functor.whiskerRight a₁ L.mapDerivedCategory ≫
      Functor.whiskerLeft R.mapDerivedCategory ek'.hom
  suffices he : lhs = rhs from congr_app he N
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₀ (.up ℤ)) (fun X ↦ ?_)
  dsimp only [lhs, rhs, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  let XR := (R.mapHomologicalComplex (.up ℤ)).obj X
  let XI := (I.mapHomologicalComplex (.up ℤ)).obj X
  rw [← cancel_mono (K'.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app X) ≫
    K'.mapDerivedCategoryFactors.hom.app XR)]
  simp only [Category.assoc]
  have nk := ek'.hom.naturality (R.mapDerivedCategoryFactors.hom.app X)
  dsimp only [Functor.comp_map] at nk
  rw [← reassoc_of% nk, derivedComp_fac K L K' ek XR]
  have h₁ := congrArg L.mapDerivedCategory.map (derivedSquare_fac I P R K t₁ X)
  simp only [Functor.map_comp] at h₁
  rw [reassoc_of% h₁]
  have n₁ := L.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X)
  dsimp only [Functor.comp_map] at n₁
  change L.mapDerivedCategory.map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X)) ≫
      L.mapDerivedCategoryFactors.hom.app ((K.mapHomologicalComplex (.up ℤ)).obj XR) =
    L.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj XI) ≫
      DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X)) at n₁
  rw [reassoc_of% n₁]
  have n₂ := a₂.naturality (I.mapDerivedCategoryFactors.hom.app X)
  dsimp only [Functor.comp_map] at n₂
  rw [← reassoc_of% n₂, reassoc_of% (derivedSquare_fac J Q P L t₂ XI),
    derivedSquare_fac I' Q R K' t X]
  have hi := congrArg Q.mapDerivedCategory.map (derivedComp_fac I J I' ei X)
  simp only [Functor.map_comp] at hi
  rw [reassoc_of% hi]
  have n₃ := Q.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex ei.hom (.up ℤ)).app X)
  dsimp only [Functor.comp_map] at n₃
  erw [reassoc_of% n₃]
  simp only [← DerivedCategory.Q.map_comp]
  have hc : (Q.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex ei.hom (.up ℤ)).app X) ≫
      (NatTrans.mapHomologicalComplex t (.up ℤ)).app X =
    (NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app XI ≫
      (L.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X) ≫
      (NatTrans.mapHomologicalComplex ek.hom (.up ℤ)).app XR := by
    ext n
    change Q.map (ei.hom.app (X.X n)) ≫ t.app (X.X n) =
      t₂.app (I.obj (X.X n)) ≫ L.map (t₁.app (X.X n)) ≫ ek.hom.app (R.obj (X.X n))
    exact ht (X.X n)
  exact congrArg (fun f ↦ Q.mapDerivedCategory.map
    (J.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app X)) ≫
    Q.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app XI) ≫
    Q.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj XI) ≫
    DerivedCategory.Q.map f) hc

end DerivedHorizontal

end PastingTransparency

attribute [local irreducible] moduleAlpha moduleGComp moduleJComp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem module_isZero_of_eval {X : Scheme.{u}} (M : Modules R φ X)
    (h : ∀ n, IsZero ((eval R φ X n).obj M)) : IsZero M := by
  -- Componentwise exactness detects zero objects on the ordinary system category.
  let S : ShortComplex (Modules R φ X) :=
    ShortComplex.mk (0 : M ⟶ M) (0 : M ⟶ M) (by simp)
  let d := (WeilConjectures.SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)).some
  have hs : S.Exact := (d.systems.componentwise S).mpr (fun n ↦
    (S.map (eval R φ X n)).exact_of_isZero_X₂ (h n))
  exact hs.isZero_of_both_zeros rfl rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem module_disjoint_direct {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Modules R φ C) :
    IsZero ((pull R φ s).obj ((push R φ c).obj N)) := by
  apply module_isZero_of_eval R φ
  intro n
  let e := (moduleEvalG R φ s n).app ((push R φ c).obj N) ≪≫
    (StrictTower.modulePullback (R n) s).mapIso ((moduleEvalP R φ c n).app N)
  exact (StrictTower.module_disjoint_direct (R n) s c hc
    ((eval R φ C n).obj N)).of_iso e

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem module_disjoint_extension {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Modules R φ U) :
    IsZero ((pull R φ c).obj ((extension R φ s).obj N)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply ((moduleAdj R φ c).homEquiv _ _).injective
  apply ((moduleJAdj R φ s).homEquiv _ _).injective
  exact (module_disjoint_direct R φ s c hc _).eq_of_tgt _ _

/-- The system clopen projection is identity on its image and zero on the complement.
Source: Stacks 09AE; node proof Step 4
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: split every test object into its pullbacks of the clopen image and its
complement. The sheaf axiom identifies its sections with the product of the two
section modules. The unit followed by inverse open-to-direct comparison is (x,y) ↦
(x,0). The horizontal restrictions are semilinear componentwise maps, so they
commute with this projection, as do module maps and differentials. -/
theorem modulePi_components {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Modules R φ X) :
    (pull R φ s).map ((modulePi R φ s).app M) =
        (moduleJAdj R φ s).unit.app ((pull R φ s).obj M) ∧
      (pull R φ c).map ((modulePi R φ s).app M) = 0 := by
  refine ⟨?_, ?_⟩
  · have hu := moduleJAdj_unit_isIso R φ s
    letI _inst : IsIso (moduleOpenToP R φ s) := moduleOpenToP_isIso R φ s
    let t : Adjunction.Triple (extension R φ s) (pull R φ s) (push R φ s) :=
      ⟨moduleJAdj R φ s, moduleAdj R φ s⟩
    let ff := (moduleJAdj R φ s).fullyFaithfulLOfIsIsoUnit
    have hfull := ff.full
    have hfaith := ff.faithful
    have he : moduleOpenToP R φ s = t.leftToRight := by
      ext N
      simp [moduleOpenToP, push, t, Adjunction.Triple.leftToRight]
    simp only [modulePi, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.map_comp]
    apply (cancel_mono ((pull R φ s).map ((moduleOpenToP R φ s).app
      ((pull R φ s).obj M)))).1
    rw [← Functor.map_comp]
    rw [← Functor.map_comp]
    simp only [Category.assoc]
    have hh := (asIso (moduleOpenToP R φ s)).inv_hom_id_app
      ((pull R φ s).obj M)
    rw [show (inv (moduleOpenToP R φ s)).app ((pull R φ s).obj M) ≫
        (moduleOpenToP R φ s).app ((pull R φ s).obj M) = 𝟙 _ from hh]
    rw [he]
    simp only [Functor.map_comp]
    rw [t.leftToRight_app_obj]
    change (pull R φ s).map ((moduleAdj R φ s).unit.app M) ≫
        (pull R φ s).map (𝟙 _) =
      (moduleJAdj R φ s).unit.app _ ≫
        (pull R φ s).map ((moduleJAdj R φ s).counit.app M ≫
          (moduleAdj R φ s).unit.app M)
    rw [Functor.map_comp, ← Category.assoc,
      (moduleJAdj R φ s).right_triangle_components]
    simp
  · have hd : Disjoint (Set.range s) (Set.range c) := by
      rw [hc]
      exact disjoint_compl_right
    exact (module_disjoint_extension R φ s c hd ((pull R φ s).obj M)).eq_of_tgt _ _

section OrdinaryPastingProofs
attribute [local irreducible] ordinaryRealization ordinaryPullComparison ordinaryOpenComparison
  Functor.leftAdjoint
  StrictTower.G StrictTower.J
  StrictTower.alpha StrictTower.gComp StrictTower.jComp

section OrdinaryVerticalTransport

variable {A₀ B₀ C₀ D₀ E₀ F₀ A₁ B₁ C₁ D₁ E₁ F₁ : Type*}
  [Category A₀] [Category B₀] [Category C₀] [Category D₀] [Category E₀] [Category F₀]
  [Category A₁] [Category B₁] [Category C₁] [Category D₁] [Category E₁] [Category F₁]
  {EA : A₀ ⥤ A₁} {EB : B₀ ⥤ B₁} {EC : C₀ ⥤ C₁}
  {ED : D₀ ⥤ D₁} {EE : E₀ ⥤ E₁} {EF : F₀ ⥤ F₁}
  {P₁ : D₀ ⥤ B₀} {P₂ : F₀ ⥤ D₀} {P₁₂ : F₀ ⥤ B₀}
  {R₁ : C₀ ⥤ A₀} {R₂ : E₀ ⥤ C₀} {R₁₂ : E₀ ⥤ A₀}
  {p₁ : D₁ ⥤ B₁} {p₂ : F₁ ⥤ D₁} {p₁₂ : F₁ ⥤ B₁}
  {r₁ : C₁ ⥤ A₁} {r₂ : E₁ ⥤ C₁} {r₁₂ : E₁ ⥤ A₁}
  {K : A₀ ⥤ B₀} {I : C₀ ⥤ D₀} {J : E₀ ⥤ F₀}
  {k : A₁ ⥤ B₁} {i : C₁ ⥤ D₁} {j : E₁ ⥤ F₁}
  {cp : P₁₂ ≅ P₂ ⋙ P₁} {cr : R₁₂ ≅ R₂ ⋙ R₁}
  {cp' : p₁₂ ≅ p₂ ⋙ p₁} {cr' : r₁₂ ≅ r₂ ⋙ r₁}
  {a : I ⋙ P₁ ⟶ R₁ ⋙ K} {b : J ⋙ P₂ ⟶ R₂ ⋙ I}
  {c : J ⋙ P₁₂ ⟶ R₁₂ ⋙ K}
  {a' : i ⋙ p₁ ⟶ r₁ ⋙ k} {b' : j ⋙ p₂ ⟶ r₂ ⋙ i}
  {c' : j ⋙ p₁₂ ⟶ r₁₂ ⋙ k}

private theorem ordinary_vertical_transport
    (eP₁ : P₁ ⋙ EB ≅ ED ⋙ p₁) (eP₂ : P₂ ⋙ ED ≅ EF ⋙ p₂)
    (eP₁₂ : P₁₂ ⋙ EB ≅ EF ⋙ p₁₂)
    (eR₁ : R₁ ⋙ EA ≅ EC ⋙ r₁) (eR₂ : R₂ ⋙ EC ≅ EE ⋙ r₂)
    (eR₁₂ : R₁₂ ⋙ EA ≅ EE ⋙ r₁₂)
    (eK : K ⋙ EB ≅ EA ⋙ k) (eI : I ⋙ ED ≅ EC ⋙ i)
    (eJ : J ⋙ EF ≅ EE ⋙ j)
    (hp : ∀ N : F₀, EB.map (cp.hom.app N) ≫ eP₁.hom.app (P₂.obj N) ≫
      p₁.map (eP₂.hom.app N) = eP₁₂.hom.app N ≫ cp'.hom.app (EF.obj N))
    (hr : ∀ N : E₀, EA.map (cr.hom.app N) ≫ eR₁.hom.app (R₂.obj N) ≫
      r₁.map (eR₂.hom.app N) = eR₁₂.hom.app N ≫ cr'.hom.app (EE.obj N))
    (ha : OrdinarySquareComparison
      (EA := EA) (EB := EB) (EC := EC) (ED := ED)
      (R₀ := R₁) (P₀ := P₁) (K := K) (I := I)
      (r := r₁) (p := p₁) (k := k) (i := i) eR₁ eP₁ eK eI a a')
    (hb : OrdinarySquareComparison
      (EA := EC) (EB := ED) (EC := EE) (ED := EF)
      (R₀ := R₂) (P₀ := P₂) (K := I) (I := J)
      (r := r₂) (p := p₂) (k := i) (i := j) eR₂ eP₂ eI eJ b b')
    (hc : OrdinarySquareComparison
      (EA := EA) (EB := EB) (EC := EE) (ED := EF)
      (R₀ := R₁₂) (P₀ := P₁₂) (K := K) (I := J)
      (r := r₁₂) (p := p₁₂) (k := k) (i := j) eR₁₂ eP₁₂ eK eJ c c')
    (hstrict : ∀ N : E₁, cp'.hom.app (j.obj N) ≫ p₁.map (b'.app N) ≫
      a'.app (r₂.obj N) = c'.app N ≫ k.map (cr'.hom.app N)) (N : E₀) :
    EB.map (cp.hom.app (J.obj N) ≫ P₁.map (b.app N) ≫ a.app (R₂.obj N)) =
      EB.map (c.app N ≫ K.map (cr.hom.app N)) := by
  apply (cancel_mono (eK.hom.app (R₁.obj (R₂.obj N)) ≫
    k.map (eR₁.hom.app (R₂.obj N)) ≫ k.map (r₁.map (eR₂.hom.app N)))).1
  simp only [Functor.map_comp, Category.assoc]
  have hn₄ := eK.hom.naturality (cr.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₄
  rw [reassoc_of% hn₄]
  have hr' := congrArg k.map (hr N)
  simp only [Functor.map_comp] at hr'
  rw [hr', reassoc_of% (hc.equation N), reassoc_of% (ha.equation (R₂.obj N))]
  have hn₁ := a'.naturality (eR₂.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁
  rw [← hn₁]
  have hn₂ := eP₁.hom.naturality (b.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₂
  rw [reassoc_of% hn₂]
  have hp' := congrArg p₁.map (hb.equation N)
  simp only [Functor.map_comp] at hp'
  rw [reassoc_of% hp', reassoc_of% (hp (J.obj N))]
  have hn₃ := cp'.hom.naturality (eJ.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₃
  rw [← reassoc_of% hn₃, hstrict]

end OrdinaryVerticalTransport

section OrdinaryHorizontalTransport

variable {A₀ B₀ C₀ D₀ E₀ F₀ A₁ B₁ C₁ D₁ E₁ F₁ : Type*}
  [Category A₀] [Category B₀] [Category C₀] [Category D₀] [Category E₀] [Category F₀]
  [Category A₁] [Category B₁] [Category C₁] [Category D₁] [Category E₁] [Category F₁]
  {EA : A₀ ⥤ A₁} {EB : B₀ ⥤ B₁} {EC : C₀ ⥤ C₁}
  {ED : D₀ ⥤ D₁} {EE : E₀ ⥤ E₁} {EF : F₀ ⥤ F₁}
  {R₀ : C₀ ⥤ A₀} {P : D₀ ⥤ B₀} {Q : F₀ ⥤ E₀}
  {r : C₁ ⥤ A₁} {p : D₁ ⥤ B₁} {q : F₁ ⥤ E₁}
  {K : A₀ ⥤ B₀} {L : B₀ ⥤ E₀} {I : C₀ ⥤ D₀} {J : D₀ ⥤ F₀}
  {K₁₂ : A₀ ⥤ E₀} {I₁₂ : C₀ ⥤ F₀}
  {k : A₁ ⥤ B₁} {l : B₁ ⥤ E₁} {i : C₁ ⥤ D₁} {j : D₁ ⥤ F₁}
  {k₁₂ : A₁ ⥤ E₁} {i₁₂ : C₁ ⥤ F₁}
  {ck : K ⋙ L ≅ K₁₂} {ci : I ⋙ J ≅ I₁₂}
  {ck' : k ⋙ l ≅ k₁₂} {ci' : i ⋙ j ≅ i₁₂}
  {a : I ⋙ P ⟶ R₀ ⋙ K} {b : J ⋙ Q ⟶ P ⋙ L} {c : I₁₂ ⋙ Q ⟶ R₀ ⋙ K₁₂}
  {a' : i ⋙ p ⟶ r ⋙ k} {b' : j ⋙ q ⟶ p ⋙ l} {c' : i₁₂ ⋙ q ⟶ r ⋙ k₁₂}

private theorem ordinary_horizontal_transport
    (eR : R₀ ⋙ EA ≅ EC ⋙ r) (eP : P ⋙ EB ≅ ED ⋙ p) (eQ : Q ⋙ EE ≅ EF ⋙ q)
    (eK : K ⋙ EB ≅ EA ⋙ k) (eL : L ⋙ EE ≅ EB ⋙ l)
    (eI : I ⋙ ED ≅ EC ⋙ i) (eJ : J ⋙ EF ≅ ED ⋙ j)
    (eK₁₂ : K₁₂ ⋙ EE ≅ EA ⋙ k₁₂) (eI₁₂ : I₁₂ ⋙ EF ≅ EC ⋙ i₁₂)
    (hi : ∀ N : C₀, EF.map (ci.hom.app N) ≫ eI₁₂.hom.app N =
      eJ.hom.app (I.obj N) ≫ j.map (eI.hom.app N) ≫ ci'.hom.app (EC.obj N))
    (hk : ∀ N : A₀, EE.map (ck.hom.app N) ≫ eK₁₂.hom.app N =
      eL.hom.app (K.obj N) ≫ l.map (eK.hom.app N) ≫ ck'.hom.app (EA.obj N))
    (ha : OrdinarySquareComparison
      (EA := EA) (EB := EB) (EC := EC) (ED := ED)
      (R₀ := R₀) (P₀ := P) (K := K) (I := I)
      (r := r) (p := p) (k := k) (i := i) eR eP eK eI a a')
    (hb : OrdinarySquareComparison
      (EA := EB) (EB := EE) (EC := ED) (ED := EF)
      (R₀ := P) (P₀ := Q) (K := L) (I := J)
      (r := p) (p := q) (k := l) (i := j) eP eQ eL eJ b b')
    (hc : OrdinarySquareComparison
      (EA := EA) (EB := EE) (EC := EC) (ED := EF)
      (R₀ := R₀) (P₀ := Q) (K := K₁₂) (I := I₁₂)
      (r := r) (p := q) (k := k₁₂) (i := i₁₂) eR eQ eK₁₂ eI₁₂ c c')
    (hstrict : ∀ N : C₁, q.map (ci'.hom.app N) ≫ c'.app N =
      b'.app (i.obj N) ≫ l.map (a'.app N) ≫ ck'.hom.app (r.obj N)) (N : C₀) :
    EE.map (Q.map (ci.hom.app N) ≫ c.app N) =
      EE.map (b.app (I.obj N) ≫ L.map (a.app N) ≫ ck.hom.app (R₀.obj N)) := by
  apply (cancel_mono (eK₁₂.hom.app (R₀.obj N) ≫ k₁₂.map (eR.hom.app N))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hc.equation]
  have hn₁ := eQ.hom.naturality (ci.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁
  rw [reassoc_of% hn₁]
  have hb' := congrArg q.map (hi N)
  simp only [Functor.map_comp] at hb'
  rw [reassoc_of% hb', reassoc_of% (hk (R₀.obj N))]
  have hn₂ := ck'.hom.naturality (eR.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₂
  rw [← hn₂]
  have hn₃ := eL.hom.naturality (a.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₃
  rw [reassoc_of% hn₃]
  have ht := congrArg l.map (ha.equation N)
  simp only [Functor.map_comp] at ht
  rw [reassoc_of% ht, reassoc_of% (hb.equation (I.obj N))]
  have hn₄ := b'.naturality (eI.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₄
  rw [← reassoc_of% hn₄, hstrict]

end OrdinaryHorizontalTransport

private theorem faithful_postcompose {C D H : Type*}
    [Category C] [Category D] [Category H]
    (E : C ⥤ H) (F : C ⥤ D) (G : D ⥤ H) [G.Faithful]
    (h : E = F ⋙ G) {X Y : C} (f g : X ⟶ Y) (he : E.map f = E.map g) :
    F.map f = F.map g := by
  subst E
  exact G.map_injective he

private theorem ordinaryRealization_jointlyFaithful {X : Scheme.{u}}
    {M N : Modules R φ X} (f g : M ⟶ N)
    (h : ∀ n, (ordinaryRealization R φ n X).map f =
      (ordinaryRealization R φ n X).map g) : f = g := by
  have he (n : ℕ) : (eval R φ X n).map f = (eval R φ X n).map g := by
    exact faithful_postcompose (ordinaryRealization R φ n X) (eval R φ X n)
      (Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0)
      (ordinaryRealization_eq R φ n X) f g (h n)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun a ↦ a.val.app (op U.unop.2) x) (he U.unop.1)

/-- Intrinsic moduleAlpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: ordinary coefficient evaluation followed by the constant tower and degree-zero
embeddings preserves the single-square comparison and the pullback compositors.
The finite categorical transport calculation below therefore turns strict-tower vertical
pasting into the evaluated equation. The degree-zero and constant embeddings are
faithful, and ordinary system maps are determined componentwise, giving the equality. -/
theorem moduleAlpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Modules R φ E) :
    (moduleGComp R φ p₁ p₂).hom.app ((extension R φ j).obj N) ≫
        (pull R φ p₁).map ((moduleAlpha R φ i r₂ p₂ j h₂).app N) ≫
        (moduleAlpha R φ k r₁ p₁ i h₁).app ((pull R φ r₂).obj N) =
      (moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (extension R φ k).map ((moduleGComp R φ r₁ r₂).hom.app N) := by
  apply ordinaryRealization_jointlyFaithful R φ
  intro n
  obtain ⟨gIso, jIso, hg, hj, ha⟩ := ordinaryClopenEvaluation R φ n
  exact ordinary_vertical_transport
    (EA := ordinaryRealization R φ n A) (EB := ordinaryRealization R φ n B₀)
    (EC := ordinaryRealization R φ n C) (ED := ordinaryRealization R φ n D)
    (EE := ordinaryRealization R φ n E) (EF := ordinaryRealization R φ n F)
    (P₁ := pull R φ p₁) (P₂ := pull R φ p₂) (P₁₂ := pull R φ (p₁ ≫ p₂))
    (R₁ := pull R φ r₁) (R₂ := pull R φ r₂) (R₁₂ := pull R φ (r₁ ≫ r₂))
    (p₁ := StrictTower.G (R n) p₁) (p₂ := StrictTower.G (R n) p₂)
    (p₁₂ := StrictTower.G (R n) (p₁ ≫ p₂))
    (r₁ := StrictTower.G (R n) r₁) (r₂ := StrictTower.G (R n) r₂)
    (r₁₂ := StrictTower.G (R n) (r₁ ≫ r₂))
    (K := extension R φ k) (I := extension R φ i) (J := extension R φ j)
    (k := StrictTower.J (R n) k) (i := StrictTower.J (R n) i) (j := StrictTower.J (R n) j)
    (cp := moduleGComp R φ p₁ p₂) (cr := moduleGComp R φ r₁ r₂)
    (cp' := StrictTower.gComp (R n) p₁ p₂) (cr' := StrictTower.gComp (R n) r₁ r₂)
    (a := moduleAlpha R φ k r₁ p₁ i h₁) (b := moduleAlpha R φ i r₂ p₂ j h₂)
    (c := moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    (a' := StrictTower.alpha (R n) k r₁ p₁ i h₁)
    (b' := StrictTower.alpha (R n) i r₂ p₂ j h₂)
    (c' := StrictTower.alpha (R n) k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    (gIso _ _ p₁) (gIso _ _ p₂) (gIso _ _ (p₁ ≫ p₂))
    (gIso _ _ r₁) (gIso _ _ r₂) (gIso _ _ (r₁ ≫ r₂))
    (jIso _ _ k) (jIso _ _ i) (jIso _ _ j) (hg p₁ p₂) (hg r₁ r₂)
    (ha k r₁ p₁ i h₁) (ha i r₂ p₂ j h₂) (ha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    (StrictTower.alpha_vertical (R n) k i j r₁ r₂ p₁ p₂ h₁ h₂ h) N

/-- Intrinsic moduleAlpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: ordinary coefficient evaluation followed by the constant tower and degree-zero
embeddings preserves the single-square comparison and the open-extension compositors.
The finite categorical transport calculation below turns strict-tower horizontal
pasting into the evaluated equation. Faithfulness of the two embeddings and
componentwise extensionality of ordinary system maps then give the equality. -/
theorem moduleAlpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Modules R φ C) :
    (pull R φ q).map ((moduleJComp R φ i j).hom.app N) ≫
        (moduleAlpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (moduleAlpha R φ l p q j h₂).app ((extension R φ i).obj N) ≫
        (extension R φ l).map ((moduleAlpha R φ k r p i h₁).app N) ≫
        (moduleJComp R φ k l).hom.app ((pull R φ r).obj N) := by
  apply ordinaryRealization_jointlyFaithful R φ
  intro n
  obtain ⟨gIso, jIso, hg, hj, ha⟩ := ordinaryClopenEvaluation R φ n
  exact ordinary_horizontal_transport
    (EA := ordinaryRealization R φ n A) (EB := ordinaryRealization R φ n B₀)
    (EC := ordinaryRealization R φ n C) (ED := ordinaryRealization R φ n D)
    (EE := ordinaryRealization R φ n E) (EF := ordinaryRealization R φ n F)
    (R₀ := pull R φ r) (P := pull R φ p) (Q := pull R φ q)
    (r := StrictTower.G (R n) r) (p := StrictTower.G (R n) p) (q := StrictTower.G (R n) q)
    (K := extension R φ k) (L := extension R φ l)
    (I := extension R φ i) (J := extension R φ j)
    (K₁₂ := extension R φ (k ≫ l)) (I₁₂ := extension R φ (i ≫ j))
    (k := StrictTower.J (R n) k) (l := StrictTower.J (R n) l)
    (i := StrictTower.J (R n) i) (j := StrictTower.J (R n) j)
    (k₁₂ := StrictTower.J (R n) (k ≫ l)) (i₁₂ := StrictTower.J (R n) (i ≫ j))
    (ck := moduleJComp R φ k l) (ci := moduleJComp R φ i j)
    (ck' := StrictTower.jComp (R n) k l) (ci' := StrictTower.jComp (R n) i j)
    (a := moduleAlpha R φ k r p i h₁) (b := moduleAlpha R φ l p q j h₂)
    (c := moduleAlpha R φ (k ≫ l) r q (i ≫ j) h)
    (a' := StrictTower.alpha (R n) k r p i h₁)
    (b' := StrictTower.alpha (R n) l p q j h₂)
    (c' := StrictTower.alpha (R n) (k ≫ l) r q (i ≫ j) h)
    (gIso _ _ r) (gIso _ _ p) (gIso _ _ q)
    (jIso _ _ k) (jIso _ _ l) (jIso _ _ i) (jIso _ _ j)
    (jIso _ _ (k ≫ l)) (jIso _ _ (i ≫ j)) (hj i j) (hj k l)
    (ha k r p i h₁) (ha l p q j h₂) (ha (k ≫ l) r q (i ≫ j) h)
    (StrictTower.alpha_horizontal (R n) k l i j r p q h₁ h₂ h) N

end OrdinaryPastingProofs

/-- Intrinsic alpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: after beta, the two clopen projections select nested open components.
On every test object's intersections of the two clopen decompositions the two
composites are both identity or both zero. Sheaf uniqueness proves equality,
termwise extension preserves it, and exact localization descends it. -/
theorem alpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Derived R φ E) :
    (gComp R φ p₁ p₂).hom.app ((J R φ j).obj N) ≫
        (G R φ p₁).map ((alpha R φ i r₂ p₂ j h₂).app N) ≫
        (alpha R φ k r₁ p₁ i h₁).app ((G R φ r₂).obj N) =
      (alpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (J R φ k).map ((gComp R φ r₁ r₂).hom.app N) := by
  simpa only [alpha, gComp, derivedSquare] using
    derivedSquare_vertical
      (extension R φ k) (extension R φ i) (extension R φ j)
      (pull R φ p₁) (pull R φ p₂) (pull R φ r₁) (pull R φ r₂)
      (pull R φ (p₁ ≫ p₂)) (pull R φ (r₁ ≫ r₂))
      (moduleGComp R φ p₁ p₂) (moduleGComp R φ r₁ r₂)
      (moduleAlpha R φ k r₁ p₁ i h₁) (moduleAlpha R φ i r₂ p₂ j h₂)
      (moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
      (fun X ↦ moduleAlpha_vertical R φ k i j r₁ r₂ p₁ p₂ h₁ h₂ h X) N

/-- Intrinsic alpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the first clopen projection selects l(W), and the second selects lk(V)
inside it. Their composite selects lk(V) and vanishes on its complement. Use the
open-composition beta equation and exact localization to identify the displayed maps. -/
theorem alpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Derived R φ C) :
    (G R φ q).map ((jComp R φ i j).hom.app N) ≫
        (alpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (alpha R φ l p q j h₂).app ((J R φ i).obj N) ≫
        (J R φ l).map ((alpha R φ k r p i h₁).app N) ≫
        (jComp R φ k l).hom.app ((G R φ r).obj N) := by
  simpa only [alpha, jComp, derivedSquare] using
    derivedSquare_horizontal
      (extension R φ k) (extension R φ l) (extension R φ i) (extension R φ j)
      (pull R φ r) (pull R φ p) (pull R φ q)
      (extension R φ (i ≫ j)) (extension R φ (k ≫ l))
      (moduleJComp R φ i j) (moduleJComp R φ k l)
      (moduleAlpha R φ k r p i h₁) (moduleAlpha R φ l p q j h₂)
      (moduleAlpha R φ (k ≫ l) r q (i ≫ j) h)
      (fun X ↦ moduleAlpha_horizontal R φ k l i j r p q h₁ h₂ h X) N

/-- Both normalized proper/open mate-pasting laws, as system transformations.
Source: Stacks 0F7C, 0F7D and the varying-ring extension of the local-pairs argument
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof (the node's eleven steps):
1. Apply the constant-ring geometric calculus, with ring Z, to obtain the clopen
   lift s=(k,r) into W ×_T S and its complementary open, without cartesianness.
2. Inverse image and direct-sum extension act on the same underlying abelian
   sheaves after restriction along φ. A semilinear transition sends [a,x] to
   [a,t(x)], with t(cx)=φ(c)t(x); exactness is componentwise.
3. Cartesian open comparison preserves the lift label under the fibre-product
   bijection. It is the inverse open-unit transpose moduleBeta. Both routes past
   a transition therefore send a generator to [a',t(x)]. Sheafify this equality.
4. On the two clopen components the projection is (x,y) ↦ (x,0). It commutes with
   every semilinear transition, restriction and differential. This is modulePi;
   composition with moduleBeta and the compositors gives moduleAlpha.
5. Inverse-image composition identifies iterated pullbacks, and open composition
   combines lift labels without changing sections. The section-normalized
   direct-image compositor and its conjugate fix these comparisons and units.
6. Vertically, the projections retain nested components. On the final retained
   component both composites are identity, and on every other component one
   projection is zero. Sheaf uniqueness proves moduleAlpha_vertical.
7. Horizontally the projections select l(W) and then lk(V) inside it. The same
   identity/zero calculation and the open compositor give moduleAlpha_horizontal.
8. Apply the simultaneous ordinary-derived section model. Localize these actual
   degreewise maps of systems, obtaining alpha and its two pasting equations.
   Equalities are not inferred from evaluation of arbitrary derived morphisms.
9. Take the proper-adjunction mate. Its definition is precisely eta_p, alpha
   whiskered by Rr, and Rp(k! epsilon_r), with the specified order.
10. mateEquiv_hcomp applied to Step 6 proves the first displayed law, and
    mateEquiv_vcomp applied to Step 7 proves the second. Conjugate comparisons
    transport from composite adjunctions to the intrinsic proper compositors.
11. Identity lift labels and projections give the identity mate via the triangle
    laws. Evaluation preserves the constructed maps, units and counits, so the
    evaluated mate is the arbitrary constant-R_n clopen-projection mate. This
    uses neither finite-coefficient invertibility nor faithfulness of evaluation. -/
theorem properOpenPasting :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived R φ A),
      (J R φ j).map ((pComp R φ r₁ r₂).hom.app M) ≫
          (gamma R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (pComp R φ p₁ p₂).inv.app ((J R φ k).obj M) =
        (gamma R φ i r₂ p₂ j h₂).app ((P R φ r₁).obj M) ≫
          (P R φ p₂).map ((gamma R φ k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived R φ A),
      (jComp R φ i j).hom.app ((P R φ r).obj M) ≫
          (gamma R φ (k ≫ l) r q (i ≫ j) h).app M ≫
          (P R φ q).map ((jComp R φ k l).inv.app M) =
        (J R φ j).map ((gamma R φ k r p i h₁).app M) ≫
          (gamma R φ l p q j h₂).app ((J R φ k).obj M)) := by
  constructor
  · intro A C E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    let a₁ := TwoSquare.mk _ _ _ _ (alpha R φ k r₁ p₁ i h₁)
    let a₂ := TwoSquare.mk _ _ _ _ (alpha R φ i r₂ p₂ j h₂)
    let a := TwoSquare.mk _ _ _ _ (alpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    have ha : TwoSquare.vComp a₂ a₁ =
        (a.whiskerLeft (gComp R φ r₁ r₂).hom).whiskerRight
          (gComp R φ p₁ p₂).inv := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      dsimp [a₁, a₂, a, TwoSquare.vComp, TwoSquare.whiskerLeft,
        TwoSquare.whiskerRight]
      simpa [TwoSquare.mk, Category.assoc] using
        (congrArg (fun f ↦ (gComp R φ p₁ p₂).inv.app ((J R φ j).obj N) ≫ f)
          (alpha_vertical R φ k i j r₁ r₂ p₁ p₂ h₁ h₂ h N))
    have hm := congrArg
      (mateEquiv ((adj R φ r₂).comp (adj R φ r₁))
        ((adj R φ p₂).comp (adj R φ p₁))) ha
    rw [mateEquiv_hcomp,
      mateEquiv_conjugateEquiv_vcomp _ (adj R φ (p₁ ≫ p₂)),
      conjugateEquiv_mateEquiv_vcomp _ (adj R φ (r₁ ≫ r₂))] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    simpa only [a₁, a₂, a, gamma, pComp, conjugateIsoEquiv_apply_hom,
      conjugateIsoEquiv_apply_inv, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hmM.symm
  · intro A C E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    let a₁ := TwoSquare.mk _ _ _ _ (alpha R φ k r p i h₁)
    let a₂ := TwoSquare.mk _ _ _ _ (alpha R φ l p q j h₂)
    let a := TwoSquare.mk _ _ _ _ (alpha R φ (k ≫ l) r q (i ≫ j) h)
    have ha : TwoSquare.hComp a₁ a₂ =
        (a.whiskerTop (jComp R φ i j).hom).whiskerBottom
          (jComp R φ k l).inv := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      dsimp [a₁, a₂, a, TwoSquare.hComp, TwoSquare.whiskerTop,
        TwoSquare.whiskerBottom]
      have hh := alpha_horizontal R φ k l i j r p q h₁ h₂ h N
      have hh' := congrArg
        (fun f ↦ f ≫ (jComp R φ k l).inv.app ((G R φ r).obj N)) hh
      simpa [TwoSquare.mk, Category.assoc] using hh'.symm
    have hm := congrArg (mateEquiv (adj R φ r) (adj R φ q)) ha
    rw [mateEquiv_vcomp (adj R φ r) (adj R φ p) (adj R φ q)] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    rw [show (a.whiskerTop (jComp R φ i j).hom).whiskerBottom
        (jComp R φ k l).inv =
        Functor.whiskerRight (jComp R φ i j).hom (G R φ q) ≫ a ≫
          Functor.whiskerLeft (G R φ r) (jComp R φ k l).inv from by
          simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc],
      mate_whisker] at hmM
    simpa only [a₁, a₂, a, gamma, TwoSquare.vComp, TwoSquare.mk,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hmM.symm

section OrdinaryUnits
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] moduleAdj

private theorem moduleP_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : Modules R φ X) (U : ℕ × Y.ProEt)
    (m : ((push R φ f).obj N).val.obj (op U)) :
    ((eqToIso (congrArg (push R φ) e)).hom.app N).val.app (op U) m =
      N.val.map (Prod.mkHom (𝟙 U.1)
        (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U.2) e.symm))).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem modulePComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    modulePComp R φ (𝟙 U) j ≪≫
        eqToIso (congrArg (push R φ) (Category.id_comp j)) =
      Functor.isoWhiskerRight (modulePId R φ U) (push R φ j) ≪≫
        Functor.leftUnitor (push R φ j) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  change ((eqToIso (congrArg (push R φ) (Category.id_comp j))).hom.app N).val.app
      V (((modulePComp R φ (𝟙 U) j).hom.app N).val.app V m) =
    ((modulePId R φ U).hom.app N).val.app
      (op (V.unop.1, (Scheme.proEtaleBaseChange j).obj V.unop.2)) m
  rw [moduleP_transport R φ (Category.id_comp j) N V.unop]
  erw [(Classical.choose_spec (modulePComp_existsUnique R φ (𝟙 U) j)).1]
  erw [(Classical.choose_spec (modulePId_existsUnique R φ U)).1]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  have hsite :
      eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj V.unop.2)
        (Category.id_comp j).symm) ≫
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          (𝟙 U) j).hom.app V.unop.2 =
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app
        ((Scheme.proEtaleBaseChange j).obj V.unop.2) := by
    have hcongr {f g : U ⟶ X} (e : f = g) :
        MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e =
          eqToIso (congrArg Scheme.proEtaleBaseChange e) := by
      cases e
      simp only [MorphismProperty.Over.pullbackCongr_refl, eqToIso_refl]
    have h := congrArg (fun e ↦ e.hom.app V.unop.2)
      (MorphismProperty.Over.pullbackComp_id_left
        (P := @WeaklyEtale) (Q := ⊤) j ((𝟙 U) ≫ j) rfl)
    rw [hcongr] at h
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at h
    rw [h]
    simp only [eqToIso.hom,
      eqToHom_refl, NatTrans.id_app, Category.id_comp]
  exact congrArg (fun a : (Scheme.proEtaleBaseChange j).obj V.unop.2 ⟶
      (Scheme.proEtaleBaseChange (𝟙 U)).obj ((Scheme.proEtaleBaseChange j).obj V.unop.2) ↦
        N.val.map (Prod.mkHom (𝟙 V.unop.1) a).op m) hsite

private def moduleGId (X : Scheme.{u}) : pull R φ (𝟙 X) ≅ 𝟭 (Modules R φ X) :=
  Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)

private theorem moduleGComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp R φ (𝟙 U) j).hom ≫
        Functor.whiskerLeft (pull R φ j) (moduleGId R φ U).hom =
      (eqToIso (congrArg (pull R φ) (Category.id_comp j))).hom := by
  unfold moduleGComp moduleGId
  exact StrictTower.leftAdjoint_unit_left (pull R φ) (push R φ) (moduleAdj R φ)
    (moduleAdj R φ (𝟙 U)) (modulePId R φ U) (Category.id_comp j)
    (modulePComp R φ (𝟙 U) j) (modulePComp_id_left R φ j)

private theorem derived_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (pull R φ) e))).hom =
        (eqToIso (congrArg (G R φ) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

set_option backward.isDefEq.respectTransparency.types false in
private theorem gComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp R φ (𝟙 U) j).hom ≫
        Functor.whiskerLeft (G R φ j) (gId R φ U).hom =
      (eqToIso (congrArg (G R φ) (Category.id_comp j))).hom := by
  change (_ ≫ _) ≫ Functor.whiskerLeft (pull R φ j).mapDerivedCategory
    ((Functor.mapDerivedCategoryNatIso (moduleGId R φ U)).hom ≫
      (Functor.mapDerivedCategoryIdIso (Modules R φ U)).hom) = _
  rw [Category.assoc]
  exact
    (StrictTower.derived_unit_left (pull R φ j) (pull R φ ((𝟙 U) ≫ j))
    (pull R φ (𝟙 U)) (moduleGComp R φ (𝟙 U) j) (moduleGId R φ U)
    (eqToIso (congrArg (pull R φ) (Category.id_comp j)))
    (moduleGComp_id_left R φ j)).trans (derived_transport R φ (Category.id_comp j))

private theorem pull_equivalence {U X : Scheme.{u}} (s : U ⟶ X) [IsIso s] :
    (pull R φ s).IsEquivalence := by
  let e : Modules R φ X ≌ Modules R φ U := CategoryTheory.Equivalence.mk
    (pull R φ s) (pull R φ (inv s))
    ((moduleGId R φ X).symm ≪≫
      eqToIso (congrArg (pull R φ) (IsIso.inv_hom_id s).symm) ≪≫
      moduleGComp R φ (inv s) s)
    ((moduleGComp R φ s (inv s)).symm ≪≫
      eqToIso (congrArg (pull R φ) (IsIso.hom_inv_id s)) ≪≫ moduleGId R φ U)
  exact e.isEquivalence_functor

private theorem pi_isIso {U X : Scheme.{u}} (s : U ⟶ X) [IsIso s]
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (modulePi R φ s) := by
  have := pull_equivalence R φ s
  have := (moduleAdj R φ s).unit_isIso_of_L_fully_faithful
  have := moduleOpenToP_isIso R φ s
  unfold modulePi
  infer_instance

private theorem lift_isIso {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    IsIso (StrictTower.squareLift k r p i h) := by
  have he : StrictTower.squareLift k r p i h = hsq.isoPullback.hom := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst k r h).trans hsq.isoPullback_hom_fst.symm
    · exact (pullback.lift_snd k r h).trans hsq.isoPullback_hom_snd.symm
  rw [he]
  infer_instance

private theorem moduleAlpha_isIso {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    IsIso (moduleAlpha R φ k r p i h) := by
  have := lift_isIso k r p i h hsq
  have := pi_isIso R φ (StrictTower.squareLift k r p i h)
  unfold moduleAlpha
  infer_instance

private theorem alpha_isIso {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    IsIso (alpha R φ k r p i h) := by
  have := moduleAlpha_isIso R φ k r p i h hsq
  change IsIso ((Functor.mapDerivedCategorySquareIso
    (asIso (moduleAlpha R φ k r p i h))).hom)
  infer_instance

end OrdinaryUnits
private theorem alpha_proper_congr {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r r' : V ⟶ S) (p p' : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper r'] [IsProper p] [IsProper p']
    (hr : r = r') (hp : p = p') (h : k ≫ p = r ≫ i) (h' : k ≫ p' = r' ≫ i)
    (M : Derived R φ S) :
    (alpha R φ k r p i h).app M ≫
        (J R φ k).map ((eqToIso (congrArg (G R φ) hr)).hom.app M) =
      (eqToIso (congrArg (G R φ) hp)).hom.app ((J R φ i).obj M) ≫
        (alpha R φ k r' p' i h').app M := by
  cases hr
  cases hp
  simp

private theorem isoId_comm {C : Type*} [Category* C] {I : C ⥤ C}
    (e : I ≅ 𝟭 C) (M : C) : I.map (e.hom.app M) = e.hom.app (I.obj M) := by
  apply (cancel_mono (e.hom.app M)).1
  exact e.hom.naturality (e.hom.app M)

private theorem alpha_first {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U) :
    (alpha R φ j (𝟙 U) (𝟙 X) j h).app M ≫
        (J R φ j).map ((gId R φ U).hom.app M) =
      (gId R φ X).hom.app ((J R φ j).obj M) := by
  have := alpha_isIso R φ j (𝟙 U) (𝟙 X) j h (IsPullback.of_id_snd (f := j))
  let h' : j ≫ ((𝟙 X) ≫ (𝟙 X)) = ((𝟙 U) ≫ (𝟙 U)) ≫ j := by simp
  have ht := alpha_vertical R φ j j j (𝟙 U) (𝟙 U) (𝟙 X) (𝟙 X) h h h' M
  have hc := alpha_proper_congr R φ j ((𝟙 U) ≫ (𝟙 U)) (𝟙 U)
    ((𝟙 X) ≫ (𝟙 X)) (𝟙 X) j (Category.id_comp _) (Category.id_comp _) h' h M
  have hu := congr_app (gComp_id_left R φ (𝟙 U)) M
  have hx := congr_app (gComp_id_left R φ (𝟙 X)) ((J R φ j).obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu hx
  have hn := (alpha R φ j (𝟙 U) (𝟙 X) j h).naturality ((gId R φ U).hom.app M)
  simp only [Functor.comp_map] at hn
  rw [isoId_comm] at hn
  have ht' := congrArg (fun a ↦ a ≫
    (J R φ j).map ((gId R φ U).hom.app ((G R φ (𝟙 U)).obj M))) ht
  simp only [Category.assoc, ← Functor.map_comp, hu, hc] at ht'
  rw [← hn] at ht'
  apply (Functor.Faithful.of_iso (gId R φ X).symm).map_injective
  apply (cancel_epi ((gComp R φ (𝟙 X) (𝟙 X)).hom.app ((J R φ j).obj M))).1
  apply (cancel_mono ((alpha R φ j (𝟙 U) (𝟙 X) j h).app M)).1
  simpa only [Functor.map_comp, Category.assoc, isoId_comm, hx,
    Functor.id_obj, Functor.comp_obj] using ht'

section OpenUnits
private def moduleJId (X : Scheme.{u}) : extension R φ (𝟙 X) ≅ 𝟭 (Modules R φ X) :=
  Adjunction.leftAdjointIdIso (moduleJAdj R φ (𝟙 X)) (moduleGId R φ X)

private def derivedJId (X : Scheme.{u}) : J R φ (𝟙 X) ≅ 𝟭 (Derived R φ X) :=
  Functor.mapDerivedCategoryNatIso (moduleJId R φ X) ≪≫
    Functor.mapDerivedCategoryIdIso (Modules R φ X)

private theorem derived_id_fac {X : Scheme.{u}}
    (L : Modules R φ X ⥤ Modules R φ X)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ≅ 𝟭 _) (K : HomotopyCategory (Modules R φ X) (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
      Functor.mapDerivedCategoryIdIso (Modules R φ X)).hom.app (DerivedCategory.Qh.obj K) =
      L.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  exact Functor.mapDerivedCategoryNatIso_fach e K

private theorem jAdj_unit_fac (X : Scheme.{u})
    (K : HomotopyCategory (Modules R φ X) (.up ℤ)) :
    (jAdj R φ (𝟙 X)).unit.app (DerivedCategory.Qh.obj K) ≫
        (G R φ (𝟙 X)).map ((extension R φ (𝟙 X)).mapDerivedCategoryFactorsh.hom.app K) ≫
        (pull R φ (𝟙 X)).mapDerivedCategoryFactorsh.hom.app
          (((extension R φ (𝟙 X)).mapHomotopyCategory (.up ℤ)).obj K) =
      DerivedCategory.Qh.map
        (((moduleJAdj R φ (𝟙 X)).mapHomotopyCategory (.up ℤ)).unit.app K) := by
  let L := extension R φ (𝟙 X)
  let P := pull R φ (𝟙 X)
  let a := moduleJAdj R φ (𝟙 X)
  have hη : a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj K) ≫
      P.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
      P.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) :=
    (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso (Modules R φ X) (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom P.rightDerivedFunctorUnit K
  have hn := P.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have hr := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hr
  change (a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    P.rightDerivedFunctorIsoMapDerivedCategory.hom.app _) ≫
    P.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
    P.mapDerivedCategoryFactorsh.hom.app _ = _
  rw [Category.assoc, ← reassoc_of% hn, ← Category.assoc, hη, Category.assoc,
    ← Category.assoc (P.rightDerivedFunctorUnit.app _) _ _, hr,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

attribute [local irreducible] jAdj gId

private theorem derivedJId_transpose (X : Scheme.{u}) :
    (jAdj R φ (𝟙 X)).unit ≫
        Functor.whiskerRight (derivedJId R φ X).hom (G R φ (𝟙 X)) = (gId R φ X).inv := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules R φ X) (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  apply (cancel_mono ((gId R φ X).hom.app (DerivedCategory.Qh.obj K))).1
  erw [Iso.inv_hom_id_app, Category.assoc]
  change (jAdj R φ (𝟙 X)).unit.app _ ≫
    (pull R φ (𝟙 X)).mapDerivedCategory.map ((derivedJId R φ X).hom.app _) ≫
    (gId R φ X).hom.app _ = _
  erw [show (derivedJId R φ X).hom.app (DerivedCategory.Qh.obj K) = _ from
    derived_id_fac R φ _ (moduleJId R φ X) K]
  erw [Functor.map_comp]
  have hn := (gId R φ X).hom.naturality
    (DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (moduleJId R φ X).hom (.up ℤ)).app K))
  simp only [Functor.id_map] at hn
  simp only [Category.assoc]
  erw [hn]
  erw [show (gId R φ X).hom.app _ = _ from
    (by simpa only [gId, moduleGId] using
      derived_id_fac R φ _ (moduleGId R φ X) _)]
  erw [Category.assoc]
  erw [reassoc_of% (jAdj_unit_fac R φ X K)]
  erw [← Functor.map_comp, ← Functor.map_comp]
  have hk :
      ((moduleJAdj R φ (𝟙 X)).mapHomotopyCategory (.up ℤ)).unit.app K ≫
        (NatTrans.mapHomotopyCategory (moduleGId R φ X).hom (.up ℤ)).app
          (((extension R φ (𝟙 X)).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (NatTrans.mapHomotopyCategory (moduleJId R φ X).hom (.up ℤ)).app K = 𝟙 K := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ = _
    erw [← Functor.map_comp]
    rw [← (HomotopyCategory.quotient (Modules R φ X) (.up ℤ)).map_id K]
    apply (HomotopyCategory.quotient _ (.up ℤ)).congr_map
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.id_f]
    change (moduleJAdj R φ (𝟙 X)).unit.app (K.X n) ≫
      (moduleGId R φ X).hom.app ((extension R φ (𝟙 X)).obj (K.X n)) ≫
      (moduleJId R φ X).hom.app (K.X n) = 𝟙 _
    erw [← (moduleGId R φ X).hom.naturality ((moduleJId R φ X).hom.app (K.X n)),
      ← Category.assoc, StrictTower.leftAdjointIdIso_transpose]
    exact Iso.inv_hom_id_app _ _
  erw [hk]
  exact DerivedCategory.Qh.map_id _

private theorem jId_eq (X : Scheme.{u}) : jId R φ X = derivedJId R φ X := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((jAdj R φ (𝟙 X)).homEquiv M M).injective
  simp only [Adjunction.homEquiv_unit]
  change (jAdj R φ (𝟙 X)).unit.app M ≫
      (G R φ (𝟙 X)).map
        ((Adjunction.leftAdjointIdIso (jAdj R φ (𝟙 X)) (gId R φ X)).hom.app M) = _
  rw [StrictTower.leftAdjointIdIso_transpose]
  exact (congr_app (derivedJId_transpose R φ X) M).symm

private def jCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (e : f = g) : J R φ f ≅ J R φ g :=
  eqToIso (by cases e; rfl)

private theorem derivedJ_transport {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (e : f = g) :
    (Functor.mapDerivedCategoryNatIso (moduleJCongr R φ e)).hom =
      (jCongr R φ e).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

attribute [local irreducible] moduleJAdj moduleGId moduleJId

private theorem moduleJComp_id (X : Scheme.{u}) :
    (moduleJComp R φ (𝟙 X) (𝟙 X)).inv ≫
      Functor.whiskerRight (moduleJId R φ X).hom (extension R φ (𝟙 X)) =
        (moduleJCongr R φ (Category.id_comp (𝟙 X))).hom := by
  let K := {t : X ⟶ X // IsOpenImmersion t}
  let L : K → Modules R φ X ⥤ Modules R φ X := fun t ↦ @extension R φ _ _ t.1 t.2
  let P : K → Modules R φ X ⥤ Modules R φ X := fun t ↦ pull R φ t.1
  let a : ∀ t : K, L t ⊣ P t := fun t ↦ @moduleJAdj R φ _ _ t.1 t.2
  let ki : K := ⟨(𝟙 X) ≫ (𝟙 X), inferInstance⟩
  let kj : K := ⟨𝟙 X, inferInstance⟩
  have e : ki = kj := Subtype.ext (Category.id_comp _)
  have hd : (moduleGComp R φ (𝟙 X) (𝟙 X)).symm ≪≫
      eqToIso (congrArg (pull R φ) (Category.id_comp (𝟙 X))) =
    Functor.isoWhiskerLeft (pull R φ (𝟙 X)) (moduleGId R φ X) ≪≫
      Functor.rightUnitor (pull R φ (𝟙 X)) := by
    apply Iso.ext
    change (moduleGComp R φ (𝟙 X) (𝟙 X)).inv ≫
        (eqToIso (congrArg (pull R φ) (Category.id_comp (𝟙 X)))).hom =
      Functor.whiskerLeft (pull R φ (𝟙 X)) (moduleGId R φ X).hom
    apply (cancel_epi (moduleGComp R φ (𝟙 X) (𝟙 X)).hom).1
    rw [← Category.assoc, Iso.hom_inv_id]
    exact (Category.id_comp _).trans (moduleGComp_id_left R φ (𝟙 X)).symm
  unfold moduleJComp moduleJId
  exact StrictTower.leftAdjoint_unit_right L P a (moduleJAdj R φ (𝟙 X))
    (moduleGId R φ X) e (moduleGComp R φ (𝟙 X) (𝟙 X)).symm hd

private theorem jComp_id (X : Scheme.{u}) (M : Derived R φ X) :
    (jComp R φ (𝟙 X) (𝟙 X)).hom.app M ≫
        (jCongr R φ (Category.id_comp (𝟙 X))).hom.app M =
      (J R φ (𝟙 X)).map ((jId R φ X).hom.app M) := by
  have ht := StrictTower.derived_unit_right
    (extension R φ (𝟙 X)) (extension R φ ((𝟙 X) ≫ (𝟙 X)))
    (extension R φ (𝟙 X)) (moduleJComp R φ (𝟙 X) (𝟙 X)).symm
    (moduleJId R φ X) (moduleJCongr R φ (Category.id_comp (𝟙 X)))
    (moduleJComp_id R φ X)
  rw [Functor.mapDerivedCategoryNatIso_symm, derivedJ_transport] at ht
  have hh := congr_app ht M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hh
  simp only [← Category.assoc] at hh
  change (jComp R φ (𝟙 X) (𝟙 X)).inv.app M ≫
    (J R φ (𝟙 X)).map ((derivedJId R φ X).hom.app M) = _ at hh
  rw [← jId_eq] at hh
  exact StrictTower.iso_unit_cancel ((jComp R φ (𝟙 X) (𝟙 X)).app M) _ _ hh

end OpenUnits

private theorem alpha_open_congr {V W S T : Scheme.{u}}
    (k k' : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i i' : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion k'] [IsOpenImmersion i] [IsOpenImmersion i']
    [QuasiCompact k] [QuasiCompact k'] [QuasiCompact i] [QuasiCompact i']
    [IsProper r] [IsProper p]
    (hk : k = k') (hi : i = i') (h : k ≫ p = r ≫ i) (h' : k' ≫ p = r ≫ i')
    (M : Derived R φ S) :
    (G R φ p).map ((jCongr R φ hi).hom.app M) ≫
        (alpha R φ k' r p i' h').app M =
      (alpha R φ k r p i h).app M ≫ (jCongr R φ hk).hom.app ((G R φ r).obj M) := by
  cases hk
  cases hi
  simp [jCongr]

private theorem alpha_second {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ X) :
    (alpha R φ (𝟙 U) p p (𝟙 X) h).app M ≫
        (jId R φ U).hom.app ((G R φ p).obj M) =
      (G R φ p).map ((jId R φ X).hom.app M) := by
  have := alpha_isIso R φ (𝟙 U) p p (𝟙 X) h (IsPullback.of_id_fst (f := p))
  let h' : ((𝟙 U) ≫ (𝟙 U)) ≫ p = p ≫ ((𝟙 X) ≫ (𝟙 X)) := by simp
  have ht := alpha_horizontal R φ (𝟙 U) (𝟙 U) (𝟙 X) (𝟙 X) p p p h h h' M
  have hc := alpha_open_congr R φ ((𝟙 U) ≫ (𝟙 U)) (𝟙 U) p p
    ((𝟙 X) ≫ (𝟙 X)) (𝟙 X) (Category.id_comp _) (Category.id_comp _) h' h M
  have hn := (alpha R φ (𝟙 U) p p (𝟙 X) h).naturality ((jId R φ X).hom.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have ht' := congrArg (fun a ↦ a ≫
    (jCongr R φ (Category.id_comp (𝟙 U))).hom.app ((G R φ p).obj M)) ht
  simp only [Category.assoc, jComp_id] at ht'
  rw [← hc, ← Category.assoc, ← Functor.map_comp, jComp_id, hn] at ht'
  apply (Functor.Faithful.of_iso (jId R φ U).symm).map_injective
  apply (cancel_epi ((alpha R φ (𝟙 U) p p (𝟙 X) h).app ((J R φ (𝟙 X)).obj M))).1
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_obj] using ht'.symm

/-- Identity normalizations of the intrinsic inverse-image/open-extension arrow.
Source: Stacks 07A7, 0F7B; node proof Steps 5 and 11
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the identity square has the identity lift and its projection retains the
entire component. The unit normalization of beta and the identity compositors
therefore gives these equalities already on system complexes; localize them. -/
theorem alpha_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (alpha R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (J R φ j).map ((gId R φ U).hom.app M) =
        (gId R φ X).hom.app ((J R φ j).obj M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ X),
      (alpha R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (jId R φ U).hom.app ((G R φ p).obj M) =
        (G R φ p).map ((jId R φ X).hom.app M)) := by
  constructor
  · intro U X j _ _ h M
    exact alpha_first R φ j h M
  · intro U X p _ h M
    exact alpha_second R φ p h M

/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (gamma R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (pId R φ X).hom.app ((J R φ j).obj M) =
        (J R φ j).map ((pId R φ U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ U),
      (gamma R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (P R φ p).map ((jId R φ U).hom.app M) =
        (jId R φ X).hom.app ((P R φ p).obj M)) := by
  constructor
  · intro U X j _ _ h M
    let a := TwoSquare.mk _ _ _ _ (alpha R φ j (𝟙 U) (𝟙 X) j h)
    have ha : (a.whiskerLeft (gId R φ U).hom).whiskerRight
        (gId R φ X).inv = TwoSquare.vId (J R φ j) := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      dsimp [a, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vId]
      simpa [TwoSquare.mk, Category.assoc] using
        (congrArg (fun f ↦ (gId R φ X).inv.app ((J R φ j).obj N) ≫ f)
          ((alpha_identities R φ).1 j h N))
    have hm := congrArg (mateEquiv Adjunction.id Adjunction.id) ha
    rw [mateEquiv_conjugateEquiv_vcomp _ (adj R φ (𝟙 X)),
      conjugateEquiv_mateEquiv_vcomp _ (adj R φ (𝟙 U))] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    have hh : (J R φ j).map ((pId R φ U).inv.app M) ≫
        (gamma R φ j (𝟙 U) (𝟙 X) j h).app M ≫
        (pId R φ X).hom.app ((J R φ j).obj M) = 𝟙 _ := by
      simpa [a, gamma, pId, conjugateIsoEquiv, TwoSquare.whiskerTop,
        TwoSquare.whiskerBottom, TwoSquare.vId, mateEquiv, Adjunction.id] using hmM
    have hh' := congrArg (fun f ↦ (J R φ j).map ((pId R φ U).hom.app M) ≫ f) hh
    simpa [← Category.assoc, ← Functor.map_comp] using hh'
  · intro U X p _ h M
    let a := TwoSquare.mk _ _ _ _ (alpha R φ (𝟙 U) p p (𝟙 X) h)
    have ha : (a.whiskerTop (jId R φ X).inv).whiskerBottom
        (jId R φ U).hom = TwoSquare.hId (G R φ p) := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      dsimp [a, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hId]
      have hh := (alpha_identities R φ).2 p h N
      have hh' := congrArg
        (fun f ↦ (G R φ p).map ((jId R φ X).inv.app N) ≫ f) hh
      simpa [TwoSquare.mk, ← Functor.map_comp,
        Category.assoc] using hh'
    have hm := congrArg (mateEquiv (adj R φ p) (adj R φ p)) ha
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      Category.assoc] at hm
    rw [mate_whisker] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    have hh : (jId R φ X).inv.app ((P R φ p).obj M) ≫
        (gamma R φ (𝟙 U) p p (𝟙 X) h).app M ≫
        (P R φ p).map ((jId R φ U).hom.app M) = 𝟙 _ := by
      simpa [a, gamma, TwoSquare.hId, mateEquiv] using hmM
    have hh' := congrArg
      (fun f ↦ (jId R φ X).hom.app ((P R φ p).obj M) ≫ f) hh
    simpa only [← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, Category.comp_id] using hh'

section Evaluation
open WeilConjectures.SemilinearSections

private def evaluationOfMate
    {X Y x y : Type k} [Category.{k} X] [Category.{k} Y]
    [Category.{k} x] [Category.{k} y]
    (E : X ⥤ x) (F : Y ⥤ y)
    {L : X ⥤ Y} {P : Y ⥤ X} {l : x ⥤ y} {p : y ⥤ x}
    (a : L ⊣ P) (b : l ⊣ p) (e : L ⋙ F ≅ E ⋙ l)
    (v : P ⋙ E ≅ F ⋙ p)
    (hv : v.hom = (mateEquiv a b e.inv)) :
    AdjunctionEvaluation E F a b where
  left := e
  right := v
  unit A := by
    rw [hv]
    have hh := congrArg (fun z ↦ z ≫ p.map (e.hom.app A))
      (unit_mateEquiv a b e.inv A)
    simp only [Functor.id_obj, Category.assoc] at hh
    rw [← p.map_comp, Iso.inv_hom_id_app] at hh
    erw [p.map_id, Category.comp_id] at hh
    exact hh
  counit B := by
    rw [hv]
    exact mateEquiv_counit a b e.inv B

end Evaluation

end AlgebraicGeometry.ProEtale.VaryingRing
