/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.CategoryTheory.SmoothPurity.ClopenMateComposite
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization

/-! # Exact localization calculations for clopen mate comparisons

## References

* Stacks Project, Tags 015F and 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ w₁ w₂ h₁ h₂ u₁ u₂ u₃ u₄ v₃ v₄ w₃ w₄ v h w

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors

-- The localization equations explicitly unfold the ordinary quotient functor.
attribute [local semireducible] DerivedCategory.Q

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.Normalization

open SheafOfModules.OpenTensorNormalization in
private theorem exact_hom_fac
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [aF : F.Additive] [aG : G.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    (exactDerivedAdjunction a).homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  have hu : (exactDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [exactDerivedAdjunction, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

private def localize
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {F G : C ⥤ D} [aF : F.Additive] [aG : G.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

/-- Localize a square comparison and insert exactly the standard composition isomorphisms. -/
private def localizeSquare
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {B : Type v₁} [Category.{h₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {A : Type v₂} [Category.{h₂} A] [Abelian A] [HasDerivedCategory.{w₂} A]
    (F : C ⥤ D) (G : D ⥤ A) (H : C ⥤ B) (I : B ⥤ A)
    [aF : F.Additive] [aG : G.Additive] [aH : H.Additive] [aI : I.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    [lH : PreservesFiniteLimits H] [cH : PreservesFiniteColimits H]
    [lI : PreservesFiniteLimits I] [cI : PreservesFiniteColimits I] (a : F ⋙ G ⟶ H ⋙ I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).hom ≫ localize a ≫
    (Functor.mapDerivedCategoryCompIso H I).inv

private theorem chosen_adj_congr
    {A B : Type*} [Category A] [Category B]
    (P Q : B ⥤ A) [rP : P.IsRightAdjoint] [rQ : Q.IsRightAdjoint] (h : P = Q) :
    HEq (Adjunction.ofIsRightAdjoint P) (Adjunction.ofIsRightAdjoint Q) := by
  subst Q
  rfl

private theorem left_comp_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L L₁ : A ⥤ B} {R R₁ : B ⥤ A}
    {M M₁ : B ⥤ D} {S S₁ : D ⥤ B}
    {N N₁ : A ⥤ D} {T T₁ : D ⥤ A}
    (a : L ⊣ R) (a₁ : L₁ ⊣ R₁) (b : M ⊣ S) (b₁ : M₁ ⊣ S₁)
    (c : N ⊣ T) (c₁ : N₁ ⊣ T₁) (d : S ⋙ R ≅ T) (d₁ : S₁ ⋙ R₁ ≅ T₁)
    (eL : L = L₁) (eR : R = R₁) (eM : M = M₁) (eS : S = S₁)
    (eN : N = N₁) (eT : T = T₁)
    (ha : HEq a a₁) (hb : HEq b b₁) (hc : HEq c c₁) (hd : HEq d d₁) :
    HEq (Adjunction.leftAdjointCompIso a b c d)
      (Adjunction.leftAdjointCompIso a₁ b₁ c₁ d₁) := by
  subst L₁
  subst R₁
  subst M₁
  subst S₁
  subst N₁
  subst T₁
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

private theorem derived_functor_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B]
    (F G : A ⥤ B) [aF : F.Additive] [aG : G.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

private theorem derived_iso_heq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B]
    (F F' G G' : A ⥤ B) [aF : F.Additive] [aFp : F'.Additive] [aG : G.Additive] [aGp : G'.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lFp : PreservesFiniteLimits F'] [cFp : PreservesFiniteColimits F']
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    [lGp : PreservesFiniteLimits G'] [cGp : PreservesFiniteColimits G']
    (a : F ≅ G) (a' : F' ≅ G') (hF : F = F') (hG : G = G') (ha : HEq a a') :
    HEq (Functor.mapDerivedCategoryNatIso a) (Functor.mapDerivedCategoryNatIso a') := by
  subst F'
  subst G'
  cases ha
  rfl

private theorem comp_iso_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B] [dD : HasDerivedCategory D]
    (F F' : A ⥤ B) (G G' : B ⥤ D)
    [aF : F.Additive] [aFp : F'.Additive] [aG : G.Additive] [aGp : G'.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lFp : PreservesFiniteLimits F'] [cFp : PreservesFiniteColimits F']
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    [lGp : PreservesFiniteLimits G']
    [cGp : PreservesFiniteColimits G'] (hf : F = F') (hg : G = G') :
    HEq (Functor.mapDerivedCategoryCompIso F G) (Functor.mapDerivedCategoryCompIso F' G') := by
  subst F'
  subst G'
  rfl

private theorem trans_iso_heq
    {A : Type*} [Category A] {X X' Y Y' Z Z' : A}
    (a : X ≅ Y) (a' : X' ≅ Y') (b : Y ≅ Z) (b' : Y' ≅ Z')
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (ha : HEq a a') (hb : HEq b b') :
    HEq (a ≪≫ b) (a' ≪≫ b') := by
  subst X'
  subst Y'
  subst Z'
  cases ha
  cases hb
  rfl

private theorem inverse_mate_localized
    {A : Type u₁} {B : Type u₂} {D : Type u₃} {F : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D] [Category.{v₄} F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} D] [HasDerivedCategory.{w₄} F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ F}
    [aL₁ : L₁.Additive] [aR₁ : R₁.Additive] [aL₂ : L₂.Additive] [aR₂ : R₂.Additive]
    [aG : G.Additive] [aH : H.Additive]
    [lL₁ : PreservesFiniteLimits L₁] [cL₁ : PreservesFiniteColimits L₁]
    [lR₁ : PreservesFiniteLimits R₁] [cR₁ : PreservesFiniteColimits R₁]
    [lL₂ : PreservesFiniteLimits L₂] [cL₂ : PreservesFiniteColimits L₂]
    [lR₂ : PreservesFiniteLimits R₂] [cR₂ : PreservesFiniteColimits R₂]
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    [lH : PreservesFiniteLimits H] [cH : PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    (β : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hβ : ∀ M, a₂.unit.app (G.obj M) ≫ R₂.map (β.hom.app M) =
      G.map (a₁.unit.app M) ≫ d.hom.app (L₁.obj M)) :
    ((mateEquiv (exactLocalizationDerivedAdjunction a₁)
      (exactLocalizationDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)) =
      (Functor.mapDerivedCategorySquareIso β).hom := by
  have he : ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)) = β.hom := by
    apply NatTrans.ext
    funext M
    apply (a₂.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ d.hom) M).symm.trans
      (hβ M).symm
  have : IsIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)) := by
    rw [he]
    infer_instance
  have hh := (exact_localization_inverse_mate a₁ a₂ d).2.1
  have hi : asIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)) = β :=
    Iso.ext he
  rw [hi] at hh
  exact hh

private theorem map_derived_transport
    {A B I : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B]
    (F : I → A ⥤ B) [∀ j, (F j).Additive]
    [∀ j, PreservesFiniteLimits (F j)] [∀ j, PreservesFiniteColimits (F j)]
    {j k : I} (h : j = k) :
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h))).hom =
      (eqToIso (congrArg (fun j ↦ (F j).mapDerivedCategory) h)).hom := by
  cases h
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem iso_word_heq
    {A I : Type*} [Category A] (F F' : I → A) {j k : I} (h : j = k)
    {X X' Y Y' : A} (a : F j ≅ X) (a' : F' j ≅ X')
    (b : F k ≅ Y) (b' : F' k ≅ Y') (hF : F = F') (hX : X = X') (hY : Y = Y')
    (ha : HEq a a') (hb : HEq b b') :
    HEq (a.symm ≪≫ eqToIso (congrArg F h) ≪≫ b)
      (a'.symm ≪≫ eqToIso (congrArg F' h) ≪≫ b') := by
  subst F'
  subst X'
  subst Y'
  cases ha
  cases hb
  rfl

private theorem chosen_exact_adjunction_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B]
    (P Q : A ⥤ B) [rP : P.IsRightAdjoint] [rQ : Q.IsRightAdjoint]
    [aP : P.Additive] [aQ : Q.Additive] [aLP : P.leftAdjoint.Additive]
    [aLQ : Q.leftAdjoint.Additive]
    [lP : PreservesFiniteLimits P] [cP : PreservesFiniteColimits P]
    [lQ : PreservesFiniteLimits Q] [cQ : PreservesFiniteColimits Q]
    [lLP : PreservesFiniteLimits P.leftAdjoint]
    [cLP : PreservesFiniteColimits P.leftAdjoint]
    [lLQ : PreservesFiniteLimits Q.leftAdjoint]
    [cLQ : PreservesFiniteColimits Q.leftAdjoint]
    (h : P = Q) :
    HEq (Adjunction.ofIsRightAdjoint P).mapExactDerivedCategory
      (Adjunction.ofIsRightAdjoint Q).mapExactDerivedCategory := by
  subst Q
  rfl

private theorem inverse_mate_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (δ : R₁ ⋙ G ⟶ H ⋙ R₂) (δ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (e₁ : L₁ = L₁') (e₂ : R₁ = R₁') (e₃ : L₂ = L₂') (e₄ : R₂ = R₂')
    (e₅ : G = G') (e₆ : H = H') (ha : HEq a a') (hb : HEq b b') (hδ : HEq δ δ') :
    HEq ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δ))
      ((mateEquiv a' b').symm (TwoSquare.mk _ _ _ _ δ')) := by
  subst L₁'
  subst R₁'
  subst L₂'
  subst R₂'
  subst G'
  subst H'
  cases ha
  cases hb
  cases hδ
  rfl

private theorem iso_inv_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y') (he : HEq e e') :
    HEq e.inv e'.inv := by
  subst X'
  subst Y'
  cases he
  rfl

private theorem iso_hom_of_inv_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y')
    (he : HEq e.inv e'.inv) : HEq e.hom e'.hom := by
  subst X'
  subst Y'
  exact congrArg Iso.hom (Iso.ext_inv (eq_of_heq he)) |>.heq

private theorem square_symm_hom
    {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B]
    [dD : HasDerivedCategory D] [dF : HasDerivedCategory F]
    {L₁ : A ⥤ B} {L₂ : B ⥤ F} {R₁ : A ⥤ D} {R₂ : D ⥤ F}
    [aL₁ : L₁.Additive] [aL₂ : L₂.Additive] [aR₁ : R₁.Additive] [aR₂ : R₂.Additive]
    [lL₁ : PreservesFiniteLimits L₁] [cL₁ : PreservesFiniteColimits L₁]
    [lL₂ : PreservesFiniteLimits L₂] [cL₂ : PreservesFiniteColimits L₂]
    [lR₁ : PreservesFiniteLimits R₁] [cR₁ : PreservesFiniteColimits R₁]
    [lR₂ : PreservesFiniteLimits R₂] [cR₂ : PreservesFiniteColimits R₂]
    (e : L₁ ⋙ L₂ ≅ R₁ ⋙ R₂) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc, Iso.symm_inv]

private theorem unit_homEquiv_symm
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {M : A} {N : B} (f : M ⟶ R.obj N) :
    a.unit.app M ≫ R.map ((a.homEquiv M N).symm f) = f := by
  simpa only [Adjunction.homEquiv_unit] using (a.homEquiv M N).apply_symm_apply f

private theorem inverse_mate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (δ : TwoSquare R₁ H G R₂) (M : A) :
    ((mateEquiv a b).symm δ).app M = (b.homEquiv _ _).symm
      (G.map (a.unit.app M) ≫ δ.app (L₁.obj M)) := by
  apply (b.homEquiv (G.obj M) (H.obj (L₁.obj M))).injective
  calc
    _ = G.map (a.unit.app M) ≫ δ.app (L₁.obj M) := by
      rw [Adjunction.homEquiv_unit]
      exact (unit_mateEquiv_symm a b δ M).symm
    _ = _ := ((b.homEquiv _ _).apply_symm_apply _).symm

private theorem left_comp_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') (M : A) :
    (a.comp b).homEquiv M _ ((Adjunction.leftAdjointCompIso a b c η).hom.app M) ≫
      η.hom.app (L''.obj M) = c.unit.app M := by
  rw [Adjunction.homEquiv_unit, Category.assoc, η.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c η).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← R''.map_comp, Iso.inv_hom_id_app, R''.map_id]
  exact Category.comp_id _

private theorem left_comp_unique
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') :
    ((a.comp b).ofNatIsoRight η).leftAdjointUniq c =
      Adjunction.leftAdjointCompIso a b c η := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (((a.comp b).ofNatIsoRight η).homEquiv M _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  exact (left_comp_unit a b c η M).symm

/-- Exact localization carries the left-adjoint composition comparison to the
composition comparison of the exact localized adjunctions. -/
theorem open_comp_localized
    {A B D : Type v₁} [Category.{h₁} A] [Category.{h₁} B] [Category.{h₁} D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₁} B]
    [HasDerivedCategory.{w₁} D]
    {F : A ⥤ B} {P : B ⥤ A} {G : B ⥤ D} {Q : D ⥤ B}
    {H : A ⥤ D} {T : D ⥤ A}
    [F.Additive] [P.Additive] [G.Additive] [Q.Additive] [H.Additive] [T.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : F ⊣ P) (b : G ⊣ Q) (c : H ⊣ T) (e : Q ⋙ P ≅ T) :
    Adjunction.leftAdjointCompIso (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a)
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction b)
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction c)
      (Functor.exactDerivedRestrictionComposition Q P T e) =
        Functor.mapDerivedCategoryCompIso F G ≪≫
          Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointCompIso a b c e) := by
  let ac := a.mapHomologicalComplex (.up ℤ)
  let bc := b.mapHomologicalComplex (.up ℤ)
  let dc := c.mapHomologicalComplex (.up ℤ)
  let η := e
  let ηc := Functor.mapHomologicalComplexCompIso η (.up ℤ)
  let ν := Adjunction.leftAdjointCompIso a b c e
  let νc := Functor.mapHomologicalComplexCompIso ν (.up ℤ)
  have hn : ∀ K, (ac.comp bc).homEquiv _ _ (νc.hom.app K) ≫
      ηc.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        dc.unit.app K := by
    intro K
    apply HomologicalComplex.hom_ext
    intro i
    have h := left_comp_unit a b c η
      (K.X i)
    rw [Adjunction.homEquiv_unit] at h ⊢
    exact h
  have hcomp := normalizedAdjunction_composition ac bc
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction b)
    F.mapDerivedCategoryFactors.hom
    G.mapDerivedCategoryFactors.hom
    P.mapDerivedCategoryFactors.inv Q.mapDerivedCategoryFactors.inv
    (exact_hom_fac a)
    (exact_hom_fac b)
  have he (K : CochainComplex A ℤ) := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q) (ac.comp bc) dc
    ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).comp
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction b))
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction c)
    (fun K ↦ G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))
    H.mapDerivedCategoryFactors.hom.app
    (fun L ↦ P.mapDerivedCategoryFactors.inv.app
      ((Q.mapHomologicalComplex (.up ℤ)).obj L) ≫
      P.mapDerivedCategory.map (Q.mapDerivedCategoryFactors.inv.app L))
    T.mapDerivedCategoryFactors.inv.app
    (by intros P L f; simpa only [Category.assoc] using hcomp P L f)
    (exact_hom_fac c)
    ηc (Functor.exactDerivedRestrictionComposition Q P T e) νc.hom.app hn
    (by
      intro L
      have hv : ηc.hom.app L = (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app L := by
        ext i
        rfl
      rw [hv]
      simpa only [Functor.comp_obj, η, Functor.exactDerivedRestrictionComposition,
        Category.assoc] using
        (Functor.exactDerivedRestrictionComposition_inv_factors Q P T η L)) K
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  rw [← cancel_mono (H.mapDerivedCategoryFactors.hom.app K)]
  have hk := he K
  rw [left_comp_unique] at hk
  change (Adjunction.leftAdjointCompIso
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction b)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction c)
    (Functor.exactDerivedRestrictionComposition Q P T e)).hom.app
      (DerivedCategory.Q.obj K) ≫ _ = _ at hk
  rw [hk]
  have hv : νc.hom.app K = (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app K := by
    ext i
    rfl
  rw [hv]
  simpa only [Category.assoc, ν,
    Functor.exactDerivedRestrictionComposition] using
    (Functor.exactDerivedRestrictionComposition_hom_factors
      F G H ν K).symm

private theorem localize_fac
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B] {F G : A ⥤ B}
    [aF : F.Additive] [aG : G.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (localize a).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  simp only [localize, Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem adjunction_on_complexes_unit
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [dA : HasDerivedCategory A] [dD : HasDerivedCategory D]
    {L : A ⥤ D} {R : D ⥤ A} [aL : L.Additive] [aR : R.Additive]
    [lL : PreservesFiniteLimits L] [cL : PreservesFiniteColimits L]
    [lR : PreservesFiniteLimits R] [cR : PreservesFiniteColimits R]
    (a : L ⊣ R) (K : CochainComplex A ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) :=
by
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
  change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
    R.mapDerivedCategoryFactors.inv.app _ ≫
    R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K)) ≫
    R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app _ = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

private theorem projector_restriction_descent
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [dA : HasDerivedCategory A] [dD : HasDerivedCategory D]
    (F : A ⥤ D) (H : D ⥤ A) [aF : F.Additive] [aH : H.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lH : PreservesFiniteLimits H] [cH : PreservesFiniteColimits H]
    (a : H ⊣ F) (p : 𝟭 A ⟶ F ⋙ H)
    (d : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (hd : ∀ K : CochainComplex A ℤ,
      d.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K)) :
    ∀ M, F.mapDerivedCategory.map (d.app M) =
      (a.mapExactDerivedCategory).unit.app (F.mapDerivedCategory.obj M) := by
  have he : Functor.whiskerRight d F.mapDerivedCategory =
      Functor.whiskerLeft F.mapDerivedCategory (a.mapExactDerivedCategory).unit := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    change F.mapDerivedCategory.map (d.app (DerivedCategory.Q.obj K)) =
      (a.mapExactDerivedCategory).unit.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K))
    apply (cancel_mono
      (F.mapDerivedCategory.map
        (H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj K)))).1
    erw [← F.mapDerivedCategory.map_comp_assoc, hd,
      Functor.mapDerivedCategoryFactors_hom_naturality]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (a.mapExactDerivedCategory).unit.naturality (F.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    erw [← reassoc_of% hn, adjunction_on_complexes_unit]
    congr 2
    apply HomologicalComplex.hom_ext
    intro n
    exact hp (K.X n)
  intro M
  exact NatTrans.congr_app he M

private theorem localized_projector
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [dA : HasDerivedCategory A] [dD : HasDerivedCategory D]
    (F : A ⥤ D) (H : D ⥤ A) [aF : F.Additive] [aH : H.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lH : PreservesFiniteLimits H] [cH : PreservesFiniteColimits H]
    (a : H ⊣ F) (R : DerivedCategory D ⥤ DerivedCategory A)
    (b : F.mapDerivedCategory ⊣ R) (t : H.mapDerivedCategory ⟶ R) [IsIso t]
    (p : 𝟭 A ⟶ F ⋙ H)
    (e : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (he : ∀ M, F.mapDerivedCategory.map (e.app M) =
      a.mapExactDerivedCategory.unit.app (F.mapDerivedCategory.obj M)) :
    (Functor.mapDerivedCategoryIdIso A).inv ≫ localize p ≫
      (Functor.mapDerivedCategoryCompIso F H).inv = e := by
  apply StrictTower.projector_unique b t
  have hd := projector_restriction_descent F H a p
    ((Functor.mapDerivedCategoryIdIso A).inv ≫ localize p ≫
      (Functor.mapDerivedCategoryCompIso F H).inv) hp (fun K ↦ ?_)
  · intro M
    exact (hd M).trans (he M).symm
  · simp only [NatTrans.comp_app, Category.assoc]
    erw [Functor.mapDerivedCategoryCompIso_hom_app_factors, localize_fac]
    rw [← Functor.mapDerivedCategoryIdIso_hom_app_Q_obj]
    erw [Iso.inv_hom_id_app_assoc]

private theorem localized_projector_heq
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [dA : HasDerivedCategory A] [dD : HasDerivedCategory D]
    (F F' : A ⥤ D) (H H' : D ⥤ A)
    [aF : F.Additive] [aFp : F'.Additive] [aH : H.Additive] [aHp : H'.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lFp : PreservesFiniteLimits F'] [cFp : PreservesFiniteColimits F']
    [lH : PreservesFiniteLimits H] [cH : PreservesFiniteColimits H]
    [lHp : PreservesFiniteLimits H'] [cHp : PreservesFiniteColimits H']
    (a : H ⊣ F) (a' : H' ⊣ F') (R : DerivedCategory D ⥤ DerivedCategory A)
    (b : F'.mapDerivedCategory ⊣ R) (t : H'.mapDerivedCategory ⟶ R) [inst : IsIso t]
    (p : 𝟭 A ⟶ F ⋙ H)
    (e : 𝟭 (DerivedCategory A) ⟶ F'.mapDerivedCategory ⋙ H'.mapDerivedCategory)
    (hF : F = F') (hH : H = H') (ha : HEq a a')
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (he : ∀ M, F'.mapDerivedCategory.map (e.app M) =
      a'.mapExactDerivedCategory.unit.app (F'.mapDerivedCategory.obj M)) :
    HEq ((Functor.mapDerivedCategoryIdIso A).inv ≫ localize p ≫
      (Functor.mapDerivedCategoryCompIso F H).inv) e := by
  subst F'
  subst H'
  cases ha
  exact (localized_projector F H a R b t p e hp he).heq

private theorem symm_iso_heq
    {A B : Type*} [Category A] [Category B] {F F' G G' : A ⥤ B}
    (e : F ≅ G) (e' : F' ≅ G') (hF : F = F') (hG : G = G') (he : HEq e e') :
    HEq e.symm e'.symm := by
  subst F'
  subst G'
  cases he
  rfl

private theorem localized_comp_iso_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B] [dD : HasDerivedCategory D]
    (F F' : A ⥤ B) (G G' : B ⥤ D) (H H' : A ⥤ D)
    [aF : F.Additive] [aFp : F'.Additive] [aG : G.Additive] [aGp : G'.Additive]
    [aH : H.Additive] [aHp : H'.Additive]
    [lF : PreservesFiniteLimits F] [cF : PreservesFiniteColimits F]
    [lFp : PreservesFiniteLimits F'] [cFp : PreservesFiniteColimits F']
    [lG : PreservesFiniteLimits G] [cG : PreservesFiniteColimits G]
    [lGp : PreservesFiniteLimits G'] [cGp : PreservesFiniteColimits G']
    [lH : PreservesFiniteLimits H] [cH : PreservesFiniteColimits H]
    [lHp : PreservesFiniteLimits H'] [cHp : PreservesFiniteColimits H']
    (e : F ⋙ G ≅ H) (e' : F' ⋙ G' ≅ H')
    (hF : F = F') (hG : G = G') (hH : H = H') (he : HEq e e') :
    HEq (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e)
      (Functor.mapDerivedCategoryCompIso F' G' ≪≫
        Functor.mapDerivedCategoryNatIso e') := by
  subst F'
  subst G'
  subst H'
  cases he
  rfl

private theorem hom_iso_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y') (he : HEq e e') :
    HEq e.hom e'.hom := by
  subst X'
  subst Y'
  cases he
  rfl

private theorem expanded_clopen_composite
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : I ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) :
    β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) B₀ ≫
      Functor.whiskerRight (Functor.associator Q S J).inv B₀ ≫
      (Functor.associator (Q ⋙ S) J B₀).hom ≫ Functor.whiskerLeft (Q ⋙ S) c ≫
      Functor.whiskerRight d K = clopenMateComposite I P Q S J B₀ K R β π c d := by
  apply NatTrans.ext
  funext M
  simp only [clopenMateComposite_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]
  erw [B₀.map_id]
  simp only [Category.id_comp]

private theorem clopen_composite_localized
    (C : Fin 5 → Type v₁) [∀ i, Category.{h₁} (C i)]
    [∀ i, Abelian (C i)] [∀ i, HasDerivedCategory.{w₁} (C i)]
    (I : C 0 ⥤ₑ C 4) (P : C 4 ⥤ₑ C 3) (Q : C 0 ⥤ₑ C 1)
    (S : C 1 ⥤ₑ C 2) (J : C 2 ⥤ₑ C 1) (B : C 1 ⥤ₑ C 3)
    (K : C 2 ⥤ₑ C 3) (R : C 0 ⥤ₑ C 2)
    [aI : I.obj.Additive] [aP : P.obj.Additive] [aQ : Q.obj.Additive] [aS : S.obj.Additive]
    [aJ : J.obj.Additive] [aB : B.obj.Additive] [aK : K.obj.Additive] [aR : R.obj.Additive]
    (β : I.obj ⋙ P.obj ⟶ Q.obj ⋙ B.obj) (π : 𝟭 (C 1) ⟶ S.obj ⋙ J.obj)
    (c : J.obj ⋙ B.obj ⟶ K.obj) (d : Q.obj ⋙ S.obj ⟶ R.obj) :
    localizeSquare I.obj P.obj R.obj K.obj
      (clopenMateComposite I.obj P.obj Q.obj S.obj J.obj B.obj K.obj R.obj β π c d) =
    clopenMateComposite I.obj.mapDerivedCategory P.obj.mapDerivedCategory
      Q.obj.mapDerivedCategory S.obj.mapDerivedCategory J.obj.mapDerivedCategory
      B.obj.mapDerivedCategory K.obj.mapDerivedCategory R.obj.mapDerivedCategory
      (localizeSquare I.obj P.obj Q.obj B.obj β)
      ((Functor.mapDerivedCategoryIdIso (C 1)).inv ≫ localize π ≫
        (Functor.mapDerivedCategoryCompIso S.obj J.obj).inv)
      ((Functor.mapDerivedCategoryCompIso J.obj B.obj).hom ≫ localize c)
      ((Functor.mapDerivedCategoryCompIso Q.obj S.obj).hom ≫ localize d) := by
  let wi := ExactDerivedPasting.Word.edge I
  let wp := ExactDerivedPasting.Word.edge P
  let wq := ExactDerivedPasting.Word.edge Q
  let ws := ExactDerivedPasting.Word.edge S
  let wj := ExactDerivedPasting.Word.edge J
  let wb := ExactDerivedPasting.Word.edge B
  let wk := ExactDerivedPasting.Word.edge K
  let wr := ExactDerivedPasting.Word.edge R
  let e : ExactDerivedPasting.Expression C (.comp wi wp) (.comp wr wk) :=
    .vcomp (.cell (P := .comp wi wp) (R := .comp wq wb) β) (.vcomp (.output (.rightUnitInv wq) wb)
      (.vcomp (.output (.input wq (.cell (P := .nil 1) (R := .comp ws wj) π)) wb)
      (.vcomp (.output (.assocInv wq ws wj) wb)
        (.vcomp (.assoc (.comp wq ws) wj wb)
          (.vcomp (.input (.comp wq ws) (.cell (P := .comp wj wb) (R := wk) c))
            (.output (.cell (P := .comp wq ws) (R := wr) d) wk))))))
  have he := (ExactDerivedPasting.exact_derived_transformation_pasting C).1 e
  have ho : e.ordinary =
      clopenMateComposite I.obj P.obj Q.obj S.obj J.obj B.obj K.obj R.obj β π c d :=
    by
      dsimp only [e, ExactDerivedPasting.Expression.ordinary,
        ExactDerivedPasting.Word.ordinary, wi, wp, wq, ws, wj, wb, wk, wr]
      apply NatTrans.ext
      funext M
      simp only [ExactFunctor.of_fst, clopenMateComposite_app, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app,
        Functor.rightUnitor_inv_app, Functor.comp_obj, Category.id_comp]
      erw [B.obj.map_id, B.obj.map_id]
      simp only [Category.id_comp]
  rw [ho] at he
  apply NatTrans.ext
  funext M
  have heM := congrArg (fun t ↦ t.app M) he.symm
  simp only [e, wi, wp, wq, ws, wj, wb, wk, wr,
    ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
    ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
    ExactDerivedPasting.Word.derived, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp, ExactFunctor.of_fst,
    Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    localizeSquare, localize, clopenMateComposite_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.comp_obj,
    Category.assoc] at heM ⊢
  erw [B.obj.mapDerivedCategory.map_id, Category.id_comp,
    B.obj.mapDerivedCategory.map_id, Category.id_comp] at heM
  exact heM

private theorem clopen_composite_heq
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I I' : A ⥤ E) (P P' : E ⥤ D) (Q Q' : A ⥤ B) (S S' : B ⥤ C)
    (J J' : C ⥤ B) (B₀ B₀' : B ⥤ D) (K K' : C ⥤ D) (R R' : A ⥤ C)
    (β : I ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R)
    (β' : I' ⋙ P' ⟶ Q' ⋙ B₀') (π' : 𝟭 B ⟶ S' ⋙ J')
    (c' : J' ⋙ B₀' ⟶ K') (d' : Q' ⋙ S' ⟶ R')
    (hI : I = I') (hP : P = P') (hQ : Q = Q') (hS : S = S')
    (hJ : J = J') (hB : B₀ = B₀') (hK : K = K') (hR : R = R')
    (hβ : HEq β β') (hπ : HEq π π') (hc : HEq c c') (hd : HEq d d') :
    HEq (clopenMateComposite I P Q S J B₀ K R β π c d)
      (clopenMateComposite I' P' Q' S' J' B₀' K' R' β' π' c' d') := by
  subst I'
  subst P'
  subst Q'
  subst S'
  subst J'
  subst B₀'
  subst K'
  subst R'
  cases hβ
  cases hπ
  cases hc
  cases hd
  rfl

section

private theorem map_iso_word
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} (e : X ≅ Y) {Z W : B} (d : F.obj Y ≅ Z) (u : W ⟶ Z) :
    u ≫ d.inv ≫ F.map e.inv ≫ F.map e.hom ≫ d.hom = u := by
  rw [← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp,
    d.inv_hom_id, Category.comp_id]

private theorem exact_adjunction_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [aL : L.Additive] [aR : R.Additive]
    [lL : PreservesFiniteLimits L] [cL : PreservesFiniteColimits L]
    [lR : PreservesFiniteLimits R] [cR : PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = exactLocalizationDerivedAdjunction a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  let K' := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hs : (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    change (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Qh.obj K') ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') = _
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc]
    erw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K'
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj K') ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K') = _ at hu
    erw [reassoc_of% hu]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj K')
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [← Category.assoc (R.rightDerivedFunctorUnit.app _), hf,
      Iso.inv_hom_id_app, Category.comp_id]
  have he : (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    have hl := StrictTower.ConstantNormalization.factorsh_hom L K
    have hr := StrictTower.ConstantNormalization.factorsh_hom R
      ((L.mapHomologicalComplex (.up ℤ)).obj K)
    change L.mapDerivedCategoryFactorsh.hom.app K' = _ at hl
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K') = _ at hr
    have hmap : DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
      dsimp only [K']
      rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      rfl
    erw [hl, hr, ← hmap, CategoryTheory.exact_unit_app]
    convert map_iso_word R.mapDerivedCategory (L.mapDerivedCategoryFactors.app K)
      (R.mapDerivedCategoryFactors.app ((L.mapHomologicalComplex (.up ℤ)).obj K))
      (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K)) using 1
    simp only [Category.assoc]
    rfl
  exact (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K'))).mp
    (by
      have hh := hs.trans he.symm
      simp only [Functor.comp_obj] at hh
      convert hh using 1 <;> rfl)

end

private theorem derived_adj_heq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    [aL : L.Additive] [aLp : L'.Additive] [aR : R.Additive] [aRp : R'.Additive]
    [lL : PreservesFiniteLimits L] [lLp : PreservesFiniteLimits L']
    [cL : PreservesFiniteColimits L] [cLp : PreservesFiniteColimits L']
    (a : L ⊣ R) (a' : L' ⊣ R') (hL : L = L') (hR : R = R') (ha : HEq a a') :
    HEq a.mapDerivedCategoryRightDerivedAdjunction
      a'.mapDerivedCategoryRightDerivedAdjunction := by
  subst L'
  subst R'
  cases ha
  rfl

private theorem mate_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : L₁ ⊣ R₁) (a' : L₁' ⊣ R₁') (b : L₂ ⊣ R₂) (b' : L₂' ⊣ R₂')
    (δ : G ⋙ L₂ ⟶ L₁ ⋙ H) (δ' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (e₁ : L₁ = L₁') (e₂ : R₁ = R₁') (e₃ : L₂ = L₂') (e₄ : R₂ = R₂')
    (e₅ : G = G') (e₆ : H = H') (ha : HEq a a') (hb : HEq b b') (hδ : HEq δ δ') :
    HEq (mateEquiv a b (TwoSquare.mk _ _ _ _ δ))
      (mateEquiv a' b' (TwoSquare.mk _ _ _ _ δ')) := by
  subst L₁'
  subst R₁'
  subst L₂'
  subst R₂'
  subst G'
  subst H'
  cases ha
  cases hb
  cases hδ
  rfl

private theorem left_id_heq
    {A : Type*} [Category A] {L L' R R' : A ⥤ A}
    (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ 𝟭 A) (e' : R' ≅ 𝟭 A)
    (hL : L = L') (hR : R = R') (ha : HEq a a') (he : HEq e e') :
    HEq (Adjunction.leftAdjointIdIso a e) (Adjunction.leftAdjointIdIso a' e') := by
  subst L'
  subst R'
  cases ha
  cases he
  rfl

private theorem conjugate_iso_heq
    {A B : Type*} [Category A] [Category B]
    {L L' M M' : A ⥤ B} {R R' S S' : B ⥤ A}
    (a : L ⊣ R) (a' : L' ⊣ R') (b : M ⊣ S) (b' : M' ⊣ S')
    (e : M ≅ L) (e' : M' ≅ L')
    (hL : L = L') (hR : R = R') (hM : M = M') (hS : S = S')
    (ha : HEq a a') (hb : HEq b b') (he : HEq e e') :
    HEq (conjugateIsoEquiv a b e) (conjugateIsoEquiv a' b' e') := by
  subst L'
  subst R'
  subst M'
  subst S'
  cases ha
  cases hb
  cases he
  rfl

private theorem identity_left_transfer
    {A B : Type*} [Category A] [Category B]
    (I I' : A ⥤ B) (R R' : A ⥤ A) (S S' : B ⥤ B)
    (t : R ⋙ I ⟶ I ⋙ S) (t' : R' ⋙ I' ⟶ I' ⋙ S')
    (a : R ≅ 𝟭 A) (a' : R' ≅ 𝟭 A) (b : S ≅ 𝟭 B) (b' : S' ≅ 𝟭 B)
    (hI : I = I') (hR : R = R') (hS : S = S')
    (ht : HEq t t') (ha : HEq a a') (hb : HEq b b')
    (h : ∀ M, t'.app M ≫ b'.hom.app (I'.obj M) = I'.map (a'.hom.app M)) :
    ∀ M, t.app M ≫ b.hom.app (I.obj M) = I.map (a.hom.app M) := by
  subst I'
  subst R'
  subst S'
  cases ht
  cases ha
  cases hb
  exact h

private theorem identity_right_transfer
    {A B : Type*} [Category A] [Category B]
    (R R' : A ⥤ B) (I I' : A ⥤ A) (J J' : B ⥤ B)
    (t : R ⋙ J ⟶ I ⋙ R) (t' : R' ⋙ J' ⟶ I' ⋙ R')
    (a : I ≅ 𝟭 A) (a' : I' ≅ 𝟭 A) (b : J ≅ 𝟭 B) (b' : J' ≅ 𝟭 B)
    (hR : R = R') (hI : I = I') (hJ : J = J')
    (ht : HEq t t') (ha : HEq a a') (hb : HEq b b')
    (h : ∀ M, t'.app M ≫ R'.map (a'.hom.app M) = b'.hom.app (R'.obj M)) :
    ∀ M, t.app M ≫ R.map (a.hom.app M) = b.hom.app (R.obj M) := by
  subst R'
  subst I'
  subst J'
  cases ht
  cases ha
  cases hb
  exact h
private theorem vertical_transfer
    {A B C D E F : Type*}
    [Category A]
    [Category B]
    [Category C]
    [Category D]
    [Category E]
    [Category F]
    (jk jk' : A ⥤ B)
    (ji ji' : C ⥤ D)
    (jj jj' : E ⥤ F)
    (r1 r1' : A ⥤ C)
    (r2 r2' : C ⥤ E)
    (r r' : A ⥤ E)
    (p1 p1' : B ⥤ D)
    (p2 p2' : D ⥤ F)
    (p p' : B ⥤ F)
    (g1 : r1 ⋙ ji ⟶ jk ⋙ p1) (g1' : r1' ⋙ ji' ⟶ jk' ⋙ p1')
    (g2 : r2 ⋙ jj ⟶ ji ⋙ p2) (g2' : r2' ⋙ jj' ⟶ ji' ⋙ p2')
    (g : r ⋙ jj ⟶ jk ⋙ p) (g' : r' ⋙ jj' ⟶ jk' ⋙ p')
    (cr : r1 ⋙ r2 ≅ r) (cr' : r1' ⋙ r2' ≅ r')
    (cp : p1 ⋙ p2 ≅ p) (cp' : p1' ⋙ p2' ≅ p')
    (hjk : jk = jk')
    (hji : ji = ji')
    (hjj : jj = jj')
    (hr1 : r1 = r1')
    (hr2 : r2 = r2')
    (hr : r = r')
    (hp1 : p1 = p1')
    (hp2 : p2 = p2')
    (hp : p = p')
    (hg1 : HEq g1 g1')
    (hg2 : HEq g2 g2')
    (hg : HEq g g')
    (hcr : HEq cr cr')
    (hcp : HEq cp cp')
    (h : ∀ M : A, jj'.map (cr'.hom.app M) ≫ g'.app M ≫ cp'.inv.app (jk'.obj M) =
      g2'.app (r1'.obj M) ≫ p2'.map (g1'.app M)) :
    ∀ M : A, jj.map (cr.hom.app M) ≫ g.app M ≫ cp.inv.app (jk.obj M) =
      g2.app (r1.obj M) ≫ p2.map (g1.app M) := by
  subst jk'
  subst ji'
  subst jj'
  subst r1'
  subst r2'
  subst r'
  subst p1'
  subst p2'
  subst p'
  cases hg1
  cases hg2
  cases hg
  cases hcr
  cases hcp
  exact h

private theorem horizontal_transfer
    {A B C D E F : Type*}
    [Category A]
    [Category B]
    [Category C]
    [Category D]
    [Category E]
    [Category F]
    (jk jk' : A ⥤ B)
    (jl jl' : B ⥤ E)
    (ji ji' : C ⥤ D)
    (jj jj' : D ⥤ F)
    (jkl jkl' : A ⥤ E)
    (jij jij' : C ⥤ F)
    (r r' : A ⥤ C)
    (p p' : B ⥤ D)
    (q q' : E ⥤ F)
    (g1 : r ⋙ ji ⟶ jk ⋙ p) (g1' : r' ⋙ ji' ⟶ jk' ⋙ p')
    (g2 : p ⋙ jj ⟶ jl ⋙ q) (g2' : p' ⋙ jj' ⟶ jl' ⋙ q')
    (g : r ⋙ jij ⟶ jkl ⋙ q) (g' : r' ⋙ jij' ⟶ jkl' ⋙ q')
    (ci : ji ⋙ jj ≅ jij) (ci' : ji' ⋙ jj' ≅ jij')
    (ck : jk ⋙ jl ≅ jkl) (ck' : jk' ⋙ jl' ≅ jkl')
    (hjk : jk = jk')
    (hjl : jl = jl')
    (hji : ji = ji')
    (hjj : jj = jj')
    (hjkl : jkl = jkl')
    (hjij : jij = jij')
    (hr : r = r')
    (hp : p = p')
    (hq : q = q')
    (hg1 : HEq g1 g1')
    (hg2 : HEq g2 g2')
    (hg : HEq g g')
    (hci : HEq ci ci')
    (hck : HEq ck ck')
    (h : ∀ M : A, ci'.hom.app (r'.obj M) ≫ g'.app M ≫ q'.map (ck'.inv.app M) =
      jj'.map (g1'.app M) ≫ g2'.app (jk'.obj M)) :
    ∀ M : A, ci.hom.app (r.obj M) ≫ g.app M ≫ q.map (ck.inv.app M) =
      jj.map (g1.app M) ≫ g2.app (jk.obj M) := by
  subst jk'
  subst jl'
  subst ji'
  subst jj'
  subst jkl'
  subst jij'
  subst r'
  subst p'
  subst q'
  cases hg1
  cases hg2
  cases hg
  cases hci
  cases hck
  exact h

private theorem cube_transfer
    {A B C D A1 B1 C1 D1 : Type*}
    [Category A]
    [Category B]
    [Category C]
    [Category D]
    [Category A1]
    [Category B1]
    [Category C1]
    [Category D1]
    (r r' : A ⥤ C)
    (p p' : B ⥤ D)
    (k k' : A ⥤ B)
    (i i' : C ⥤ D)
    (r1 r1' : A1 ⥤ C1)
    (p1 p1' : B1 ⥤ D1)
    (k1 k1' : A1 ⥤ B1)
    (i1 i1' : C1 ⥤ D1)
    (a a' : B ⥤ B1)
    (b b' : D ⥤ D1)
    (c c' : C ⥤ C1)
    (d d' : A ⥤ A1)
    (g : r ⋙ i ⟶ k ⋙ p) (g' : r' ⋙ i' ⟶ k' ⋙ p')
    (g1 : r1 ⋙ i1 ⟶ k1 ⋙ p1) (g1' : r1' ⋙ i1' ⟶ k1' ⋙ p1')
    (ep : p ⋙ b ⟶ a ⋙ p1) (ep' : p' ⋙ b' ⟶ a' ⋙ p1')
    (er : r ⋙ c ⟶ d ⋙ r1) (er' : r' ⋙ c' ⟶ d' ⋙ r1')
    (bk : k ⋙ a ≅ d ⋙ k1) (bk' : k' ⋙ a' ≅ d' ⋙ k1')
    (bi : i ⋙ b ≅ c ⋙ i1) (bi' : i' ⋙ b' ≅ c' ⋙ i1')
    (hr : r = r')
    (hp : p = p')
    (hk : k = k')
    (hi : i = i')
    (hr1 : r1 = r1')
    (hp1 : p1 = p1')
    (hk1 : k1 = k1')
    (hi1 : i1 = i1')
    (ha : a = a')
    (hb : b = b')
    (hc : c = c')
    (hd : d = d')
    (hg : HEq g g')
    (hg1 : HEq g1 g1')
    (hep : HEq ep ep')
    (her : HEq er er')
    (hbk : HEq bk bk')
    (hbi : HEq bi bi')
    (h : ∀ M : A, b'.map (g'.app M) ≫ ep'.app (k'.obj M) ≫ p1'.map (bk'.hom.app M) =
      bi'.hom.app (r'.obj M) ≫ i1'.map (er'.app M) ≫ g1'.app (d'.obj M)) :
    ∀ M : A, b.map (g.app M) ≫ ep.app (k.obj M) ≫ p1.map (bk.hom.app M) =
      bi.hom.app (r.obj M) ≫ i1.map (er.app M) ≫ g1.app (d.obj M) := by
  subst r'
  subst p'
  subst k'
  subst i'
  subst r1'
  subst p1'
  subst k1'
  subst i1'
  subst a'
  subst b'
  subst c'
  subst d'
  cases hg
  cases hg1
  cases hep
  cases her
  cases hbk
  cases hbi
  exact h

private theorem adj_comp_heq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L L' : A ⥤ B} {R R' : B ⥤ A} {M M' : B ⥤ C} {S S' : C ⥤ B}
    (a : L ⊣ R) (a' : L' ⊣ R') (b : M ⊣ S) (b' : M' ⊣ S')
    (hL : L = L') (hR : R = R') (hM : M = M') (hS : S = S')
    (ha : HEq a a') (hb : HEq b b') : HEq (a.comp b) (a'.comp b') := by
  subst L'
  subst R'
  subst M'
  subst S'
  cases ha
  cases hb
  rfl

private theorem iso_heq_of_hom_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y')
    (he : HEq e.hom e'.hom) : HEq e e' := by
  subst X'
  subst Y'
  exact (Iso.ext (eq_of_heq he)).heq

private theorem forward_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.hom.app X) ≫ θ'.app (a.obj X) =
        pK.inv.app (G.obj X) ≫ d.map (θ.app X) ≫
          pH.hom.app (F.obj X) ≫ H'.map (pF.hom.app X))
    (E : B) :
    c.map ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E) ≫
        (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫
        G'.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E) ≫
        (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) := by
  apply CategoryTheory.exchangeMate_cube adj adjK adj' adjK' a b c d
    pF pG pH pK θ θ' ?_ E
  intro X
  have hh := congrArg (fun t ↦ K'.map (pG.inv.app X) ≫ t ≫
    H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X)) (hc X)
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app] at hh
  erw [K'.map_id, Category.id_comp, H'.map_id, Category.id_comp] at hh
  simp only [Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.Normalization
