/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Preservation of commutative cubes under exact localization.
The generic proof is retained from TensorPullbackSquare for its existing consumers. -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace CategoryTheory.Functor

section ExactCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory F]
  (L : C ⥤ D) (M : D ⥤ E) (N : E ⥤ F)
  [L.Additive] [M.Additive] [N.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]

private noncomputable abbrev tripleComparison :
    (L ⋙ M ⋙ N).mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ M.mapDerivedCategory ⋙ N.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (L ⋙ M) N).symm ≪≫
    isoWhiskerRight (Functor.mapDerivedCategoryCompIso L M).symm N.mapDerivedCategory

private lemma tripleComparison_hom :
    (tripleComparison L M N).hom =
      (Functor.mapDerivedCategoryCompIso L (M ⋙ N)).inv ≫
        Functor.whiskerLeft L.mapDerivedCategory (Functor.mapDerivedCategoryCompIso M N).inv :=
  (Functor.mapDerivedCategoryCompIso_assoc L M N).symm

variable {L M N}
  {D' : Type*} [Category D'] [Abelian D'] [HasDerivedCategory D']
  {L' : C ⥤ D'} {M' : D' ⥤ E}
  [L'.Additive] [M'.Additive]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits M'] [PreservesFiniteColimits M']

private lemma tripleComparison_right (e : L ⋙ M ≅ L' ⋙ M') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso e).hom
          N.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerRight e N)).hom ≫
        (tripleComparison L' M' N).hom := by
  dsimp only [tripleComparison, Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Functor.whiskerRight_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerRight_comp
    (Functor.mapDerivedCategoryCompIso L M).inv
    (Functor.mapDerivedCategoryCompIso L M).hom N.mapDerivedCategory), Iso.inv_hom_id]
  simp only [Functor.whiskerRight_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N)]

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory E']
  {M'' : D ⥤ E'} {N' : E' ⥤ F}
  [M''.Additive] [N'.Additive]
  [PreservesFiniteLimits M''] [PreservesFiniteColimits M'']
  [PreservesFiniteLimits N'] [PreservesFiniteColimits N']

private lemma tripleComparison_left (e : M ⋙ N ≅ M'' ⋙ N') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerLeft L.mapDerivedCategory
          (Functor.mapDerivedCategorySquareIso e).hom =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerLeft L e)).hom ≫
        (tripleComparison L M'' N').hom := by
  rw [tripleComparison_hom, tripleComparison_hom]
  dsimp only [Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerLeft_comp L.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso M N).inv
    (Functor.mapDerivedCategoryCompIso M N).hom), Iso.inv_hom_id]
  simp only [Functor.whiskerLeft_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft L e)]

end ExactCoherence

section DerivedCube
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']

/-- An exact functorial cube remains commutative on unbounded derived categories.
Source: the final tensor-compatibility paragraph of the latest blueprint's
lemma-sp-reduction--1; exact localization via
`Functor.mapDerivedCategoryCompIso_assoc` and its whiskering identities.
(blueprint: lem-sp-exact-derived-cube)
Proof: form the two ordinary triple pastings. Their components agree by hc, hence
natural-isomorphism extensionality identifies them. The left and right triple-comparison
whiskering identities express the two derived pastings as the images of these ordinary
pastings with the same triple comparators. Cancel the common comparator and evaluate.
This proof is the generic derivedCube argument formerly in TensorPullbackSquare. -/
theorem exactDerivedCube
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : ∀ M, c.hom.app (R₀.obj M) ≫ I.map (qG.hom.app M) ≫ qI.hom.app (G'.obj M) =
      H.map (qJ.hom.app M) ≫ qH.hom.app (J'.obj M) ≫ R₃.map (d.hom.app M))
    (M : DerivedCategory D₀) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (R₀.mapDerivedCategory.obj M) ≫
        I.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qG).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qI).hom.app (G'.mapDerivedCategory.obj M) =
      H.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qJ).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qH).hom.app (J'.mapDerivedCategory.obj M) ≫
        R₃.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app M) := by
  let pL := isoWhiskerLeft R₀ c ≪≫ isoWhiskerRight qG I ≪≫ isoWhiskerLeft G' qI
  let pR := isoWhiskerRight qJ H ≪≫ isoWhiskerLeft J' qH ≪≫ isoWhiskerRight d R₃
  have hp : pL = pR := by
    apply Iso.ext
    ext K
    exact hc K
  have hL : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerLeft R₀.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom
        I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qI).hom =
      (Functor.mapDerivedCategoryNatIso pL).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_left c),
      reassoc_of% (tripleComparison_right qG), tripleComparison_left qI]
    simp only [pL, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have hR : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom
        H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom
        R₃.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso pR).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_right qJ),
      reassoc_of% (tripleComparison_left qH), tripleComparison_right d]
    simp only [pR, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have h := hL.trans ((congrArg (fun p ↦
    (Functor.mapDerivedCategoryNatIso p).hom ≫ (tripleComparison G' I' R₃).hom) hp).trans
      hR.symm)
  have h' := (cancel_epi (tripleComparison R₀ J H).hom).1 h
  exact congr_app h' M

end DerivedCube

end CategoryTheory.Functor
