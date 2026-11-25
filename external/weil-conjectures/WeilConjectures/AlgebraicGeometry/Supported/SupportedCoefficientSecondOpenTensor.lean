/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenTensor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenMateQuotient
import WeilConjectures.AlgebraicGeometry.Supported.SupportedTensorComplexSquare
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# Open pullback in the second coefficient

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, steps 5 and 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Pull the uncut first supported coefficient to the second open product.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-second-open-tensor). -/
noncomputable def supportSecondOpenFirstCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (V : Y.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedFirstCoefficients A f (V.ι ≫ g) b).mapDerivedCategory.obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.obj
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M) :=
  (supportFirstCoefficientProjectionIso A f (V.ι ≫ g) b).hom.app M ≫
    (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
      (supportedSecondOpenMap_fst f g V)
      ((supportedCoefficients A b).mapDerivedCategory.obj M)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
      ((supportFirstCoefficientProjectionIso A f g b).inv.app M)

/-- Pull the second supported coefficient to the open product by the mate of restriction.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-second-open-tensor). -/
noncomputable def supportSecondOpenCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (V : Y.Opens) (N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V)).mapDerivedCategory.obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.obj
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N) :=
  (supportSecondCoefficientProjectionIso A f (V.ι ≫ g) (supportOnOpen d V)).hom.app N ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g))).leftDerivedFunctor.map
      ((supportCoefficientOpenMate A V.ι d (supportOnOpen d V)
        (supportOnOpen_complement d V)).app N) ≫
    (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      (pullback.snd f g) (pullback.snd f (V.ι ≫ g)) V.ι
      (supportedSecondOpenMap_snd f g V)
      ((supportedCoefficients A d).mapDerivedCategory.obj N)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
      ((supportSecondCoefficientProjectionIso A f g d).inv.app N)

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
-- Match the symmetry projection used by the generic coefficient constructions.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance high] sheafBraidedCategory

section ExactFactors

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private theorem factorsh_quotient (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem exactMap_fac_h {F' : C ⥤ D} [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Qh.obj K) ≫
        F.mapDerivedCategoryFactorsh.hom.app K =
      F'.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K) := by
  simp only [Functor.exactDerivedMap, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem exactMap_fac {F' : C ⥤ D} [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F) (P : CochainComplex C ℤ) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Q.obj P) ≫
        F.mapDerivedCategoryFactors.hom.app P =
      F'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) := by
  have h := exactMap_fac_h F α ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [factorsh_quotient, factorsh_quotient] at h
  exact h

end ExactFactors

section TensorFactors

universe w₀

variable {C : Type*} [Category.{w₀} C] [Abelian C]
  [IsGrothendieckAbelian.{w₀} C] [HasDerivedCategory.{w₀} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C] in
private theorem quotient_tensor (P Q : CochainComplex C ℤ) :
    ((HomotopyCategory.quotient C (.up ℤ)).obj P ⊗
      (HomotopyCategory.quotient C (.up ℤ)).obj Q) =
      (HomotopyCategory.quotient C (.up ℤ)).obj (P ⊗ Q) := rfl

private theorem μQ_eq (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ (_ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ 𝟙 _ = _
  simp only [tensorHom_id, id_whiskerRight, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

end TensorFactors

section CochainTensorFactor

universe w
variable {C D : Type*} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Monoidal] [PreservesColimitsOfSize.{0, 0} F]
  (κ : ∀ K L : DerivedCategory C,
    F.mapDerivedCategory.obj (K ⊗ L) ⟶
      F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L)

/-- Keep the cochain normalization folded when specializing its coefficient category. -/
@[irreducible]
private noncomputable def tensorFactorCondition (P Q : CochainComplex C ℤ) : Prop :=
  κ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
    (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
      F.mapDerivedCategoryFactors.hom.app Q) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
  F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
    F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
    DerivedCategory.Q.map
      (Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) P Q)

end CochainTensorFactor

section ModelSquare

variable {C D E C' D' E' : Type*}
  [Category C] [Category D] [Category E]
  [Category C'] [Category D'] [Category E']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
  (L : C ⥤ C') (R : D ⥤ D') (S : E ⥤ E')
  [L.LaxMonoidal] [R.LaxMonoidal] [S.LaxMonoidal]
  (G F₁ F₂ : C ⥤ D) (G' F₁' F₂' : C ⥤ E) (H : D ⥤ E) [H.OplaxMonoidal]
  (DG DF₁ DF₂ : C' ⥤ D') (DG' DF₁' DF₂' : C' ⥤ E') (DH : D' ⥤ E')
  (eG : L ⋙ DG ≅ G ⋙ R) (e₁ : L ⋙ DF₁ ≅ F₁ ⋙ R)
  (e₂ : L ⋙ DF₂ ≅ F₂ ⋙ R) (eG' : L ⋙ DG' ≅ G' ⋙ S)
  (e₁' : L ⋙ DF₁' ≅ F₁' ⋙ S) (e₂' : L ⋙ DF₂' ≅ F₂' ⋙ S)
  (eH : R ⋙ DH ≅ H ⋙ S)
  (a₀ : G' ⟶ G ⋙ H) (a₁ : F₁' ⟶ F₁ ⋙ H) (a₂ : F₂' ⟶ F₂ ⋙ H)
  (d₀ : DG' ⟶ DG ⋙ DH) (d₁ : DF₁' ⟶ DF₁ ⋙ DH) (d₂ : DF₂' ⟶ DF₂ ⋙ DH)
  (κ : (Functor.postcompose₂.obj DH).obj (curriedTensor D') ⟶
    (((Functor.whiskeringLeft₂ E').obj DH).obj DH).obj (curriedTensor E'))

private theorem tensorSquare_model
    (τ : ∀ M N, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N)
    (τ' : ∀ M N, G'.obj (M ⊗ N) ⟶ F₁'.obj M ⊗ F₂'.obj N)
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N)
    (t' : ∀ M N, DG'.obj (M ⊗ N) ⟶ DF₁'.obj M ⊗ DF₂'.obj N)
    (h₀ : ∀ P, d₀.app (L.obj P) ≫ DH.map (eG.hom.app P) ≫ eH.hom.app (G.obj P) =
      eG'.hom.app P ≫ S.map (a₀.app P))
    (h₁ : ∀ P, d₁.app (L.obj P) ≫ DH.map (e₁.hom.app P) ≫ eH.hom.app (F₁.obj P) =
      e₁'.hom.app P ≫ S.map (a₁.app P))
    (h₂ : ∀ P, d₂.app (L.obj P) ≫ DH.map (e₂.hom.app P) ≫ eH.hom.app (F₂.obj P) =
      e₂'.hom.app P ≫ S.map (a₂.app P))
    (hκ : ∀ P Q, (κ.app (R.obj P)).app (R.obj Q) ≫
      (eH.hom.app P ⊗ₘ eH.hom.app Q) ≫
        Functor.LaxMonoidal.μ S (H.obj P) (H.obj Q) =
      DH.map (Functor.LaxMonoidal.μ R P Q) ≫ eH.hom.app (P ⊗ Q) ≫
        S.map (Functor.OplaxMonoidal.δ H P Q))
    (ht : ∀ P Q, DG.map (Functor.LaxMonoidal.μ L P Q) ≫ eG.hom.app (P ⊗ Q) ≫
      R.map (τ P Q) = t (L.obj P) (L.obj Q) ≫
        (e₁.hom.app P ⊗ₘ e₂.hom.app Q) ≫ Functor.LaxMonoidal.μ R _ _)
    (ht' : ∀ P Q, DG'.map (Functor.LaxMonoidal.μ L P Q) ≫ eG'.hom.app (P ⊗ Q) ≫
      S.map (τ' P Q) = t' (L.obj P) (L.obj Q) ≫
        (e₁'.hom.app P ⊗ₘ e₂'.hom.app Q) ≫ Functor.LaxMonoidal.μ S _ _)
    (ha : ∀ P Q, a₀.app (P ⊗ Q) ≫ H.map (τ P Q) ≫
      Functor.OplaxMonoidal.δ H (F₁.obj P) (F₂.obj Q) =
      τ' P Q ≫ (a₁.app P ⊗ₘ a₂.app Q))
    (P Q : C) [Mono (Functor.LaxMonoidal.μ S (H.obj (F₁.obj P)) (H.obj (F₂.obj Q)))] :
    d₀.app (L.obj P ⊗ L.obj Q) ≫ DH.map (t (L.obj P) (L.obj Q)) ≫
      (κ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) =
    t' (L.obj P) (L.obj Q) ≫ (d₁.app (L.obj P) ⊗ₘ d₂.app (L.obj Q)) := by
  apply (cancel_mono ((DH.map (e₁.hom.app P) ≫ eH.hom.app (F₁.obj P) ⊗ₘ
      DH.map (e₂.hom.app Q) ≫ eH.hom.app (F₂.obj Q)) ≫
        Functor.LaxMonoidal.μ S _ _)).1
  have hn := congr_app (κ.naturality (e₁.hom.app P)) (DF₂.obj (L.obj Q))
  have hm := (κ.app (R.obj (F₁.obj P))).naturality (e₂.hom.app Q)
  change DH.map (e₁.hom.app P ▷ _) ≫ _ =
    _ ≫ (DH.map (e₁.hom.app P) ▷ _) at hn
  change DH.map (_ ◁ e₂.hom.app Q) ≫ _ =
    _ ≫ (_ ◁ DH.map (e₂.hom.app Q)) at hm
  have hnat : DH.map (e₁.hom.app P ⊗ₘ e₂.hom.app Q) ≫
      (κ.app (R.obj (F₁.obj P))).app (R.obj (F₂.obj Q)) =
    (κ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) ≫
      (DH.map (e₁.hom.app P) ⊗ₘ DH.map (e₂.hom.app Q)) := by
    rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc]
    erw [hm, ← Category.assoc, hn]
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← Category.assoc _ (DH.map (e₁.hom.app P) ⊗ₘ DH.map (e₂.hom.app Q)),
    ← hnat]
  simp only [Category.assoc]
  rw [hκ]
  simp only [← DH.map_comp_assoc]
  rw [← ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (eH.hom.naturality (τ P Q))]
  erw [← reassoc_of% (d₀.naturality (Functor.LaxMonoidal.μ L P Q))]
  rw [reassoc_of% (h₀ (P ⊗ Q))]
  rw [← S.map_comp, ← S.map_comp, ha, S.map_comp]
  rw [reassoc_of% (ht' P Q)]
  rw [← Functor.LaxMonoidal.μ_natural]
  erw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  rw [← h₁, ← h₂]
  erw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rfl

private theorem tensorComparison_natural
    {P P' Q Q' : D'} (a : P ⟶ P') (b : Q ⟶ Q') :
    DH.map (a ⊗ₘ b) ≫ (κ.app P').app Q' =
      (κ.app P).app Q ≫ (DH.map a ⊗ₘ DH.map b) := by
  have hn := congr_app (κ.naturality a) Q
  have hm := (κ.app P').naturality b
  change DH.map (a ▷ _) ≫ _ = _ ≫ (DH.map a ▷ _) at hn
  change DH.map (_ ◁ b) ≫ _ = _ ≫ (_ ◁ DH.map b) at hm
  rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc]
  erw [hm, ← Category.assoc, hn]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]

private theorem tensorSquare_left_natural
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N)
    (ht : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      DG.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ (DF₁.map a ⊗ₘ DF₂.map b))
    {M M' N N' : C'} (a : M ⟶ M') (b : N ⟶ N') :
    DG'.map (a ⊗ₘ b) ≫
        (d₀.app (M' ⊗ N') ≫ DH.map (t M' N') ≫ (κ.app (DF₁.obj M')).app (DF₂.obj N')) =
      (d₀.app (M ⊗ N) ≫ DH.map (t M N) ≫ (κ.app (DF₁.obj M)).app (DF₂.obj N)) ≫
        (DH.map (DF₁.map a) ⊗ₘ DH.map (DF₂.map b)) := by
  rw [← Category.assoc, d₀.naturality]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  rw [← DH.map_comp_assoc, ht, DH.map_comp, Category.assoc,
    tensorComparison_natural]

omit [MonoidalCategory D'] in
private theorem tensorSquare_right_natural
    (t' : ∀ M N, DG'.obj (M ⊗ N) ⟶ DF₁'.obj M ⊗ DF₂'.obj N)
    (ht' : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      DG'.map (a ⊗ₘ b) ≫ t' M' N' = t' M N ≫ (DF₁'.map a ⊗ₘ DF₂'.map b))
    {M M' N N' : C'} (a : M ⟶ M') (b : N ⟶ N') :
    DG'.map (a ⊗ₘ b) ≫ (t' M' N' ≫ (d₁.app M' ⊗ₘ d₂.app N')) =
      (t' M N ≫ (d₁.app M ⊗ₘ d₂.app N)) ≫
        (DH.map (DF₁.map a) ⊗ₘ DH.map (DF₂.map b)) := by
  rw [← Category.assoc, ht']
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  erw [d₁.naturality, d₂.naturality]
  rfl

end ModelSquare

private theorem family_eq_of_models
    {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory C]
    [MonoidalCategory E] (G : C ⥤ D) (F₁ F₂ : C ⥤ E) (H : E ⥤ D)
    (s t : ∀ M N, G.obj (M ⊗ N) ⟶ H.obj (F₁.obj M ⊗ F₂.obj N))
    (hs : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ s M' N' = s M N ≫ H.map (F₁.map a ⊗ₘ F₂.map b))
    (ht : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ H.map (F₁.map a ⊗ₘ F₂.map b))
    (hmodels : ∀ M N, ∃ P Q, s P Q = t P Q ∧ Nonempty (P ≅ M) ∧ Nonempty (Q ≅ N))
    (M N : C) : s M N = t M N := by
  obtain ⟨P, Q, h, ⟨e⟩, ⟨d⟩⟩ := hmodels M N
  apply (cancel_epi (G.map (e.hom ⊗ₘ d.hom))).1
  rw [hs, ht, h]

section ExactNaturality

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

end ExactNaturality

private theorem triangle_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F ⋙ H) (P : CochainComplex C ℤ) :
    ((Functor.exactDerivedMap α).app (DerivedCategory.Q.obj P) ≫
        (Functor.mapDerivedCategoryCompIso F H).inv.app (DerivedCategory.Q.obj P)) ≫
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    F'.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map (Functor.mapHomologicalComplexCompNatTrans F H F' α P) := by
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, exactMap_fac]
  congr 2
  ext n
  simp only [Functor.mapHomologicalComplexCompNatTrans_f,
    NatTrans.mapHomologicalComplex_app_f]

section

attribute [local irreducible] supportCoefficientOpenMate supportCoefficientMate
  Functor.exactDerivedMap

end

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency true in
private noncomputable def transportBifunctorIso
    {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    {L H : C ⥤ D} (τ : L ≅ H)
    (δ : (Functor.postcompose₂.obj L).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj T') :
    (Functor.postcompose₂.obj H).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj T' :=
  (Functor.postcompose₂.mapIso τ.symm).app T ≪≫ δ ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso τ).app L).app T' ≪≫
    (((Functor.whiskeringLeft₂ _).obj H).mapIso τ).app T'

section TensorPullback

variable (E : Type v₁) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [UpperStarPreservesFlat E]

omit [UpperStarPreservesFlat E] in
private noncomputable def exactTensorNatIso
    {P Q : Scheme.{u}} (h : Q ⟶ P) :
    (Functor.postcompose₂.obj (upperStar E h).mapDerivedCategory).obj
        (curriedTensor (DerivedCategory (Sheaf P.smallEtaleTopology E))) ≅
      (((Functor.whiskeringLeft₂ _).obj
        (upperStar E h).mapDerivedCategory).obj
        (upperStar E h).mapDerivedCategory).obj (curriedTensor _) :=
  transportBifunctorIso (derivedTensor E P)
    (derivedTensor E Q)
    (leftDerivedUpperStarIsoMapDerivedCategory E h)
    (leftDerivedUpperStarTensorNatIso E h)

end TensorPullback

section ExactSquare

universe w
variable {C D E : Type*} [Category.{w + 1} C] [Category.{w + 1} D] [Category.{w + 1} E]
  [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D] [HasDerivedCategory.{w + 1} E]
  (G F₁ F₂ : C ⥤ D) (G' F₁' F₂' : C ⥤ E) (H : D ⥤ E)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G'.Additive] [F₁'.Additive] [F₂'.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.Monoidal] [H.IsLeftAdjoint]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint]
  (a₀ : G' ⟶ G ⋙ H) (a₁ : F₁' ⟶ F₁ ⋙ H) (a₂ : F₂' ⟶ F₂ ⋙ H)
  (κ : (Functor.postcompose₂.obj H.mapDerivedCategory).obj
      (curriedTensor (DerivedCategory D)) ⟶
    (((Functor.whiskeringLeft₂ _).obj H.mapDerivedCategory).obj
      H.mapDerivedCategory).obj (curriedTensor (DerivedCategory E)))
  (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) ⟶
    (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
      (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex D ℤ)))
  (τ' : (Functor.postcompose₂.obj (G'.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) ⟶
    (((Functor.whiskeringLeft₂ _).obj (F₁'.mapHomologicalComplex (.up ℤ))).obj
      (F₂'.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex E ℤ)))
  (t : supportedDerivedComparisonHom G F₁ F₂)
  (t' : supportedDerivedComparisonHom G' F₁' F₂')

-- Keep the total-complex square folded when its coefficient categories are specialized.
omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint] in
@[irreducible]
private noncomputable def exactComplexSquareCondition (P Q : CochainComplex C ℤ) : Prop :=
  Functor.mapHomologicalComplexCompNatTrans G H G' a₀ (P ⊗ Q) ≫
    (H.mapHomologicalComplex (.up ℤ)).map ((τ.app P).app Q) ≫
    Functor.OplaxMonoidal.δ (H.mapHomologicalComplex (.up ℤ))
      ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
      ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) =
  (τ'.app P).app Q ≫
    (Functor.mapHomologicalComplexCompNatTrans F₁ H F₁' a₁ P ⊗ₘ
      Functor.mapHomologicalComplexCompNatTrans F₂ H F₂' a₂ Q)

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint] in
private theorem complexSquare
    [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G']
    (σ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (σ' : (Functor.postcompose₂.obj G').obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj F₁').obj F₂').obj (curriedTensor E))
    (ha : ∀ M N, a₀.app (M ⊗ N) ≫ H.map ((σ.app M).app N) ≫
      Functor.OplaxMonoidal.δ H (F₁.obj M) (F₂.obj N) =
      (σ'.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (P Q : CochainComplex C ℤ) :
    exactComplexSquareCondition G F₁ F₂ G' F₁' F₂' H a₀ a₁ a₂
      (supportedComplexComparisonNatTrans G F₁ F₂ σ)
      (supportedComplexComparisonNatTrans G' F₁' F₂' σ') P Q := by
  unfold exactComplexSquareCondition
  have e := supportedTensorComplex_square G F₁ F₂ G' F₁' F₂' H σ σ' a₀ a₁ a₂ ha P Q
  unfold supportedTensorComplexSquareCondition at e
  exact e

private theorem exactSquare
    (ht : supportedDerivedComparisonCondition G F₁ F₂ τ t)
    (ht' : supportedDerivedComparisonCondition G' F₁' F₂' τ' t')
    (hκ : ∀ P Q : CochainComplex D ℤ,
      tensorFactorCondition H (fun K L => (κ.app K).app L) P Q)
    (ha : ∀ P Q : CochainComplex C ℤ,
      exactComplexSquareCondition G F₁ F₂ G' F₁' F₂' H a₀ a₁ a₂ τ τ' P Q)
    (M N : DerivedCategory C) :
    ((Functor.exactDerivedMap a₀).app (M ⊗ N) ≫
        (Functor.mapDerivedCategoryCompIso G H).inv.app (M ⊗ N)) ≫
      H.mapDerivedCategory.map (t M N) ≫
      (κ.app (F₁.mapDerivedCategory.obj M)).app (F₂.mapDerivedCategory.obj N) =
    t' M N ≫
      (((Functor.exactDerivedMap a₁).app M ≫
        (Functor.mapDerivedCategoryCompIso F₁ H).inv.app M) ⊗ₘ
      ((Functor.exactDerivedMap a₂).app N ≫
        (Functor.mapDerivedCategoryCompIso F₂ H).inv.app N)) := by
  unfold tensorFactorCondition at hκ
  unfold exactComplexSquareCondition at ha
  let d₀ := Functor.exactDerivedMap a₀ ≫ (Functor.mapDerivedCategoryCompIso G H).inv
  let d₁ := Functor.exactDerivedMap a₁ ≫ (Functor.mapDerivedCategoryCompIso F₁ H).inv
  let d₂ := Functor.exactDerivedMap a₂ ≫ (Functor.mapDerivedCategoryCompIso F₂ H).inv
  refine family_eq_of_models G'.mapDerivedCategory
    (F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (F₂.mapDerivedCategory ⋙ H.mapDerivedCategory) (𝟭 _)
    (fun M N => d₀.app (M ⊗ N) ≫ H.mapDerivedCategory.map (t M N) ≫
      (κ.app (F₁.mapDerivedCategory.obj M)).app (F₂.mapDerivedCategory.obj N))
    (fun M N => t' M N ≫ (d₁.app M ⊗ₘ d₂.app N)) ?_ ?_ ?_ M N
  · exact fun _ _ _ _ a b => tensorSquare_left_natural
      (DG := G.mapDerivedCategory) (DF₁ := F₁.mapDerivedCategory)
      (DF₂ := F₂.mapDerivedCategory) (DG' := G'.mapDerivedCategory)
      (DH := H.mapDerivedCategory) d₀ κ t ht.1 a b
  · exact fun _ _ _ _ a b => tensorSquare_right_natural
      (DF₁ := F₁.mapDerivedCategory) (DF₂ := F₂.mapDerivedCategory)
      (DG' := G'.mapDerivedCategory) (DF₁' := F₁'.mapDerivedCategory)
      (DF₂' := F₂'.mapDerivedCategory) (DH := H.mapDerivedCategory) d₁ d₂ t' ht'.1 a b
  · intro M N
    let := Localization.essSurj DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    let P := DerivedCategory.Q.objPreimage M
    let Q := DerivedCategory.Q.objPreimage N
    let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some
    let R := Λ.reduced.resolutionFunctor.obj Q
    have hR : (HomologicalComplex.quasiIso E (.up ℤ)).kFlat
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj R)) :=
      (F₂ ⋙ H).kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
        ObjectProperty.flat.essImage_ι_le Q
    have : IsIso (DerivedCategory.Q.map (Λ.reduced.resolutionNatTrans.app Q)) := by
      have := Λ.reduced.quasiIso_resolutionNatTrans_app Q
      infer_instance
    refine ⟨DerivedCategory.Q.obj P, DerivedCategory.Q.obj R, ?_,
      ⟨DerivedCategory.Q.objObjPreimageIso M⟩,
      ⟨asIso (DerivedCategory.Q.map (Λ.reduced.resolutionNatTrans.app Q)) ≪≫
        DerivedCategory.Q.objObjPreimageIso N⟩⟩
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj R))) := by
      rw [μQ_eq (C := E)]
      exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
        (HomotopyCategory.quasiIso E (.up ℤ)) _ _
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR)
    apply tensorSquare_model DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      (G.mapHomologicalComplex (.up ℤ)) (F₁.mapHomologicalComplex (.up ℤ))
      (F₂.mapHomologicalComplex (.up ℤ)) (G'.mapHomologicalComplex (.up ℤ))
      (F₁'.mapHomologicalComplex (.up ℤ)) (F₂'.mapHomologicalComplex (.up ℤ))
      (H.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategory F₁.mapDerivedCategory
      F₂.mapDerivedCategory G'.mapDerivedCategory F₁'.mapDerivedCategory
      F₂'.mapDerivedCategory H.mapDerivedCategory
      G.mapDerivedCategoryFactors F₁.mapDerivedCategoryFactors F₂.mapDerivedCategoryFactors
      G'.mapDerivedCategoryFactors F₁'.mapDerivedCategoryFactors F₂'.mapDerivedCategoryFactors
      H.mapDerivedCategoryFactors
      (NatTrans.mapHomologicalComplex a₀ (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).inv)
      (NatTrans.mapHomologicalComplex a₁ (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ H)) (.up ℤ)).inv)
      (NatTrans.mapHomologicalComplex a₂ (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F₂ ⋙ H)) (.up ℤ)).inv)
      d₀ d₁ d₂ κ (fun P Q => (τ.app P).app Q)
      (fun P Q => (τ'.app P).app Q) t t'
      (triangle_fac G H G' a₀) (triangle_fac F₁ H F₁' a₁)
      (triangle_fac F₂ H F₂' a₂) hκ ?_ ?_ ha P R
    · intro P Q
      have h := ht.2 P Q
      have he : eqToHom (supportedComplexTensor_eq
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)) = 𝟙 _ := rfl
      rw [he, CategoryTheory.Functor.map_id, Category.comp_id] at h
      exact h
    · intro P Q
      have h := ht'.2 P Q
      have he : eqToHom (supportedComplexTensor_eq
          ((F₁'.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂'.mapHomologicalComplex (.up ℤ)).obj Q)) = 𝟙 _ := rfl
      rw [he, CategoryTheory.Functor.map_id, Category.comp_id] at h
      exact h

end ExactSquare

attribute [local irreducible] supportSecondOpenFirstCoefficientMap
  supportSecondOpenCoefficientMap supportCoefficientOpenMate supportExactPullbackTensorIso
  exactTensorNatIso supportedDerivedComparisonCondition supportedComplexComparisonNatTrans

end AlgebraicGeometry.Etale
