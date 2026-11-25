/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullback
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarNormalizations
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax

/-! # Tensor compatibility of the fixed scalar comparisons

Source: Stacks 07A4 and 0D6D, the tensor clause of the finite-Hom domain calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

private theorem complex_compositor_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    (η : F ⋙ G ≅ H) (K : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso η (.up ℤ)).hom.app K =
      (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K := by
  ext i
  rfl

private theorem transpose_of_unit
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (QC : C ⥤ V) (QD : D ⥤ W) (FC : C ⥤ D) (UC : D ⥤ C)
    (E : V ⥤ W) (U : W ⥤ V) (adj : E ⊣ U)
    (a : FC ⊣ UC) (fac : UC ⋙ QC ≅ QD ⋙ U) (r : QC ⋙ E ⟶ FC ⋙ QD)
    (hr : ∀ P, adj.unit.app (QC.obj P) ≫ U.map (r.app P) =
      QC.map (a.unit.app P) ≫ fac.hom.app (FC.obj P))
    (P : C) (K : D) (f : FC.obj P ⟶ K) :
    adj.homEquiv _ _ (r.app P ≫ QD.map f) = QC.map (a.homEquiv _ _ f) ≫ fac.hom.app K := by
  rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_unit, hr]
  have hn := fac.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← QC.map_comp, Adjunction.homEquiv_unit]

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

private theorem left_comp_unit_complex
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [L''.Additive] [R''.Additive]
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'')
    (K : CochainComplex A ℤ) :
    ((a.mapHomologicalComplex (.up ℤ)).comp (b.mapHomologicalComplex (.up ℤ))).homEquiv _ _
        ((Functor.mapHomologicalComplexCompIso
          (Adjunction.leftAdjointCompIso a b c η) (.up ℤ)).hom.app K) ≫
      (Functor.mapHomologicalComplexCompIso η (.up ℤ)).hom.app _ =
        (c.mapHomologicalComplex (.up ℤ)).unit.app K := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := left_comp_unit a b c η (K.X i)
  rw [Adjunction.homEquiv_unit] at h ⊢
  exact h

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

private theorem complex_compositor_tensor
    {C D E : Type*}
    [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [H.IsLeftAdjoint]
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (ν : F ⋙ G ≅ H) [NatTrans.IsMonoidal ν.hom] (K L : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app (K ⊗ L) ≫
        complexTensorMap H K L =
      (G.mapHomologicalComplex (.up ℤ)).map (complexTensorMap F K L) ≫
        complexTensorMap G ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
        ((Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app K ⊗ₘ
          (Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app L) := by
  have hn := Functor.mapHomologicalComplexδNatTrans_naturality ν.hom K L
  rw [Functor.mapHomologicalComplexδNatTrans_comp] at hn
  have he (M) : (Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app M =
      (NatTrans.mapHomologicalComplex ν.hom (.up ℤ)).app M := by
    ext i
    rfl
  simpa only [complexTensorMap, he, Category.assoc] using hn

private def ordinaryComp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u}) :
    ProEtale.etaleSheafExtendScalars φ T ⋙ ProEtale.etaleSheafExtendScalars ψ T ≅
      ProEtale.etaleSheafExtendScalars χ T :=
  Adjunction.leftAdjointCompIso
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (ProEtale.etaleSheafExtendScalarsAdjunction ψ T)
    (ProEtale.etaleSheafExtendScalarsAdjunction χ T)
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ hχ)

section OrdinaryComposition
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
open Functor.LaxMonoidal
variable {R₁ R₂ R₃ : Type (u + 1)} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃) (X : Scheme.{u})

attribute [local instance] Sheaf.monoidalCategory in
private theorem monoidal_tensor_ext
    {C A D : Type*} [Category C] [Category A] [MonoidalCategory A]
    {J : GrothendieckTopology C} [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [Category D] [MonoidalCategory D]
    (F G : D ⥤ Sheaf J A) [F.LaxMonoidal] [G.LaxMonoidal]
    (τ : F ⟶ G) (P Q : D)
    (h : «μ» (sheafToPresheaf J A) (F.obj P) (F.obj Q) ≫
          (sheafToPresheaf J A).map («μ» F P Q ≫ τ.app (P ⊗ Q)) =
        «μ» (sheafToPresheaf J A) (F.obj P) (F.obj Q) ≫
          (sheafToPresheaf J A).map ((τ.app P ⊗ₘ τ.app Q) ≫ «μ» G P Q)) :
    «μ» F P Q ≫ τ.app (P ⊗ Q) = (τ.app P ⊗ₘ τ.app Q) ≫ «μ» G P Q :=
  Sheaf.hom_ext_of_μ_comp h

private theorem restrictScalars_tensor_comp (M N : ModuleCat.{u + 1} R₃) :
    «μ» (ModuleCat.restrictScalars.{u + 1} f) ((ModuleCat.restrictScalars.{u + 1} g).obj M)
        ((ModuleCat.restrictScalars.{u + 1} g).obj N) ≫
      (ModuleCat.restrictScalars.{u + 1} f).map («μ» (ModuleCat.restrictScalars.{u + 1} g) M N) =
    «μ» (ModuleCat.restrictScalars.{u + 1} (g.comp f)) M N := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_
  have h₁ := ModuleCat.restrictScalars_μ_tmul f ((ModuleCat.restrictScalars.{u + 1} g).obj M)
    ((ModuleCat.restrictScalars.{u + 1} g).obj N) s t
  have h₂ := ModuleCat.restrictScalars_μ_tmul g M N s t
  have h₃ := ModuleCat.restrictScalars_μ_tmul (g.comp f) M N s t
  exact (congrArg (fun x ↦ ((ModuleCat.restrictScalars.{u + 1} f).map
    («μ» (ModuleCat.restrictScalars.{u + 1} g) M N)).hom x) h₁).trans (h₂.trans h₃.symm)

/-- Restriction of scalars of sheaves along `g` and then `f` is restriction of scalars along
`g ∘ f`. -/
private def restrictionComp :
    sheafCompose (X.smallEtaleTopology) (ModuleCat.restrictScalars.{u + 1} g) ⋙
        sheafCompose (X.smallEtaleTopology) (ModuleCat.restrictScalars.{u + 1} f) ≅
      sheafCompose (X.smallEtaleTopology) (ModuleCat.restrictScalars.{u + 1} (g.comp f)) :=
  Iso.refl _

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
/-- The identification of the restrictions of scalars along `f ∘ g` in one or two steps is
monoidal. -/
private theorem restrictionComp_monoidal :
    NatTrans.IsMonoidal (restrictionComp f g X).hom where
  unit := by
    apply Sheaf.hom_ext_of_ε_comp
    have h₁ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1} (g.comp f))
    have h₂ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1} f)
    have h₃ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1} g)
    simp only [comp_ε, restrictionComp, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, Functor.map_comp]
    rw [h₁, reassoc_of% h₂]
    rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
        f)).map (ε (sheafCompose (X.smallEtaleTopology)
          (ModuleCat.restrictScalars.{u + 1} g)))) =
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          ((sheafToPresheaf _ _).map (ε (sheafCompose (X.smallEtaleTopology)
          (ModuleCat.restrictScalars.{u + 1} g)))) from rfl, ← Functor.map_comp, h₃]
    have key : ε ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} f)) ≫
        ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          (ε ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} g))) =
        ε ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} (g.comp f))) := by
      ext U : 2
      apply ModuleCat.hom_ext
      ext
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
      rfl
    rw [Functor.map_comp, ← Category.assoc]
    erw [key]
    rfl
  tensor P Q := by
    refine monoidal_tensor_ext _ _ (restrictionComp f g X).hom P Q ?_
    have h₁ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1} (g.comp f)) P Q
    have h₂ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1} f)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} g)).obj P)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} g)).obj Q)
    have h₃ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (X.smallEtaleTopology)
      (ModuleCat.restrictScalars.{u + 1} g) P Q
    simp only [comp_μ, restrictionComp, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, Functor.map_comp, tensorHom_id, id_whiskerRight, Category.id_comp]
    conv_rhs => erw [h₁]
    erw [reassoc_of% h₂]
    rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
        f)).map («μ» (sheafCompose (X.smallEtaleTopology)
          (ModuleCat.restrictScalars.{u + 1} g)) P Q)) =
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          ((sheafToPresheaf _ _).map («μ» (sheafCompose (X.smallEtaleTopology)
          (ModuleCat.restrictScalars.{u + 1} g)) P Q)) from rfl, ← Functor.map_comp, h₃]
    have key : «μ» ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} f)) _ _ ≫
        ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          («μ» ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
            (ModuleCat.restrictScalars.{u + 1} g)) P.obj Q.obj) =
        «μ» ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} (g.comp f))) P.obj Q.obj := by
      ext U : 2
      exact restrictScalars_tensor_comp f g _ _
    rw [Functor.map_comp, ← Category.assoc]
    erw [key]
    rfl

end OrdinaryComposition

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem ordinaryComp_monoidal
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u}) : NatTrans.IsMonoidal (ordinaryComp φ ψ χ hχ T).hom := by
  subst χ
  have he : Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl =
      restrictionComp φ ψ T := by
    apply Iso.ext
    ext P U x
    rfl
  have hm := restrictionComp_monoidal φ ψ T
  rw [← he] at hm
  let a := ProEtale.etaleSheafExtendScalarsAdjunction φ T
  let b := ProEtale.etaleSheafExtendScalarsAdjunction ψ T
  let c := ProEtale.etaleSheafExtendScalarsAdjunction (ψ.comp φ) T
  let η := Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  have hm' : NatTrans.IsMonoidal η.hom := hm
  have := CategoryTheory.Adjunction.isMonoidal_ofNatIsoRight (a.comp b) η
  rw [ordinaryComp, ← left_comp_unique]
  exact Adjunction.isMonoidal_leftAdjointUniq_hom _ c

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.leftAdjoint Functor.rightAdjoint

private theorem complex_derived_comp_factors
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (S : C ⥤ B) (R : B ⥤ A) (W : C ⥤ A)
    [S.Additive] [R.Additive] [W.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (η : S ⋙ R ≅ W) (K : CochainComplex C ℤ) :
    R.mapDerivedCategoryFactors.symm.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.symm.hom.app K) ≫
      (Functor.exactDerivedRestrictionComposition S R W η).hom.app
        (_root_.DerivedCategory.Q.obj K) =
      _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso η (.up ℤ)).hom.app K) ≫
        W.mapDerivedCategoryFactors.symm.hom.app K := by
  rw [complex_compositor_hom]
  exact Functor.exactDerivedRestrictionComposition_inv_factors S R W η K

private theorem derived_normalized_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A}
    [F.Additive] [R.Additive] [G.Additive] [S.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    {FD : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {GD : _root_.DerivedCategory B ⥤ _root_.DerivedCategory C}
    {HD : _root_.DerivedCategory A ⥤ _root_.DerivedCategory C}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ W)
    (ad : FD ⊣ R.mapDerivedCategory) (bd : GD ⊣ S.mapDerivedCategory)
    (cd : HD ⊣ W.mapDerivedCategory) (η : S ⋙ R ≅ W)
    (rF : _root_.DerivedCategory.Q ⋙ FD ⟶ F.mapHomologicalComplex (.up ℤ) ⋙
      _root_.DerivedCategory.Q)
    (rG : _root_.DerivedCategory.Q ⋙ GD ⟶ G.mapHomologicalComplex (.up ℤ) ⋙
      _root_.DerivedCategory.Q)
    (rH : _root_.DerivedCategory.Q ⋙ HD ⟶ H.mapHomologicalComplex (.up ℤ) ⋙
      _root_.DerivedCategory.Q)
    (hF : ∀ K, ad.unit.app (_root_.DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (rF.app K) =
      _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.symm.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (hG : ∀ K, bd.unit.app (_root_.DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (rG.app K) =
      _root_.DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        S.mapDerivedCategoryFactors.symm.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (hH : ∀ K, cd.unit.app (_root_.DerivedCategory.Q.obj K) ≫
      W.mapDerivedCategory.map (rH.app K) =
      _root_.DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        W.mapDerivedCategoryFactors.symm.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K))
    (P : CochainComplex A ℤ) :
    (Adjunction.leftAdjointCompIso ad bd cd
      (Functor.exactDerivedRestrictionComposition S R W η)).hom.app
        (_root_.DerivedCategory.Q.obj P) ≫ rH.app P =
      GD.map (rF.app P) ≫ rG.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Adjunction.leftAdjointCompIso a b c η) (.up ℤ)).hom.app P) := by
  rw [← left_comp_unique ad bd cd]
  have hF' := transpose_of_unit _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _ _ _ _ ad (a.mapHomologicalComplex (.up ℤ)) R.mapDerivedCategoryFactors.symm rF hF
  have hG' := transpose_of_unit _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _ _ _ _ bd (b.mapHomologicalComplex (.up ℤ)) S.mapDerivedCategoryFactors.symm rG hG
  have hH' := transpose_of_unit _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _ _ _ _ cd (c.mapHomologicalComplex (.up ℤ)) W.mapDerivedCategoryFactors.symm rH hH
  simpa only [Category.assoc] using normalizedAdjunction_uniqueness
    ((a.mapHomologicalComplex (.up ℤ)).comp (b.mapHomologicalComplex (.up ℤ)))
    (c.mapHomologicalComplex (.up ℤ)) (ad.comp bd) cd
    (fun K ↦ GD.map (rF.app K) ≫ rG.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) rH.app
    (fun K ↦ R.mapDerivedCategoryFactors.symm.hom.app
      ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
        R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.symm.hom.app K))
    W.mapDerivedCategoryFactors.symm.hom.app
    (by
      intro K L f
      simpa only [Category.assoc] using normalizedAdjunction_composition
        (a.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ)) ad bd rF rG
        R.mapDerivedCategoryFactors.symm.hom S.mapDerivedCategoryFactors.symm.hom
        hF' hG' K L f)
    hH' (Functor.mapHomologicalComplexCompIso η (.up ℤ))
    (Functor.exactDerivedRestrictionComposition S R W η)
    (Functor.mapHomologicalComplexCompIso (Adjunction.leftAdjointCompIso a b c η)
      (.up ℤ)).hom.app
    (left_comp_unit_complex a b c η)
    (by intro K; simpa only [Category.assoc] using complex_derived_comp_factors S R W η K) P

private theorem scalar_unit_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    scalarRepresentativeUnit φ T K =
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ)).unit.app
        K :=
  (mapComplex_unit_formula (ProEtale.etaleSheafExtendScalarsAdjunction φ T) K).symm

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem scalar_unit_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app
        (_root_.DerivedCategory.Q.obj K) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        ((scalarRepresentativeTransformation φ T).app K) =
      _root_.DerivedCategory.Q.map
        (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex
          (.up ℤ)).unit.app K) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.symm.hom.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj K) := by
  simpa only [scalar_rep_app, scalar_unit_eq, Iso.symm_hom] using
    scalarExtensionRepresentative_unit_public φ T K

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem scalar_comp_rep
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
        (_root_.DerivedCategory.Q.obj P) ≫ scalarExtensionRepresentative χ T P =
    (scalarExtension ψ T).map (scalarExtensionRepresentative φ T P) ≫
      scalarExtensionRepresentative ψ T
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (ordinaryComp φ ψ χ hχ T) (.up ℤ)).hom.app P) := by
  have h := derived_normalized_composition
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (ProEtale.etaleSheafExtendScalarsAdjunction ψ T)
    (ProEtale.etaleSheafExtendScalarsAdjunction χ T)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology χ))
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ hχ)
    (scalarRepresentativeTransformation φ T) (scalarRepresentativeTransformation ψ T)
    (scalarRepresentativeTransformation χ T)
    (scalar_unit_normalization φ T) (scalar_unit_normalization ψ T)
    (scalar_unit_normalization χ T) P
  simpa only [scalar_rep_app, ordinaryComp, ProEtale.pbcFixedScalarExtensionComp,
    Sheaf.derivedRestrictScalarsCompIso, Functor.exactDerivedRestrictionComposition,
    scalarExtension, ProEtale.pbcFixedScalarExtension, Sheaf.derivedRestrictScalars] using h

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] ProEtale.pbcFixedScalarExtension
  ProEtale.pbcFixedScalarExtensionComp ordinaryComp scalarExtensionRepresentative
  scalarRepresentativeTransformation tensorIso

private theorem normalized_composition_tensor
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
    (Q : C ⥤ C') (R : D ⥤ D') (S : E ⥤ E')
    [Q.LaxMonoidal] [R.LaxMonoidal] [S.LaxMonoidal]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (dF₀ : ∀ X Y, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (dG₀ : ∀ X Y, G.obj (X ⊗ Y) ⟶ G.obj X ⊗ G.obj Y)
    (dH₀ : ∀ X Y, H.obj (X ⊗ Y) ⟶ H.obj X ⊗ H.obj Y)
    (LF : C' ⥤ D') (LG : D' ⥤ E') (LH : C' ⥤ E')
    (rF : Q ⋙ LF ⟶ F ⋙ R) (rG : R ⋙ LG ⟶ G ⋙ S) (rH : Q ⋙ LH ⟶ H ⋙ S)
    (dF : ∀ X Y, LF.obj (X ⊗ Y) ⟶ LF.obj X ⊗ LF.obj Y)
    (dG : ∀ X Y, LG.obj (X ⊗ Y) ⟶ LG.obj X ⊗ LG.obj Y)
    (dH : ∀ X Y, LH.obj (X ⊗ Y) ⟶ LH.obj X ⊗ LH.obj Y)
    (hF : ∀ P T, dF (Q.obj P) (Q.obj T) ≫ (rF.app P ⊗ₘ rF.app T) ≫
      Functor.LaxMonoidal.μ R (F.obj P) (F.obj T) =
      LF.map (Functor.LaxMonoidal.μ Q P T) ≫ rF.app (P ⊗ T) ≫ R.map (dF₀ P T))
    (hG : ∀ P T, dG (R.obj P) (R.obj T) ≫ (rG.app P ⊗ₘ rG.app T) ≫
      Functor.LaxMonoidal.μ S (G.obj P) (G.obj T) =
      LG.map (Functor.LaxMonoidal.μ R P T) ≫ rG.app (P ⊗ T) ≫ S.map (dG₀ P T))
    (hH : ∀ P T, dH (Q.obj P) (Q.obj T) ≫ (rH.app P ⊗ₘ rH.app T) ≫
      Functor.LaxMonoidal.μ S (H.obj P) (H.obj T) =
      LH.map (Functor.LaxMonoidal.μ Q P T) ≫ rH.app (P ⊗ T) ≫ S.map (dH₀ P T))
    (hn : ∀ {X X' Y Y' : D'} (f : X ⟶ X') (g : Y ⟶ Y'),
      LG.map (f ⊗ₘ g) ≫ dG X' Y' = dG X Y ≫ (LG.map f ⊗ₘ LG.map g))
    (a : LF ⋙ LG ≅ LH) (t : F ⋙ G ≅ H)
    (ht : ∀ P T, t.hom.app (P ⊗ T) ≫ dH₀ P T =
      G.map (dF₀ P T) ≫ dG₀ (F.obj P) (F.obj T) ≫ (t.hom.app P ⊗ₘ t.hom.app T))
    (hr : ∀ K, a.hom.app (Q.obj K) ≫ rH.app K =
      LG.map (rF.app K) ≫ rG.app (F.obj K) ≫ S.map (t.hom.app K))
    (P T : C) [IsIso (Functor.LaxMonoidal.μ Q P T)] [IsIso (rH.app (P ⊗ T))]
    [IsIso (dH₀ P T)] [IsIso (dH (Q.obj P) (Q.obj T))] :
    a.hom.app (Q.obj P ⊗ Q.obj T) ≫ dH (Q.obj P) (Q.obj T) =
      LG.map (dF (Q.obj P) (Q.obj T)) ≫ dG (LF.obj (Q.obj P)) (LF.obj (Q.obj T)) ≫
        (Functor.uncurry.obj (curriedTensor E')).map
          (Prod.mkHom (a.hom.app (Q.obj P)) (a.hom.app (Q.obj T))) := by
  let rFG : Q ⋙ (LF ⋙ LG) ⟶ (F ⋙ G) ⋙ S :=
    Functor.whiskerRight rF LG ≫ Functor.whiskerLeft F rG
  let dFG := fun K L ↦ LG.map (dF K L) ≫ dG (LF.obj K) (LF.obj L)
  let dFG₀ := fun K L ↦ G.map (dF₀ K L) ≫ dG₀ (F.obj K) (F.obj L)
  have hcomp := normalized_tensor_comp Q R S F G dF₀ dG₀ LF LG rF rG dF dG hF hG hn
  have : IsIso (dH (Q.obj P) (Q.obj T) ≫ (rH.app P ⊗ₘ rH.app T) ≫
      Functor.LaxMonoidal.μ S (H.obj P) (H.obj T)) := by
    rw [hH]
    infer_instance
  have : IsIso ((rH.app P ⊗ₘ rH.app T) ≫
      Functor.LaxMonoidal.μ S (H.obj P) (H.obj T)) :=
    IsIso.of_isIso_comp_left (dH (Q.obj P) (Q.obj T)) _
  have hc := normalized_tensor_transport Q S (F ⋙ G) H dFG₀ dH₀ (LF ⋙ LG) LH
    a.hom t.hom rFG rH dFG dH
    (by simpa only [rFG, dFG, dFG₀, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map] using hcomp)
    hH (by intro K L; simpa only [dFG₀, Category.assoc] using ht K L) P T
    (by simpa only [rFG, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hr P)
    (by simpa only [rFG, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hr T)
    (by simpa only [rFG, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hr (P ⊗ T))
  simpa only [dFG, Functor.uncurry_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using hc

private theorem normalized_cochain_composition
    {C D E : Type*}
    [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
    [HasDerivedCategory.{u + 1} E] [Abelian.HasFunctorialFlatResolution E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [H.IsLeftAdjoint]
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (LF : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (LG : _root_.DerivedCategory D ⥤ _root_.DerivedCategory E)
    (LH : _root_.DerivedCategory C ⥤ _root_.DerivedCategory E)
    (rF : _root_.DerivedCategory.Q ⋙ LF ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (rG : _root_.DerivedCategory.Q ⋙ LG ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (rH : _root_.DerivedCategory.Q ⋙ LH ⟶
      H.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (repF : ∀ K, LF.obj (_root_.DerivedCategory.Q.obj K) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (repG : ∀ K, LG.obj (_root_.DerivedCategory.Q.obj K) ⟶
      _root_.DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (repH : ∀ K, LH.obj (_root_.DerivedCategory.Q.obj K) ⟶
      _root_.DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K))
    (hrF : ∀ K, rF.app K = repF K) (hrG : ∀ K, rG.app K = repG K)
    (hrH : ∀ K, rH.app K = repH K)
    (δF : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ LF ≅
      LF.prod LF ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (δG : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)) ⋙ LG ≅
      LG.prod LG ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory E)))
    (δH : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ LH ≅
      LH.prod LH ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory E)))
    (hF : TensorNormalizationAux F LF repF δF)
    (hG : TensorNormalizationAux G LG repG δG)
    (hH : TensorNormalizationAux H LH repH δH)
    (a : LF ⋙ LG ≅ LH) (ν : F ⋙ G ≅ H) [NatTrans.IsMonoidal ν.hom]
    (hrep : ∀ K, a.hom.app (_root_.DerivedCategory.Q.obj K) ≫ repH K =
      LG.map (repF K) ≫ repG ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app K))
    (hiso : ∀ K, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K → IsIso (rH.app K))
    (P Q : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q) :
    a.hom.app (_root_.DerivedCategory.Q.obj P ⊗ _root_.DerivedCategory.Q.obj Q) ≫
        δH.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) =
      LG.map (δF.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q)) ≫
        δG.hom.app (LF.obj (_root_.DerivedCategory.Q.obj P),
          LF.obj (_root_.DerivedCategory.Q.obj Q)) ≫
        (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory E))).map
          (Prod.mkHom (a.hom.app (_root_.DerivedCategory.Q.obj P))
            (a.hom.app (_root_.DerivedCategory.Q.obj Q))) := by
  have : IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) := by
    rw [AlgebraicGeometry.Etale.quotient_tensorator]
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left _root_.DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have := hiso (P ⊗ Q) (ObjectProperty.prop_tensor hP hQ)
  apply normalized_composition_tensor
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) (G.mapHomologicalComplex (.up ℤ))
    (H.mapHomologicalComplex (.up ℤ)) (complexTensorMap F) (complexTensorMap G)
    (complexTensorMap H) LF LG LH rF rG rH
    (fun K L ↦ δF.hom.app (K, L)) (fun K L ↦ δG.hom.app (K, L))
    (fun K L ↦ δH.hom.app (K, L))
    (by intro K L; simpa only [hrF, complexTensorMap] using hF K L)
    (by intro K L; simpa only [hrG, complexTensorMap] using hG K L)
    (by intro K L; simpa only [hrH, complexTensorMap] using hH K L)
    (uncurried_tensor_naturality LG δG.hom) a
    (Functor.mapHomologicalComplexCompIso ν (.up ℤ))
    (complex_compositor_tensor F G H ν)
    (by intro K; simpa only [hrF, hrG, hrH] using hrep K) P Q

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem scalar_comp_tensor_kFlat
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u})
    (P Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj
          (_root_.DerivedCategory.Q.obj P)).obj (_root_.DerivedCategory.Q.obj Q)) ≫
      (tensorIso χ T).hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) =
    (scalarExtension ψ T).map
        ((tensorIso φ T).hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q)) ≫
      (tensorIso ψ T).hom.app
        ((scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj P),
          (scalarExtension φ T).obj (_root_.DerivedCategory.Q.obj Q)) ≫
      (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} C) T)).map
        (Prod.mkHom
          ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
            (_root_.DerivedCategory.Q.obj P))
          ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
            (_root_.DerivedCategory.Q.obj Q))) := by
  have := ordinaryComp_monoidal φ ψ χ hχ T
  simpa only [derivedTensor, curriedTensor_obj_obj, scalarExtension] using
    normalized_cochain_composition
    (ProEtale.etaleSheafExtendScalars φ T) (ProEtale.etaleSheafExtendScalars ψ T)
    (ProEtale.etaleSheafExtendScalars χ T)
    (scalarExtension φ T) (scalarExtension ψ T) (scalarExtension χ T)
    (scalarRepresentativeTransformation φ T) (scalarRepresentativeTransformation ψ T)
    (scalarRepresentativeTransformation χ T)
    (scalarExtensionRepresentative φ T) (scalarExtensionRepresentative ψ T)
    (scalarExtensionRepresentative χ T)
    (scalar_rep_app φ T) (scalar_rep_app ψ T) (scalar_rep_app χ T)
    (tensorIso φ T) (tensorIso ψ T) (tensorIso χ T)
    (scalarExtension_normalizations φ T).2 (scalarExtension_normalizations ψ T).2
    (scalarExtension_normalizations χ T).2
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ)
    (ordinaryComp φ ψ χ hχ T) (scalar_comp_rep φ ψ χ hχ T)
    (scalarRepresentativeTransformation_isIso χ T) P Q hP hQ

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
/-- The published scalar tensor comparison respects the fixed scalar compositor.
Source: blueprint lemma-change-coefficients-internal-hom--1, successive coefficient paragraph;
Stacks 07A4, 0D6D (blueprint: lem-coef-etale-scalar-tensor-composition).

Proof: choose flat-term K-flat complexes P,Q representing U,V. Ordinary scalar extension
preserves their flatness and K-flatness, including for nonflat ring maps. The compositor
is the adjunction mate of the actual restriction compositor; its normalized representative
is ordinary reassociation (x tensor b) tensor c mapped to x tensor psi(b)c. The normalized
tensorator sends (x tensor y) tensor b to (x tensor b) tensor (y tensor 1). Both routes in
the square send ((x tensor y) tensor b) tensor c to
(x tensor psi(b)c) tensor (y tensor 1). These are balanced maps on sheafified tensors,
and their degreewise equalities extend through the direct sums of the signed total
complex. Paste this ordinary square with the all-complex tensor normalization equations
and the scalar-compositor representative equation. All representative maps are
isomorphisms on these models, so cancellation proves the square there. Naturality along
the representing isomorphisms gives the equation for arbitrary unbounded U,V. -/
theorem scalarTensor_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (T : Scheme.{u}) (U V : DerivedCategoryModule A T) :
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj U).obj V) ≫
      (tensorIso χ T).hom.app (U, V) =
    (scalarExtension ψ T).map ((tensorIso φ T).hom.app (U, V)) ≫
      (tensorIso ψ T).hom.app ((scalarExtension φ T).obj U, (scalarExtension φ T).obj V) ≫
      (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} C) T)).map
        (Prod.mkHom
          ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app U)
          ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ).hom.app V)) := by
  let LF := scalarExtension φ T
  let LG := scalarExtension ψ T
  let LH := scalarExtension χ T
  let TA := Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T)
  let TC := Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} C) T)
  let a := ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ hχ
  let α : TA ⋙ LF ⋙ LG ⟶ LH.prod LH ⋙ TC :=
    Functor.whiskerLeft TA a.hom ≫ (tensorIso χ T).hom
  let β : TA ⋙ LF ⋙ LG ⟶ LH.prod LH ⋙ TC :=
    Functor.whiskerRight (tensorIso φ T).hom LG ≫
      Functor.whiskerLeft (LF.prod LF) (tensorIso ψ T).hom ≫
      Functor.whiskerRight (NatTrans.prod a.hom a.hom) TC
  have hab : α = β := by
    apply natTrans_ext_flat α β
    intro P Q hP hQ _ _
    have h := scalar_comp_tensor_kFlat φ ψ χ hχ T P Q hP hQ
    simpa only [α, β, LF, LG, LH, TA, TC, a, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.comp_obj,
      Functor.prod_obj, derivedTensor, curriedTensor_obj_obj,
      curriedTensor_map_app, curriedTensor_obj_map, Functor.uncurry_obj_obj,
      Functor.uncurry_obj_map, NatTrans.prod, MonoidalCategory.tensorHom_def,
      Category.assoc] using h
  exact congrArg (fun t ↦ t.app (U, V)) hab

end AlgebraicGeometry.Etale.ExceptionalCoefficients
