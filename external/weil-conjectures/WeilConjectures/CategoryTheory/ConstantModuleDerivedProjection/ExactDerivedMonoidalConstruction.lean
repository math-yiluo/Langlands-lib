/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.DerivedProjectionComparisonSquares
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Mathlib.CategoryTheory.Whiskering

/-! # Construction of normalized exact derived monoidal functors

Source: Stacks Project, Tags 07A4, 0FPQ and 0FPT.
(blueprint: lem-sfb-exact-derived-monoidal-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.ConstantModuleDerivedProjection
section AbstractLocalization
open CategoryTheory.Category CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

private def property_localizer {B : Type*} [Category* B]
    (W : MorphismProperty B) (S : ObjectProperty B) :
    LocalizerMorphism (W.inverseImage S.ι) W where
  functor := S.ι
  map := by rfl

private theorem monoidal_localization
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    (Q : B ⥤ F) (L : E ⥤ H) (G : B ⥤ E) (V : F ⥤ H)
    [Q.LaxMonoidal] [L.LaxMonoidal] [G.Monoidal]
    (e : Q ⋙ V ≅ G ⋙ L) (W : MorphismProperty B) (S : ObjectProperty B)
    [W.ContainsIdentities] [W.RespectsIso] [Q.IsLocalization W]
    [(property_localizer W S).IsLeftDerivabilityStructure]
    [IsIso (ε Q)] [IsIso (ε L)]
    (hmodels : ∀ X : F, ∃ P, S P ∧ Nonempty (Q.obj P ≅ X))
    (hQ : ∀ P R, S R → IsIso (μ Q P R))
    (hL : ∀ (X : E) R, S R → IsIso (μ L X (G.obj R))) :
    ∃ m : V.Monoidal, letI := m
      ∀ P R, δ V (Q.obj P) (Q.obj R) ≫
        (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := by
  let T := (((whiskeringLeft₂ H).obj V).obj V).obj (curriedTensor H)
  let U := (postcompose₂.obj V).obj (curriedTensor F)
  let a : (((whiskeringLeft₂ H).obj Q).obj Q).obj T ⟶
      (((whiskeringLeft₂ H).obj G).obj G).obj
        ((postcompose₂.obj L).obj (curriedTensor E)) :=
    (((whiskeringLeft₂ H).map e.hom).app (Q ⋙ V)).app (curriedTensor H) ≫
      (((whiskeringLeft₂ H).obj (G ⋙ L)).map e.hom).app (curriedTensor H) ≫
      (((whiskeringLeft₂ H).obj G).obj G).map (μNatTrans L)
  have ha P R : (a.app P).app R =
      (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) := by
    dsimp [a]
    rw [tensorHom_def, assoc]
    rfl
  let b : (((whiskeringLeft₂ H).obj Q).obj Q).obj U ⟶
      (((whiskeringLeft₂ H).obj G).obj G).obj
        ((postcompose₂.obj L).obj (curriedTensor E)) :=
    (postcompose₂.obj V).map (μNatTrans Q) ≫
      (postcompose₂.map e.hom).app (curriedTensor B) ≫
      postcompose₂MapWhiskeringLeft₂ (δNatTrans G) L
  have hb P R : (b.app P).app R =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := rfl
  have : T.IsLeftDerivedFunctor₂ a W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (property_localizer W S) a
    intro P R
    have := hL (G.obj P) R.obj R.property
    change IsIso ((a.app P).app R.obj)
    rw [ha]
    infer_instance
  have : U.IsLeftDerivedFunctor₂ b W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) (property_localizer W S) b
    intro P R
    have := hQ P R.obj R.property
    change IsIso (V.map (μ Q P R.obj) ≫ e.hom.app (P ⊗ R.obj) ≫
      L.map (δ G P R.obj))
    infer_instance
  let t : U ≅ T := leftDerived₂NatIso T a W W U b (Iso.refl _)
  have ht P R : (t.hom.app (Q.obj P)).app (Q.obj R) ≫
      (e.hom.app P ⊗ₘ e.hom.app R) ≫ μ L (G.obj P) (G.obj R) =
      V.map (μ Q P R) ≫ e.hom.app (P ⊗ R) ≫ L.map (δ G P R) := by
    have h := leftDerived₂NatTrans_app_app T a W W U b (𝟙 _) P R
    rw [ha, hb] at h
    exact h.trans (Category.comp_id _)
  let : V.OplaxMonoidal := .ofLaxSquare t.hom (fun P ↦ e.hom.app P)
    (fun _ _ f ↦ e.hom.naturality f) ht S hmodels hL
  have (X Y : F) : IsIso (δ V X Y) :=
    inferInstanceAs (IsIso ((t.hom.app X).app Y))
  have : IsIso (η V) := by
    change IsIso (V.map (ε Q) ≫ e.hom.app _ ≫ L.map (η G) ≫ inv (ε L))
    infer_instance
  exact ⟨.ofOplaxMonoidal V, ht⟩

universe a b ha hb wa wb
variable {B : Type a} [Category.{ha} B] [Abelian B]
  [IsGrothendieckAbelian.{ha} B] [HasColimitsOfSize.{0, 0} B]
  [MonoidalCategory B] [MonoidalClosed B] [MonoidalPreadditive B] [BraidedCategory B]
  [Abelian.HasFunctorialFlatResolution B] [HasDerivedCategory.{wa} B]
  {E : Type b} [Category.{hb} E] [Abelian E]
  [IsGrothendieckAbelian.{hb} E] [HasColimitsOfSize.{0, 0} E]
  [MonoidalCategory E] [MonoidalClosed E] [MonoidalPreadditive E] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory.{wb} E]

private theorem tensor_localization_iso (P R : CochainComplex E ℤ)
    (hR : R.IsKFlatForTotalTensor) : IsIso (μ DerivedCategory.Q P R) := by
  have : IsIso (μ DerivedCategory.Qh
      ((HomotopyCategory.quotient E (.up ℤ)).obj P)
      ((HomotopyCategory.quotient E (.up ℤ)).obj R)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso E (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff R).2 hR)
  change IsIso ((_ ⊗ₘ _) ≫
    (μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

/-- An exact flat-preserving monoidal functor has a representative-normalized derived
strong monoidal structure, for the chosen derived-category universes.
Source: Stacks Project, Derived Categories, Tags 0FPQ and 0FPT, and Cohomology on Sites,
Tag 07A4 (blueprint: lem-sfb-exact-derived-monoidal-construction).

Proof: take the subcategory of source K-flat complexes whose termwise images are K-flat.
Functorial flat-term resolutions land in it, because the functor preserves flat objects
and the countable colimits used to form these resolutions. Its inclusion is therefore a
left derivability structure. Derive the source and target tensor bifunctors: their
comparison maps are invertible when the second input lies in this subcategory. The
canonical isomorphism between these two left-derived bifunctors gives an oplax tensorator.
The defining representative equation and `ofLaxSquare` transfer all associativity and
unit axioms. Its tensor components and its unit are invertible, so the structure is strong.
The left-derived comparison factor equation is the asserted normalization. The argument
uses the chosen localization functors directly and does not compare localization universes. -/
theorem exact_monoidal_normalization
    (G : B ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesColimitsOfSize.{0, 0} G] [G.PreservesFlat] (m : G.Monoidal) :
    ∃ n : G.mapDerivedCategory.Monoidal, TensorNormalization B E G m n := by
  letI := m
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let S : ObjectProperty (CochainComplex B ℤ) := W.kFlat ⊓
    (HomologicalComplex.quasiIso E (.up ℤ)).kFlat.inverseImage
      (G.mapHomologicalComplex (.up ℤ))
  let Φ := property_localizer W S
  have : HasExactColimitsOfShape ℤ B := by
    have := AB5OfSize_of_univLE.{0, 0, ha, ha} B
    infer_instance
  have : HasExactColimitsOfShape ℤ E := by
    have := AB5OfSize_of_univLE.{0, 0, hb, hb} E
    infer_instance
  have (X : E) : PreservesColimitsOfShape ℤ ((curriedTensor E).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution B).some.reduced
  have hρ (P : CochainComplex B ℤ) : S (Λ.resolutionFunctor.obj P) :=
    ⟨Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P,
      G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
        ObjectProperty.flat.essImage_ι_le P⟩
  have : Φ.functor.Full := inferInstanceAs S.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs S.ι.Faithful
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLeftDerivabilityStructure :=
    Φ.isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift S Λ.resolutionFunctor hρ) Λ.resolutionNatTrans
      (fun P ↦ by
        change HomologicalComplex.quasiIso B (.up ℤ) _
        rw [HomologicalComplex.mem_quasiIso_iff]
        exact Λ.quasiIso_resolutionNatTrans_app P) rfl
  have : IsIso (ε (DerivedCategory.Q (C := B))) :=
    RingedDerivedNative.localization_isIso_ε
  have : IsIso (ε (DerivedCategory.Q (C := E))) :=
    RingedDerivedNative.localization_isIso_ε
  have hmodels (X : DerivedCategory B) :
      ∃ P, S P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let P := DerivedCategory.Q.objPreimage X
    have : QuasiIso (Λ.resolutionNatTrans.app P) := Λ.quasiIso_resolutionNatTrans_app P
    exact ⟨Λ.resolutionFunctor.obj P, hρ P,
      ⟨asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app P)) ≪≫
        DerivedCategory.Q.objObjPreimageIso X⟩⟩
  obtain ⟨n, hn⟩ := monoidal_localization DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategory G.mapDerivedCategoryFactors W S
    hmodels (fun P R hR ↦ tensor_localization_iso P R hR.1)
    (fun X R hR ↦ tensor_localization_iso X _ hR.2)
  refine ⟨n, ?_⟩
  intro P R _ _
  simpa only [Functor.mapCochainComplex_δ, Functor.mapCochainComplexμIso_inv] using hn P R

end AbstractLocalization
end CategoryTheory.ConstantModuleDerivedProjection
