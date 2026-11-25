/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.LaxComplex.CanonicalTensorComplex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Localization.LaxMonoidal.CanonicalTensorLocalization
/-!
# Normalized derived lax tensor for an exact functor

An exact additive lax monoidal functor induces a lax monoidal functor on the native
unbounded derived categories. Descend through the strong monoidal localization of
K-flat source complexes, then transport the normalization to arbitrary complexes by
functorial K-flat quasi-isomorphisms. The functor need not preserve flat objects.

Source: blueprint local boundary duality, Step 5, deriving the evaluation tensor pairing.
(blueprint: lem-a1-canonical-lax-derived)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u vA vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.CanonicalDerivedLax
section
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
private theorem tensor_square_of_cover (e : F ≅ G) {P Q P' Q' : C}
    (f : P' ⟶ P) (g : Q' ⟶ Q) [IsIso (F.map f)] [IsIso (F.map g)]
    (h : Functor.LaxMonoidal.μ F P' Q' ≫ e.hom.app (P' ⊗ Q') =
      (e.hom.app P' ⊗ₘ e.hom.app Q') ≫ Functor.LaxMonoidal.μ G P' Q') :
    Functor.LaxMonoidal.μ F P Q ≫ e.hom.app (P ⊗ Q) =
      (e.hom.app P ⊗ₘ e.hom.app Q) ≫ Functor.LaxMonoidal.μ G P Q := by
  apply (cancel_epi (F.map f ⊗ₘ F.map g)).mp
  rw [Functor.LaxMonoidal.μ_natural_assoc, e.hom.naturality,
    ← Category.assoc, h]
  simp only [Category.assoc, ← Functor.LaxMonoidal.μ_natural]
  rw [← Category.assoc, tensorHom_comp_tensorHom, ← e.hom.naturality,
    ← e.hom.naturality, ← tensorHom_comp_tensorHom]
  rw [Category.assoc]

end

variable {A B : Type*} [Category.{u} A] [Category.{u} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u} A] [IsGrothendieckAbelian.{u} B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [MonoidalClosed A] [MonoidalClosed B] [SymmetricCategory A] [SymmetricCategory B]
    [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B]
    [HasDerivedCategory.{vA} A] [HasDerivedCategory.{vB} B]
    (F : A ⥤ B) [F.Additive] [F.LaxMonoidal]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exact-derived lax monoidality with the specified chain-level normalization.

Proof: the inclusion of K-flat complexes followed by localization is strong monoidal.
Compose the termwise lax structure with target localization and descend along this
strong localization, using the canonical exact-derived factor as lifting. The descent
formulas give the unit equation and the tensor equation on K-flat complexes. For any
P,Q, precompose the two tensor equations by the localized K-flat resolutions. Naturality
identifies them, and their invertible images cancel to give the equation on P,Q.
Source: blueprint local boundary duality, Step 5, derived evaluation pairing.
(blueprint: lem-a1-canonical-lax-derived) -/
theorem exists_normalized :
    ∃ m : F.mapDerivedCategory.LaxMonoidal,
      (m.ε ≫ F.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
        F.mapDerivedCategoryFactors.hom.app (𝟙_ _) =
          Functor.LaxMonoidal.ε DerivedCategory.Q ≫
            DerivedCategory.Q.map (Functor.LaxComplex.chainUnit F)) ∧
      (∀ P Q : CochainComplex A ℤ,
        m.μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) =
        (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
          DerivedCategory.Q.map (Functor.LaxComplex.chainTensor F P Q)) := by
  let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
  let : HasColimitsOfSize.{0, 0} B := hasColimitsOfSizeShrink B
  let : MonoidalCategory (CochainComplex A ℤ) := inferInstance
  let : MonoidalCategory (CochainComplex B ℤ) := inferInstance
  let : MonoidalCategory (DerivedCategory A) := inferInstance
  let : MonoidalCategory (DerivedCategory B) := inferInstance
  let := Functor.LaxComplex.mapCochainComplexLax F
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let I := W.ιKFlat
  let L := I ⋙ (DerivedCategory.Q (C := A))
  let G := (I ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙ (DerivedCategory.Q (C := B))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  have : W.localizerMorphismKFlat.IsLocalizedEquivalence :=
    W.localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions
      (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  have : L.IsLocalization W.WKFlat :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization W.localizerMorphismKFlat
      DerivedCategory.Q
  let : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := A))) :=
    RingedDerivedNative.localization_isIso_ε
  have (P Q : W.KFlat) : IsIso (Functor.LaxMonoidal.μ L P Q) := by
    have hh := RingedDerivedNative.localization_isIso_mu P.obj Q.obj
      (Or.inl ((HomotopyCategory.kFlat_quotient_obj_iff P.obj).2 P.property))
    change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.μ I P Q))
    infer_instance
  have : IsIso (Functor.LaxMonoidal.ε L) := by
    dsimp only [L, Functor.LaxMonoidal.comp_ε]
    infer_instance
  let : L.Monoidal := Functor.Monoidal.ofLaxMonoidal L
  let : Localization.Lifting L W.WKFlat G F.mapDerivedCategory :=
    ⟨Functor.associator I DerivedCategory.Q F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft I F.mapDerivedCategoryFactors ≪≫
        (Functor.associator I (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).symm⟩
  let m := Localization.LaxMonoidal.functorLaxMonoidalOfComp L W.WKFlat
    F.mapDerivedCategory G
  have eh (P : W.KFlat) :
      (Localization.Lifting.iso L W.WKFlat G F.mapDerivedCategory).hom.app P =
        F.mapDerivedCategoryFactors.hom.app P.obj := by
    change (𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app P.obj ≫ 𝟙 _) = _
    simp
  have εH : Functor.LaxMonoidal.ε (F.mapHomologicalComplex (.up ℤ)) =
      Functor.LaxComplex.chainUnit F := rfl
  have μH (P Q : CochainComplex A ℤ) :
      Functor.LaxMonoidal.μ (F.mapHomologicalComplex (.up ℤ)) P Q =
        Functor.LaxComplex.chainTensor F P Q := rfl
  refine ⟨m, ?_, ?_⟩
  · simpa [G, L, I, Functor.LaxMonoidal.comp_ε, eh, εH, Category.assoc] using
      Localization.LaxMonoidal.functorLaxMonoidalOfComp_unit L W.WKFlat
        F.mapDerivedCategory G
  · have hk (P Q : W.KFlat) :
        m.μ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) ≫
          F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj) ≫
          F.mapDerivedCategoryFactors.hom.app (P.obj ⊗ Q.obj) =
        (F.mapDerivedCategoryFactors.hom.app P.obj ⊗ₘ
          F.mapDerivedCategoryFactors.hom.app Q.obj) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
          DerivedCategory.Q.map (Functor.LaxComplex.chainTensor F P.obj Q.obj) := by
      simpa [G, L, I, Functor.LaxMonoidal.comp_μ, eh, μH, Category.assoc] using
        Localization.LaxMonoidal.functorLaxMonoidalOfComp_tensor L W.WKFlat
          F.mapDerivedCategory G P Q
    intro P Q
    let R := Λ.kFlatResolutionFunctor ObjectProperty.flat.essImage_ι_le
    let π := Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le
    let := m
    have hp : IsIso (DerivedCategory.Q.map (π.app P)) := by infer_instance
    have hq : IsIso (DerivedCategory.Q.map (π.app Q)) := by infer_instance
    have hp' : IsIso ((DerivedCategory.Q ⋙ F.mapDerivedCategory).map (π.app P)) := by
      change IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map (π.app P)))
      infer_instance
    have hq' : IsIso ((DerivedCategory.Q ⋙ F.mapDerivedCategory).map (π.app Q)) := by
      change IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map (π.app Q)))
      infer_instance
    have hh := hk (R.obj P) (R.obj Q)
    have hh' : Functor.LaxMonoidal.μ (DerivedCategory.Q ⋙ F.mapDerivedCategory)
        (R.obj P).obj (R.obj Q).obj ≫
        F.mapDerivedCategoryFactors.hom.app ((R.obj P).obj ⊗ (R.obj Q).obj) =
        (F.mapDerivedCategoryFactors.hom.app (R.obj P).obj ⊗ₘ
          F.mapDerivedCategoryFactors.hom.app (R.obj Q).obj) ≫
        Functor.LaxMonoidal.μ (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
          (R.obj P).obj (R.obj Q).obj := by
      simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map,
        Category.assoc, μH] using hh
    simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map,
      Category.assoc, Functor.id_obj, μH] using
      tensor_square_of_cover F.mapDerivedCategoryFactors (π.app P) (π.app Q) hh'
end CategoryTheory.CanonicalDerivedLax
