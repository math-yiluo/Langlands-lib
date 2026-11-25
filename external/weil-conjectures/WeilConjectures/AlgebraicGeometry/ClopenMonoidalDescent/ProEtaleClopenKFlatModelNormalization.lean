/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Extending the clopen tensor normalization to all K-flat complexes

Source: Stacks Project, sites-cohomology.tex, Tags 06YS and 06YT.
(blueprint: lem-pur-clopen-kflat-model-normalization)
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory RingedDerivedNative.monoidal
  RingedDerivedNative.symmetric HasDerivedCategory.standard coefficientTotalTensor
  SheafOfModules.pushforward

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

private theorem natTrans_eq_of_resolutions
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (α β : F ⟶ G) (good : A → Prop)
    (resolve : ∀ X, ∃ (Y : A) (f : Y ⟶ X), IsIso (F.map f) ∧ good Y)
    (h : ∀ Y, good Y → α.app Y = β.app Y) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, f, hf, hg⟩ := resolve X
  have := hf
  apply (cancel_epi (F.map f)).1
  rw [α.naturality, β.naturality, h Y hg]

private theorem flat_resolution {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (P : CochainComplex (clopenTensorModules.{t, u} R) ℤ) :
    ∃ (V : CochainComplex (clopenTensorModules.{t, u} R) ℤ) (f : V ⟶ P),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) V ∧
      (∀ n, SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (V.X n)) ∧ QuasiIso f := by
  obtain ⟨V, f, hf, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) P
  exact ⟨V, f, hf, fun n ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (V.X n)).symm (hflat n), hq⟩

-- Elaborating both natural-isomorphism composites involves large dependent functor types.
/-- The normalization on flat-term K-flat models extends to every K-flat pair.
Source: Stacks Project, sites-cohomology.tex, Tags 06YS and 06YT
(blueprint: lem-pur-clopen-kflat-model-normalization).

Proof: the two sides of the model square are natural isomorphisms on pairs of K-flat
complexes, using the native comparison and the restricted K-flat comparison. Resolve
each input by a flat-term K-flat complex. The maps of resolutions become isomorphisms
under localization, hence also under tensor and restriction. Naturality and cancellation
transport the known square on the resolving pair to the given pair. No termwise flatness
of the given pair, boundedness, or nonzero coefficient assumption is needed. -/
theorem clopen_kflat_model_normalization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (hk : ∀ P : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients
        (R := (clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P))
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y)
            ((clopenTensorRings.{t, u} j).obj R))
    (c : Comparison.{t, u} j R) (h : ModelNormalization.{t, u} j R b c)
    (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (hiP : CochainComplex.IsKFlatIndependentCoefficients
      (R := (clopenTensorRings.{t, u} j).obj R)
      ((clopenTensorComplexRestriction.{t, u} j R).obj P)) :
    (derivedRestriction.{t, u} j R).map
        (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology X) R P Q (Or.inl hP)).hom ≫
      c.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      tensorHom ((factors.{t, u} j R).hom.app P) ((factors.{t, u} j R).hom.app Q) =
    (factors.{t, u} j R).hom.app
        ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) ≫
      DerivedCategory.Q.map (b.hom.app (P, Q)) ≫
      (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology Y)
        ((clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P)
        ((clopenTensorComplexRestriction.{t, u} j R).obj Q) (Or.inl hiP)).hom := by
  let K := coefficientKFlatInclusion.{u, t + 1, t} (topology X) R
  let S := (clopenTensorRings.{t, u} j).obj R
  let r := clopenTensorComplexRestriction.{t, u} j R
  let rK := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (R := S)) (K ⋙ r)
    (fun A ↦ hk A.obj A.property)
  let T := coefficientTotalTensor.{u, t + 1, t} (topology X) R
  let D := derivedRestriction.{t, u} j R
  let A := Functor.isoWhiskerRight
    (RingedDerivedNative.comparison.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology X) R) D
  let B := Functor.isoWhiskerLeft ((K ⋙ DerivedCategory.Q).prod
    (K ⋙ DerivedCategory.Q)) c
  let C := Functor.isoWhiskerRight
    (NatIso.prod (Functor.isoWhiskerLeft K (factors.{t, u} j R))
      (Functor.isoWhiskerLeft K (factors.{t, u} j R)))
    (tensor (DerivedCategory (clopenTensorModules.{t, u} S)))
  let F := (K.prod K) ⋙ T ⋙ DerivedCategory.Q ⋙ D
  let G := ((K ⋙ r ⋙ DerivedCategory.Q).prod (K ⋙ r ⋙ DerivedCategory.Q)) ⋙
    tensor (DerivedCategory (clopenTensorModules.{t, u} S))
  let α : F ≅ G := A ≪≫ B ≪≫ C
  let β₁ := Functor.isoWhiskerLeft (K.prod K)
    (Functor.isoWhiskerLeft T (factors.{t, u} j R))
  let β₂ := Functor.isoWhiskerLeft (K.prod K)
    (Functor.isoWhiskerRight b DerivedCategory.Q)
  let β₃ := Functor.isoWhiskerLeft (rK.prod rK)
    (RingedDerivedNative.comparison.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) S)
  let β : F ≅ G := β₁ ≪≫ β₂ ≪≫ β₃
  have he : α.hom = β.hom := by
    apply natTrans_eq_of_resolutions α.hom β.hom
      (fun Z ↦ (∀ n, SheafOfModules.IsFlatOnSite (J := topology X)
          (R := R) (Z.1.obj.X n)) ∧
        (∀ n, SheafOfModules.IsFlatOnSite (J := topology X)
          (R := R) (Z.2.obj.X n)))
    · rintro ⟨V, W⟩
      obtain ⟨V', f, hf, hff, hfi⟩ := flat_resolution R V.obj
      obtain ⟨W', g, hg, hgf, hgi⟩ := flat_resolution R W.obj
      have := hfi
      have := hgi
      let f' := ObjectProperty.homMk (P := CochainComplex.IsKFlatIndependentCoefficients
        (R := R)) (X := ⟨V', hf⟩) (Y := V) f
      let g' := ObjectProperty.homMk (P := CochainComplex.IsKFlatIndependentCoefficients
        (R := R)) (X := ⟨W', hg⟩) (Y := W) g
      let z : (⟨V', hf⟩, ⟨W', hg⟩) ⟶ (V, W) := (f', g')
      have hz : IsIso ((K ⋙ DerivedCategory.Q).map f') := by
        change IsIso (DerivedCategory.Q.map f)
        infer_instance
      have hz' : IsIso ((K ⋙ DerivedCategory.Q).map g') := by
        change IsIso (DerivedCategory.Q.map g)
        infer_instance
      let G' := ((K ⋙ DerivedCategory.Q).prod (K ⋙ DerivedCategory.Q)) ⋙
        tensor (DerivedCategory (clopenTensorModules.{t, u} R)) ⋙ D
      have hG : IsIso (G'.map z) := by
        change IsIso (D.map (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g))
        infer_instance
      have : IsIso (F.map z) := (NatIso.isIso_map_iff A z).mpr hG
      exact ⟨(⟨V', hf⟩, ⟨W', hg⟩), z, inferInstance, hff, hgf⟩
    · rintro ⟨V, W⟩ ⟨hV, hW⟩
      exact h V.obj W.obj V.property W.property hV hW (hk V.obj V.property)
  exact NatTrans.congr_app he (⟨P, hP⟩, ⟨Q, hQ⟩)

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
