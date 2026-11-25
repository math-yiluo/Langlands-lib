/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
/-! # Extending tensor comparisons to one K-flat representative

Source: Stacks Project, Tags 06YS, 06YT and 0FPT
(blueprint: lem-sfb-ringed-tensor-comparison-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
open scoped ZeroObject
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
private abbrev Complex := CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ

private theorem oneFlatTensorResolution_isIso
    (F : Complex.{c, v, r} J R ⥤ Complex.{c, v, r} J R)
    (η : F ⟶ 𝟭 _) (hη : ∀ P, QuasiIso (η.app P))
    (hF : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) (F.obj P))
    (P Q : Complex.{c, v, r} J R)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    IsIso (DerivedCategory.Q.{w}.map
      ((coefficientTotalTensor.{r, c, v} J R).map
        (X := (F.obj P, F.obj Q)) (Y := (P, Q)) (η.app P, η.app Q))) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.cochainModulesPreadditive R
  have hp := hη P
  have hq := hη Q
  have hk (X : Complex.{c, v, r} J R)
      (hX : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) X) :
      (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, r} J R) (.up ℤ)).kFlat X := by
    exact (HomotopyCategory.kFlat_quotient_obj_iff X).1
      (RingedDerivedNative.kFlat.{c, v, r} J R X hX)
  have he : QuasiIso
      ((coefficientTotalTensor.{r, c, v} J R).map
        (X := (F.obj P, F.obj Q)) (Y := (P, Q)) (η.app P, η.app Q)) := by
    rcases h with hP | hQ
    · have h₁ := (hk (F.obj Q) (hF Q)).2 (η.app P) hp
      have h₂ := (hk P hP).1 (η.app Q) hq
      have : QuasiIso (η.app P ▷ F.obj Q) := h₁
      have : QuasiIso (P ◁ η.app Q) := h₂
      change QuasiIso ((η.app P ▷ F.obj Q) ≫ (P ◁ η.app Q))
      infer_instance
    · have h₁ := (hk (F.obj P) (hF P)).1 (η.app Q) hq
      have h₂ := (hk Q hQ).2 (η.app P) hp
      have : QuasiIso (F.obj P ◁ η.app Q) := h₁
      have : QuasiIso (η.app P ▷ Q) := h₂
      rw [show (coefficientTotalTensor.{r, c, v} J R).map
        (X := (F.obj P, F.obj Q)) (Y := (P, Q)) (η.app P, η.app Q) =
        (F.obj P ◁ η.app Q) ≫ (η.app P ▷ Q) from
          (whisker_exchange (η.app P) (η.app Q)).symm]
      exact (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, r} J R)
        (.up ℤ)).comp_mem _ _ h₁ h₂
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 he

private def resolvedTensorIso
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (F : Complex.{c, v, r} J R ⥤ Complex.{c, v, r} J R)
    (η : F ⟶ 𝟭 _) (hη : ∀ P, QuasiIso (η.app P))
    (hF : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) (F.obj P))
    (P Q : Complex.{c, v, r} J R)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      S.tensor.obj (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q) :=
  let := hη P
  let := hη Q
  let := oneFlatTensorResolution_isIso.{c, v, r, w} J R F η hη hF P Q h
  (asIso (DerivedCategory.Q.{w}.map
    ((coefficientTotalTensor.{r, c, v} J R).map
        (X := (F.obj P, F.obj Q)) (Y := (P, Q)) (η.app P, η.app Q)))).symm ≪≫
    T.iso J R S (F.obj P) (F.obj Q) (hF P) (hF Q) ≪≫
    S.tensor.mapIso (Iso.prod (asIso (DerivedCategory.Q.{w}.map (η.app P)))
      (asIso (DerivedCategory.Q.{w}.map (η.app Q))))

-- Naturality compares composites through dependent total-tensor and resolution models.
private theorem resolvedTensorIso_naturality
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (F : Complex.{c, v, r} J R ⥤ Complex.{c, v, r} J R)
    (η : F ⟶ 𝟭 _) (hη : ∀ P, QuasiIso (η.app P))
    (hF : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) (F.obj P)) :
    RingedDerivedTensorNaturality J R S (resolvedTensorIso J R S T F η hη hF) := by
  intro P Q P' Q' h h' f g
  let A := coefficientTotalTensor.{r, c, v} J R
  let u := DerivedCategory.Q.{w}.map (A.map
    (X := (F.obj P, F.obj Q)) (Y := (P, Q)) (η.app P, η.app Q))
  let u' := DerivedCategory.Q.{w}.map (A.map
    (X := (F.obj P', F.obj Q')) (Y := (P', Q')) (η.app P', η.app Q'))
  let := hη P
  let := hη Q
  let := hη P'
  let := hη Q'
  let := oneFlatTensorResolution_isIso.{c, v, r, w} J R F η hη hF P Q h
  let := oneFlatTensorResolution_isIso.{c, v, r, w} J R F η hη hF P' Q' h'
  have hA : u ≫ DerivedCategory.Q.{w}.map (A.map (f, g)) =
      DerivedCategory.Q.{w}.map (A.map (F.map f, F.map g)) ≫ u' := by
    dsimp only [u, u']
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 2
    exact Prod.ext (η.naturality f).symm (η.naturality g).symm
  have hB :
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj (F.obj P), DerivedCategory.Q.{w}.obj (F.obj Q)))
        (Y := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
        (DerivedCategory.Q.{w}.map (η.app P), DerivedCategory.Q.{w}.map (η.app Q)) ≫
        S.tensor.map (DerivedCategory.Q.{w}.map f, DerivedCategory.Q.{w}.map g) =
      S.tensor.map (DerivedCategory.Q.{w}.map (F.map f), DerivedCategory.Q.{w}.map (F.map g)) ≫
        S.tensor.map
          (X := (DerivedCategory.Q.{w}.obj (F.obj P'), DerivedCategory.Q.{w}.obj (F.obj Q')))
          (Y := (DerivedCategory.Q.{w}.obj P', DerivedCategory.Q.{w}.obj Q'))
          (DerivedCategory.Q.{w}.map (η.app P'), DerivedCategory.Q.{w}.map (η.app Q')) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Prod.ext
    · change DerivedCategory.Q.{w}.map (η.app P) ≫ DerivedCategory.Q.{w}.map f =
        DerivedCategory.Q.{w}.map (F.map f) ≫ DerivedCategory.Q.{w}.map (η.app P')
      simpa only [← Functor.map_comp, Functor.id_map] using
        congrArg (DerivedCategory.Q.{w}.map) (η.naturality f).symm
    · change DerivedCategory.Q.{w}.map (η.app Q) ≫ DerivedCategory.Q.{w}.map g =
        DerivedCategory.Q.{w}.map (F.map g) ≫ DerivedCategory.Q.{w}.map (η.app Q')
      simpa only [← Functor.map_comp, Functor.id_map] using
        congrArg (DerivedCategory.Q.{w}.map) (η.naturality g).symm
  have hT :
      DerivedCategory.Q.{w}.map (A.map (F.map f, F.map g)) ≫
        (T.iso J R S (F.obj P') (F.obj Q') (hF P') (hF Q')).hom =
      (T.iso J R S (F.obj P) (F.obj Q) (hF P) (hF Q)).hom ≫
        S.tensor.map (DerivedCategory.Q.{w}.map (F.map f),
          DerivedCategory.Q.{w}.map (F.map g)) := by
    exact T.comparison.hom.naturality
      (X := (⟨F.obj P, hF P⟩, ⟨F.obj Q, hF Q⟩))
      (Y := (⟨F.obj P', hF P'⟩, ⟨F.obj Q', hF Q'⟩))
      (ObjectProperty.homMk (F.map f), ObjectProperty.homMk (F.map g))
  apply (cancel_epi u).mp
  change u ≫ (DerivedCategory.Q.{w}.map (A.map (f, g)) ≫
    (inv u' ≫ (T.iso J R S (F.obj P') (F.obj Q') (hF P') (hF Q')).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj (F.obj P'), DerivedCategory.Q.{w}.obj (F.obj Q')))
        (Y := (DerivedCategory.Q.{w}.obj P', DerivedCategory.Q.{w}.obj Q'))
        (DerivedCategory.Q.{w}.map (η.app P'), DerivedCategory.Q.{w}.map (η.app Q')))) =
    u ≫ ((inv u ≫ (T.iso J R S (F.obj P) (F.obj Q) (hF P) (hF Q)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj (F.obj P), DerivedCategory.Q.{w}.obj (F.obj Q)))
        (Y := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
        (DerivedCategory.Q.{w}.map (η.app P), DerivedCategory.Q.{w}.map (η.app Q))) ≫
        S.tensor.map (DerivedCategory.Q.{w}.map f, DerivedCategory.Q.{w}.map g))
  rw [← Category.assoc u, hA]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hT, Category.assoc, hB]

private theorem resolvedTensorIso_both
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (F : Complex.{c, v, r} J R ⥤ Complex.{c, v, r} J R)
    (η : F ⟶ 𝟭 _) (hη : ∀ P, QuasiIso (η.app P))
    (hF : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) (F.obj P)) :
    RingedDerivedTensorBothModel J R S T (resolvedTensorIso J R S T F η hη hF) := by
  intro P Q hP hQ
  let := hη P
  let := hη Q
  let := oneFlatTensorResolution_isIso.{c, v, r, w} J R F η hη hF P Q (Or.inl hP)
  apply Iso.ext
  apply (cancel_epi (DerivedCategory.Q.{w}.map
    ((coefficientTotalTensor.{r, c, v} J R).map
        (X := (F.obj P, F.obj Q)) (Y := (P, Q)) (η.app P, η.app Q)))).mp
  dsimp only [resolvedTensorIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Functor.mapIso_hom, Iso.prod_hom]
  simp only [IsIso.hom_inv_id_assoc]
  exact (T.comparison.hom.naturality
    (X := (⟨F.obj P, hF P⟩, ⟨F.obj Q, hF Q⟩))
    (Y := (⟨P, hP⟩, ⟨Q, hQ⟩))
    (ObjectProperty.homMk (η.app P), ObjectProperty.homMk (η.app Q))).symm

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem flatResolutionFamily :
    ∃ (F : Complex.{c, v, r} J R ⥤ Complex.{c, v, r} J R) (η : F ⟶ 𝟭 _),
      (∀ P, QuasiIso (η.app P)) ∧ ∀ P,
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) (F.obj P) := by
  classical
  let A := RingedTensorModules.{c, v, r} J R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) := by
    have := SheafOfModules.cochainTensorRightPreservesColimits R X
    infer_instance
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ A).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  refine ⟨Λ.resolutionFunctor, Λ.resolutionNatTrans, fun P ↦ inferInstance, ?_⟩
  intro P Z hZ
  have hkF := Λ.kFlat_resolutionFunctor_obj hι P
  let T := MonoidalCategory.tensorRight (Λ.resolutionFunctor.obj P)
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hkF.2 _ hz
  have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

/-- A simultaneous K-flat comparison extends to a natural comparison whenever either factor
is K-flat, retaining its prescribed value when both factors are K-flat.

Source: Stacks Project, Tags 06YS, 06YT and 0FPT
(blueprint: lem-sfb-ringed-tensor-comparison-extension).

Proof: take the reduced functorial flat resolution and its augmentation. Its complexes
are K-flat. Tensoring the two augmentations is a quasi-isomorphism whenever either
unresolved factor is K-flat, by factoring it into tensor products with a K-flat factor.
Invert its localization, apply the given comparison to the two resolutions, and then
apply derived tensor to the localized augmentations. Naturality follows from naturality
of the augmentations and of the original comparison. On two K-flat inputs the same
naturality square identifies the construction with the prescribed comparison. -/
theorem ringedTensorComparison_extension
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S) :
    ∃ t : RingedDerivedTensorComparison.{c, v, r, w} J R S,
      RingedDerivedTensorBothModel.{c, v, r, w} J R S T t ∧
        RingedDerivedTensorNaturality.{c, v, r, w} J R S t := by
  obtain ⟨F, η, hη, hF⟩ := flatResolutionFamily.{c, v, r} J R
  exact ⟨resolvedTensorIso J R S T F η hη hF,
    resolvedTensorIso_both J R S T F η hη hF,
    resolvedTensorIso_naturality J R S T F η hη hF⟩

end CategoryTheory
