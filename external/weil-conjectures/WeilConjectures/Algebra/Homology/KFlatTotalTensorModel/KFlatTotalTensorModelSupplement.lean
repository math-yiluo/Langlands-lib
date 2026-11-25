/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Sites.Limits

public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
/-!
# Flat-term K-flat total tensor models

Source: Stacks Project, Cohomology on Sites, Tags 07A2 and 07A4;
Modules on Sites, Tag 0G6Q (blueprint: lem-pur-kflat-total-tensor-model).

The helpers below only specialize existing category and tensor constructions.
The derived tensor in the conclusion is exactly the localized bifunctor supplied by
`site_derived_tensor_descent_independentCoefficients`, characterized by its natural
representative comparison.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.KFlatTotalTensorModel

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

private local instance (I : Type r) : HasColimitsOfShape (Discrete I)
    (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

private local instance (I : Type r) : HasColimitsOfShape (Discrete I) (Modules R) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

private local instance (I : Type) : HasColimitsOfShape (Discrete I) (Modules R) := by
  let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _







private theorem total_map_f
    {P P' Q Q' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') (i : ℤ) :
    let := monoidal R
    ((total R).map (Prod.mkHom f g)).f i =
      GradedObject.Monoidal.tensorHom f.f g.f i := by
  let := monoidal R
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  rw [GradedObject.Monoidal.ι_tensorHom]
  change CochainComplex.ιMapBifunctor P Q (tensor R) p q i hpq ≫ _ = _
  simp only [total, Functor.uncurry_obj_map,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex,
    HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f]
  simp [tensor, MonoidalCategory.tensorHom_def]
  rfl

private theorem flat_coproductOnSite {I : Type} (F : I → Modules R)
    (hF : ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (F i)) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) (∐ F) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := monoidal R
  let := SheafOfModules.symmetricCategory R
  have (M : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have (i : I) : PreservesFiniteLimits (tensorLeft (F i)) :=
    (SheafOfModules.flat_to_cat R (F i) (hF i)).1.1
  let : HasSheafify J AddCommGrpCat.{r} := smallSiteHasSheafify (J := J)
  let : HasWeakSheafify J AddCommGrpCat.{r} := HasSheafify.isRightAdjoint
  have : HasColimitsOfShape (Discrete I) AddCommGrpCat.{r} := inferInstance
  have : HasColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{r}) :=
    ⟨fun D ↦ HasColimit.mk ⟨
      Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf J AddCommGrpCat.{r})),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
  have : HasExactColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{r}) :=
    CategoryTheory.Sheaf.hasExactColimitsOfShape J
  have : HasExactColimitsOfShape (Discrete I) (Modules R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete I) (SheafOfModules.toSheaf.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  have : PreservesColimit (Discrete.functor F) (curriedTensor (Modules R)) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor _
  let e : tensorLeft (∐ F) ≅ (Discrete.functor F ⋙ curriedTensor (Modules R)).flip ⋙ colim :=
    preservesColimitIso (curriedTensor (Modules R)) (Discrete.functor F) ≪≫
      colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((Discrete.functor F ⋙ curriedTensor (Modules R)).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (F j.as))))
  have : PreservesFiniteLimits (tensorLeft (∐ F)) := preservesFiniteLimits_of_natIso e.symm
  have hr : exactFunctor _ _ (tensorRight (∐ F)) :=
    ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (∐ F)),
      (inferInstance : PreservesFiniteColimits (tensorRight (∐ F)))⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (∐ F)).symm hr

private theorem totalFlat
    (P Q : CochainComplex (Modules R) ℤ)
    (hP : ∀ p, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p))
    (hQ : ∀ q, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) :
    ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (((total R).obj (P, Q)).X i) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := monoidal R
  have hf (p q : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R)
      ((tensor R).obj (P.X p) |>.obj (Q.X q)) := by
    have h : ObjectProperty.flat (P.X p ⊗ Q.X q) :=
      ObjectProperty.prop_tensor (SheafOfModules.flat_to_cat R _ (hP p))
        (SheafOfModules.flat_to_cat R _ (hQ q))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  intro i
  change SheafOfModules.IsFlatOnSite (J := J) (R := R)
    (∐ fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = i} ↦
      ((tensor R).obj (P.X pq.val.1)).obj (Q.X pq.val.2))
  exact flat_coproductOnSite R _ (fun pq ↦ hf pq.val.1 pq.val.2)

private theorem derivedComparison
    [HasDerivedCategory.{w} (Modules R)]
    (P Q : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (hPflat : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p))
    (hQflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) :
    Nonempty (DerivedCategory.Q.obj ((total R).obj (P, Q)) ≅
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let h := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R
  let S := h.choose
  have hS := h.choose_spec.1
  let B := h.choose_spec.2.2.1.choose
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let d := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let p : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj P,
    (hS _).2 ⟨hP, hPflat⟩⟩
  let q : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj Q,
    (hS _).2 ⟨hQ, hQflat⟩⟩
  exact ⟨((DerivedCategory.quotientCompQhIso (Modules R)).app ((total R).obj (P, Q))).symm ≪≫
    (DerivedCategory.Qh.mapIso (c.app (P, Q))).symm ≪≫ d.app (p, q) ≪≫
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).mapIso
      (((DerivedCategory.quotientCompQhIso (Modules R)).app P).prod
        ((DerivedCategory.quotientCompQhIso (Modules R)).app Q))⟩


end SheafOfModules.KFlatTotalTensorModel
