/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # K-flat resolutions with K-flat stalks -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.RingedSitePoint

/-- There is a K-flat resolution whose stalk at a specified point is K-flat.
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, first paragraph, using
Tags 077J, 06YQ and 06YR.
(auxiliary; not a blueprint node)

Proof: use the reduced flat-resolution functor to present a resolution as a
countable filtered colimit of bounded-above flat complexes. The module stalk
functor preserves colimits by its module adjunction. It preserves flat terms by
geometric inverse-image flatness. The image of each bounded-above complex is
therefore K-flat; exactness of filtered colimits of modules gives K-flatness of
the image of their colimit. The augmentation of the reduced resolution is a
quasi-isomorphism, and its source is K-flat already on the original site. -/
theorem exists_kFlat_resolution
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
    (s : RingedSitePoint R p)
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
      (q : P ⟶ K), P.IsKFlatIndependentCoefficients ∧ QuasiIso q ∧
      (HomologicalComplex.quasiIso (ModuleCat.{w} s.ring) (.up ℤ)).kFlat
        ((s.modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let A := SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  have (I : Type w) : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (I : Type w) : HasColimitsOfShape (Discrete I) A :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive_adapted (R := R)
  have := SheafOfModules.hasTensor_adapted (R := R)
  have := SheafOfModules.hasGoodTensor₁₂_adapted (R := R)
  have := SheafOfModules.hasGoodTensor₂₃_adapted (R := R)
  have := SheafOfModules.hasTensor₄_adapted (R := R)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    SheafOfModules.tensorLeftColimits_adapted R M
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    SheafOfModules.tensorRightColimits_adapted R M
  have (M : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).obj M) := inferInstance
  have (M : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ A := SheafOfModules.hasExactColimits_int_adapted R
  have := SheafOfModules.hasFunctorialFlatResolution_adapted (R := R)
  have : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let P := Λ.resolutionFunctor.obj K
  let q := Λ.resolutionNatTrans.app K
  let presentation := Λ.colimitOfShapeFlatResolutionFunctorObj
    ObjectProperty.flat.essImage_ι_le K
  refine ⟨P, q, SheafOfModules.independent_of_categorical_adapted R _
    (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K), inferInstance, ?_⟩
  have : PreservesColimits s.modules := preservesColimits s
  have : PreservesColimitsOfSize.{0, 0} s.modules := preservesColimitsOfSize_shrink _
  have : AB5OfSize.{0, 0} (ModuleCat.{w} s.ring) := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{w} s.ring) := inferInstance
  have (M : ModuleCat.{w} s.ring) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink _
  have (M : ModuleCat.{w} s.ring) :
      PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{w} s.ring)).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M : ModuleCat.{w} s.ring) :
      PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{w} s.ring)).obj M) :=
    inferInstance
  let F := s.modules.mapHomologicalComplex (.up ℤ)
  apply ObjectProperty.prop_of_isColimit _ (isColimitOfPreserves F presentation.isColimit)
  intro j
  obtain ⟨b, hb⟩ := (presentation.prop_diag_obj j).2
  have := hb
  have : CochainComplex.IsStrictlyLE ((presentation.diag ⋙ F).obj j) b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact s.modules.map_isZero ((presentation.diag.obj j).isZero_of_isStrictlyLE b i hi)
  apply CochainComplex.kFlat_of_isStrictlyLE_of_flat _ b
  intro n
  apply (ModuleCat.flat_iff_flat _).2
  exact s.flat _ (SheafOfModules.flatOnSite_of_categorical_adapted R _
    ((presentation.prop_diag_obj j).1 n))

end CategoryTheory.RingedSitePoint
