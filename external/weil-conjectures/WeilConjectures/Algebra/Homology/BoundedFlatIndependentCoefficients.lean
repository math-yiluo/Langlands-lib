/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
/-! # Bounded flat complexes at independent coefficient universes

Source: Stacks Project, Tag 06YQ.
(auxiliary; not a blueprint node). -/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
set_option hygiene false in
local notation "𝒜" => SheafOfModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
/-- Tensor of module sheaves is preadditive at independent site and coefficient universes. -/
theorem tensorPreadditive :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    MonoidalPreadditive 𝒜 := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let (M : 𝒜) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : 𝒜) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

/-- Site-flatness implies categorical flatness for the sheaf tensor product. -/
theorem flat_to_cat (M : 𝒜) (h : IsFlatOnSite (J := J) (R := R) M) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    ObjectProperty.flat M := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  have hr : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) h
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight M).symm hr, hr⟩

/-- A bounded-above complex with flat terms is K-flat at independent universes.
Source: Stacks Project, Cohomology on Sites, Tag 06YQ.
(auxiliary; not a blueprint node).

Proof: the site tensor functor is naturally isomorphic to the monoidal tensor
functor, by the sheafification counit and its monoidal tensor comparison. Thus
site-flatness of each term gives categorical flatness. Tensor colimit preservation
makes tensor additive and gives the graded tensor instances. Filtered colimits of
abelian groups are exact; forgetting sheaf-module structure preserves and reflects
exactness, so sequential colimits of module sheaves are exact as well. Apply the
source-library bounded-above flat criterion, proved from finite flat stupid
truncations and their filtered colimit. It says tensoring preserves quasi-isomorphisms.
Apply it to the map from the zero complex to an arbitrary acyclic complex. Its
source tensor is zero, so the target tensor is acyclic. This is exactly independent-
coefficient K-flatness. Zero rings and the zero complex require no separate case. -/
theorem isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (P : CochainComplex 𝒜 ℤ) (n : ℤ) [P.IsStrictlyLE n]
    (hflat : ∀ i, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    P.IsKFlatIndependentCoefficients := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (I : Type w) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (M : 𝒜) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : 𝒜) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ : GradedObject ℤ 𝒜, GradedObject.HasTensor X₁ X₂ := by
    infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ 𝒜,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ 𝒜,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ 𝒜,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have : AB5OfSize.{w, w} AddCommGrpCat.{w} := inferInstance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℤ 𝒜 :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  have hk : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P n (fun i ↦ flat_to_cat R _ (hflat i))
  intro Z hZ
  let T := MonoidalCategory.tensorRight P
  have hz : QuasiIso (0 : (0 : CochainComplex 𝒜 ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex 𝒜 ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex 𝒜 ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex 𝒜 ℤ) ⟶ Z)) i).1 (htzero i)

end SheafOfModules
