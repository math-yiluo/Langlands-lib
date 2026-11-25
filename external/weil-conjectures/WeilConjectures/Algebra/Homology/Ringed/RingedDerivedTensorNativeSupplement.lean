/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
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
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNative

/-! # The native localization tensor at independent ringed-site universes

Source: Stacks Project, Tags 06YS, 06YT and 0FPT.
(blueprint: lem-sf-ringed-derived-native-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures Opposite

namespace CategoryTheory.RingedDerivedNative

section InverseTensorator
variable {A B : Type*} [Category* A] [Category* B]
  [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.LaxMonoidal]

/-- Invertible components of a lax tensorator preserve reassociation. -/
theorem inverse_associativity (X Y Z : A)
    [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F Y Z)]
    [IsIso (Functor.LaxMonoidal.μ F (X ⊗ Y) Z)]
    [IsIso (Functor.LaxMonoidal.μ F X (Y ⊗ Z))] :
    inv (Functor.LaxMonoidal.μ F (X ⊗ Y) Z) ≫
        inv (Functor.LaxMonoidal.μ F X Y) ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ inv (Functor.LaxMonoidal.μ F X (Y ⊗ Z)) ≫
        F.obj X ◁ inv (Functor.LaxMonoidal.μ F Y Z) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y ▷ F.obj Z ≫
    Functor.LaxMonoidal.μ F (X ⊗ Y) Z)).1
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight,
    Category.id_comp, Functor.LaxMonoidal.associativity_assoc,
    IsIso.hom_inv_id_assoc, ← whiskerLeft_comp, IsIso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- Inverting the tensorator and the unit comparison preserves the left unitor. -/
theorem inverse_leftUnitor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F (𝟙_ A) X)] :
    inv (Functor.LaxMonoidal.μ F (𝟙_ A) X) ≫
      inv (Functor.LaxMonoidal.ε F) ▷ F.obj X ≫ (λ_ (F.obj X)).hom =
        F.map (λ_ X).hom := by
  rw [Functor.LaxMonoidal.left_unitality F]
  simp only [← Category.assoc, ← comp_whiskerRight, IsIso.inv_hom_id,
    id_whiskerRight, Category.id_comp]

/-- Inverting the tensorator and the unit comparison preserves the right unitor. -/
theorem inverse_rightUnitor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F X (𝟙_ A))] :
    inv (Functor.LaxMonoidal.μ F X (𝟙_ A)) ≫
      F.obj X ◁ inv (Functor.LaxMonoidal.ε F) ≫ (ρ_ (F.obj X)).hom =
        F.map (ρ_ X).hom := by
  rw [Functor.LaxMonoidal.right_unitality F]
  simp only [← Category.assoc, ← whiskerLeft_comp, IsIso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- Tensor-morphism form of the inverse associativity equation. -/
theorem inverse_associativity_tensor (X Y Z : A)
    [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F Y Z)]
    [IsIso (Functor.LaxMonoidal.μ F (X ⊗ Y) Z)]
    [IsIso (Functor.LaxMonoidal.μ F X (Y ⊗ Z))] :
    inv (Functor.LaxMonoidal.μ F (X ⊗ Y) Z) ≫
        (inv (Functor.LaxMonoidal.μ F X Y) ⊗ₘ 𝟙 (F.obj Z)) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ inv (Functor.LaxMonoidal.μ F X (Y ⊗ Z)) ≫
        (𝟙 (F.obj X) ⊗ₘ inv (Functor.LaxMonoidal.μ F Y Z)) := by
  rw [tensorHom_id, id_tensorHom]
  exact inverse_associativity F X Y Z

/-- Tensor-morphism form of the inverse left-unit equation. -/
theorem inverse_leftUnitor_tensor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F (𝟙_ A) X)] :
    inv (Functor.LaxMonoidal.μ F (𝟙_ A) X) ≫
      (inv (Functor.LaxMonoidal.ε F) ⊗ₘ 𝟙 (F.obj X)) ≫
        (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  rw [tensorHom_id]
  exact inverse_leftUnitor F X

/-- Tensor-morphism form of the inverse right-unit equation. -/
theorem inverse_rightUnitor_tensor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F X (𝟙_ A))] :
    inv (Functor.LaxMonoidal.μ F X (𝟙_ A)) ≫
      (𝟙 (F.obj X) ⊗ₘ inv (Functor.LaxMonoidal.ε F)) ≫
        (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  rw [id_tensorHom]
  exact inverse_rightUnitor F X

end InverseTensorator

section BraidedTensorator
variable {A B : Type*} [Category* A] [Category* B]
  [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
  (F : A ⥤ B) [F.LaxBraided]

/-- Inverting an invertible lax tensorator gives the usual braiding square. -/
theorem inverse_braiding
    (X Y : A) [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F Y X)] :
    inv (Functor.LaxMonoidal.μ F X Y) ≫ (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ inv (Functor.LaxMonoidal.μ F Y X) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y)).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [Functor.LaxBraided.braided (F := F), Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

end BraidedTensorator

section AcyclicTensor
variable {A : Type*} [Category* A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

omit [HasColimitsOfSize.{0, 0} A] [SymmetricCategory A] in
/-- The native derived localization has an invertible unit comparison. -/
theorem localization_isIso_ε [HasDerivedCategory.{w} A]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))] :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q.{w} (C := A))) := by
  have : IsIso (Functor.LaxMonoidal.ε
      (DerivedCategory.Qh.{w} (C := A))) := by
    change IsIso (𝟙 _)
    infer_instance
  change IsIso ((Functor.LaxMonoidal.ε DerivedCategory.Qh ≫
    DerivedCategory.Qh.map (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance

section DerivedSymmetric
variable [HasDerivedCategory.{w} A]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))]
  [(HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

local instance : SymmetricCategory (DerivedCategory A) := derivedSymmetric

end DerivedSymmetric

end AcyclicTensor

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

attribute [local instance] moduleMonoidal moduleSymmetric modulePreadditive moduleClosed
  moduleGrothendieck moduleFlat countableColimits tensorLeftColimits tensorRightColimits

variable [HasDerivedCategory.{w} (Modules.{c, v, u} J R)]

local instance : MonoidalCategory (DerivedCategory (Modules.{c, v, u} J R)) :=
  monoidal.{c, v, u, w} J R

omit [HasDerivedCategory.{w} (Modules.{c, v, u} J R)] in
/-- The native complex tensor is precisely the recorded total tensor.
Source: Stacks Project, Tag 06YN. -/
theorem totalTensor_eq (P L : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj (P, L) = P ⊗ L := by
  rfl

omit [HasDerivedCategory.{w} (Modules.{c, v, u} J R)] in
local instance : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤
    DerivedCategory (Modules.{c, v, u} J R)).LaxMonoidal := lax.{c, v, u, w} J R

/-- The comparison is the inverse of the native lax tensorator. -/
theorem tensorIso_hom (P L : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L)] :
    (tensorIso.{c, v, u, w} J R P L h).hom =
      inv (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L) := rfl

/-- The simultaneous comparison has the specified one-K-flat components. -/
theorem comparison_app
    (P L : ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients
        (J := J) (R := R) : ObjectProperty (CochainComplex (Modules.{c, v, u} J R) ℤ))) :
    (comparison.{c, v, u, w} J R).app (P, L) =
      tensorIso.{c, v, u, w} J R P.obj L.obj (Or.inl P.property) := rfl

local instance : SymmetricCategory (DerivedCategory (Modules.{c, v, u} J R)) :=
  symmetric.{c, v, u, w} J R

/-- Localization preserves the Koszul braiding with its fixed lax tensorator.
Source: Stacks Project, Tag 0FPT. -/
@[instance_reducible]
def laxBraided : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤
    DerivedCategory (Modules.{c, v, u} J R)).LaxBraided := by
  exact localizationLaxBraided (A := Modules.{c, v, u} J R)

/-- The comparison intertwines the native braidings. -/
theorem symmetry_square (P Q : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    (tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
        (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (β_ P Q).hom ≫
        (tensorIso.{c, v, u, w} J R Q P (Or.inl hQ)).hom := by
  let : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤
      DerivedCategory (Modules.{c, v, u} J R)).LaxBraided := laxBraided.{c, v, u, w} J R
  have := isIso_mu.{c, v, u, w} J R P Q (Or.inl hP)
  have := isIso_mu.{c, v, u, w} J R Q P (Or.inl hQ)
  change inv (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ _ =
    _ ≫ inv (Functor.LaxMonoidal.μ DerivedCategory.Q Q P)
  exact inverse_braiding DerivedCategory.Q P Q

/-- The unit comparison of localization is invertible. -/
theorem isIso_ε : IsIso (Functor.LaxMonoidal.ε
    (DerivedCategory.Q.{w} (C := Modules.{c, v, u} J R))) := by
  exact localization_isIso_ε (A := Modules.{c, v, u} J R)

/-- The localization identifies the derived unit with the ring in degree zero.
Source: Stacks Project, Tag 0FPT. -/
def unitIso : 𝟙_ (DerivedCategory (Modules.{c, v, u} J R)) ≅
    DerivedCategory.Q.{w}.obj (𝟙_ (CochainComplex (Modules.{c, v, u} J R) ℤ)) := by
  have := isIso_ε.{c, v, u, w} J R
  exact asIso (Functor.LaxMonoidal.ε DerivedCategory.Q.{w})

/-- The inverse unit comparison is the inverse of the lax unit map. -/
theorem unitIso_inv [IsIso (Functor.LaxMonoidal.ε
    (DerivedCategory.Q.{w} (C := Modules.{c, v, u} J R)))] :
    (unitIso.{c, v, u, w} J R).inv =
      inv (Functor.LaxMonoidal.ε DerivedCategory.Q.{w}) := rfl

/-- The fixed tensor comparison preserves reassociation. -/
theorem associator_square (P Q N : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (hN : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) N) :
    (tensorIso.{c, v, u, w} J R (P ⊗ Q) N (Or.inr hN)).hom ≫
        ((tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ⊗ₘ 𝟙 _) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map (α_ P Q N).hom ≫
        (tensorIso.{c, v, u, w} J R P (Q ⊗ N) (Or.inl hP)).hom ≫
        (𝟙 _ ⊗ₘ (tensorIso.{c, v, u, w} J R Q N (Or.inl hQ)).hom) := by
  have := isIso_mu.{c, v, u, w} J R P Q (Or.inl hP)
  have := isIso_mu.{c, v, u, w} J R Q N (Or.inl hQ)
  have := isIso_mu.{c, v, u, w} J R (P ⊗ Q) N (Or.inr hN)
  have := isIso_mu.{c, v, u, w} J R P (Q ⊗ N) (Or.inl hP)
  exact inverse_associativity_tensor DerivedCategory.Q P Q N

/-- The fixed tensor comparison preserves the left unit constraint. -/
theorem leftUnitor_square (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    (tensorIso.{c, v, u, w} J R (𝟙_ _) P (Or.inr hP)).hom ≫
      ((unitIso.{c, v, u, w} J R).inv ⊗ₘ 𝟙 _) ≫
        (λ_ (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map (λ_ P).hom := by
  have := isIso_mu.{c, v, u, w} J R (𝟙_ _) P (Or.inr hP)
  have := isIso_ε.{c, v, u, w} J R
  exact inverse_leftUnitor_tensor DerivedCategory.Q P

/-- The fixed tensor comparison preserves the right unit constraint. -/
theorem rightUnitor_square (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    (tensorIso.{c, v, u, w} J R P (𝟙_ _) (Or.inl hP)).hom ≫
      (𝟙 _ ⊗ₘ (unitIso.{c, v, u, w} J R).inv) ≫
        (ρ_ (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map (ρ_ P).hom := by
  have := isIso_mu.{c, v, u, w} J R P (𝟙_ _) (Or.inl hP)
  have := isIso_ε.{c, v, u, w} J R
  exact inverse_rightUnitor_tensor DerivedCategory.Q P

end CategoryTheory.RingedDerivedNative
