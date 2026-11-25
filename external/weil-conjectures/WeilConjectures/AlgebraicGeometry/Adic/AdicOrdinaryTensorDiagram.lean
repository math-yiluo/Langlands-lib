/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientDiagram
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Ordinary algebraic quotient tensor diagrams

Source: Stacks Project, More on Algebra, Tag 09AW; More on Algebra, Tag 06Y6.
(blueprint: lem-weil-pbc-adic-ordinary-tensor-levels).
The coefficient maps are the actual quotient homomorphisms, viewed as linear maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The quotient rings as a diagram of modules over the original ring.
Source: Stacks Project, Tag 09AW. -/
def adicOrdinaryCoefficientDiagram {A : Type t} [CommRing A] (I : Ideal A) :
    ℕᵒᵖ ⥤ ModuleCat.{t} A :=
  Functor.ofOpSequence (X := fun n ↦ ModuleCat.of A (A ⧸ I ^ (n + 1)))
    (fun n : ℕ ↦ ModuleCat.ofHom
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap)

/-- Tensor an algebraic module with the full quotient coefficient diagram.
Source: Stacks Project, Tag 09AW. -/
def adicOrdinaryTensorFunctor {A : Type t} [CommRing A] (I : Ideal A) :
    ModuleCat.{t} A ⥤ (ℕᵒᵖ ⥤ ModuleCat.{t} A) :=
  curriedTensor (ModuleCat.{t} A) ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (ModuleCat.{t} A) (ModuleCat.{t} A)).obj
      (adicOrdinaryCoefficientDiagram I)

instance adicOrdinaryTensorFunctor_additive {A : Type t} [CommRing A] (I : Ideal A) :
    (adicOrdinaryTensorFunctor I).Additive := by
  unfold adicOrdinaryTensorFunctor
  infer_instance

/-- Apply the ordinary coefficient tensors in every cochain degree.
Source: Stacks Project, Tag 09AW. -/
def adicOrdinaryTensorComplexDiagram {A : Type t} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{t} A) ℤ :=
  (((adicOrdinaryTensorFunctor I).mapHomologicalComplex (.up ℤ)).obj P).asFunctor

private theorem algebraicFlatResolution (A : Type t) [CommRing A] :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (ModuleCat.{t} A) := by
  classical
  let F := ObjectProperty.lift ObjectProperty.flat
    (CategoryTheory.forget (ModuleCat.{t} A) ⋙ ModuleCat.free A) (fun M ↦ by
      apply (ModuleCat.flat_iff_flat _).2
      change Module.Flat A (M →₀ A)
      infer_instance)
  refine ⟨{ F := F, π := (ModuleCat.adj A).counit, epi_π_app := ?_ }⟩
  intro M
  apply (ModuleCat.epi_iff_surjective _).2
  intro x
  refine ⟨ModuleCat.freeMk x, ?_⟩
  change ModuleCat.freeDesc (𝟙 (CategoryTheory.forget (ModuleCat.{t} A)).obj M)
    (ModuleCat.freeMk x) = x
  simp only [ModuleCat.freeDesc_apply]
  rfl

/-- K-flatness makes the transpose of the localized ordinary unit invertible.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-weil-pbc-adic-ordinary-tensor-levels).
Proof: apply the exact-right-adjoint K-flat representative criterion, using free
module flat resolutions and preservation of K-flat quasi-isomorphisms by scalar extension. -/
theorem adicOrdinaryTranspose_isIso
    {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B)
    (L : DerivedCategory (ModuleCat.{t} A) ⥤ DerivedCategory (ModuleCat.{t} B))
    (ad : L ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (hP : P.IsKFlatForTotalTensor) :
    IsIso ((ad.homEquiv _ _).symm
      (DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{t, t, t} φ).mapHomologicalComplex
          (.up ℤ)).unit.app P) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{t, t, t} φ).mapHomologicalComplex (.up ℤ)).obj P))) := by
  have := algebraicFlatResolution A
  have : AB5OfSize.{0, 0} (ModuleCat.{t} A) := AB5OfSize_of_univLE.{0, 0, t, t} _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{t} A) := inferInstance
  have : (ModuleCat.extendScalars.{t, t, t} φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{t, t, t} φ).left_adjoint_additive
  have := ModuleCat.extendScalars_preservesKFlatQuasiIso φ
  exact Adjunction.isIso_cochainTranspose_of_kFlat _ _
    (ModuleCat.extendRestrictScalarsAdj.{t, t, t} φ) ad P
    ⟨fun _ _ s hs ↦ hP.1 s hs, fun _ _ s hs ↦ hP.2 s hs⟩

/-- Restriction of ordinary scalar extension is tensor with the coefficient module.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-weil-pbc-adic-ordinary-tensor-levels). -/
def adicOrdinaryRestrictedTensorIso
    {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ModuleCat.extendScalars.{t, t, t} φ ⋙ ModuleCat.restrictScalars φ ≅
      tensorRight ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)) := by
  let F := ModuleCat.extendScalars.{t, t, t} φ
  let V : ModuleCat.{t} A := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)
  let eobj (M : ModuleCat.{t} A) :
      (F ⋙ ModuleCat.restrictScalars φ).obj M ≅ (tensorLeft V).obj M :=
    (AddEquiv.toLinearEquiv (M := ↑((F ⋙ ModuleCat.restrictScalars φ).obj M))
      (M₂ := ↑((tensorLeft V).obj M)) (AddEquiv.refl _) (by
        intro r z
        induction z using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add a b ha hb =>
            simpa only [map_add, smul_add] using congrArg₂ (· + ·) ha hb)).toModuleIso
  let e : F ⋙ ModuleCat.restrictScalars φ ≅ tensorLeft V :=
    NatIso.ofComponents eobj (by intro M N f; ext z; rfl)
  exact e ≪≫ BraidedCategory.tensorLeftIsoTensorRight V

/-- The restricted extension complex is the ordinary quotient tensor complex.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-weil-pbc-adic-ordinary-tensor-levels). -/
def adicOrdinaryQuotientComplexIso
    {A : Type t} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (n : ℕ) :
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
      (.up ℤ)).obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
          (.up ℤ)).obj P) ≅ (adicOrdinaryTensorComplexDiagram I P).obj (op n) := by
  exact (Functor.mapHomologicalComplexCompIso
    (adicOrdinaryRestrictedTensorIso (Ideal.Quotient.mk (I ^ (n + 1)))) (.up ℤ)).app P

/-- The restricted transpose of scalar insertion, defined on every complex.
Source: Stacks Project, Tag 06Y6, K-flat computation of derived scalar extension.
(blueprint: lem-weil-pbc-adic-ordinary-tensor-levels).
Compose the restricted transpose with exact scalar restriction and tensor symmetry. -/
def adicOrdinaryTensorLevelMap
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (n : ℕ) :
    (DerivedCategory.adicLevelRestriction I n).obj ((L n).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((adicOrdinaryTensorComplexDiagram I P).obj (op n)) := by
  let q := Ideal.Quotient.mk (I ^ (n + 1))
  let V := ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  let r : (L n).obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj V :=
    ((adj n).homEquiv _ _).symm
      (DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.inv.app V)
  exact (DerivedCategory.adicLevelRestriction I n).map r ≫
    (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.hom.app V ≫
    DerivedCategory.Q.map (adicOrdinaryQuotientComplexIso I P n).hom

/-- K-flatness makes the explicitly defined level map invertible.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-weil-pbc-adic-ordinary-tensor-levels).
Proof: its transpose is invertible by the derived-adjunction criterion; restriction,
the exact factorization and tensor symmetry preserve invertibility. -/
theorem adicOrdinaryTensorLevelMap_isIso
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (hP : P.IsKFlatForTotalTensor) (n : ℕ) :
    IsIso (adicOrdinaryTensorLevelMap I L adj P n) := by
  let q := Ideal.Quotient.mk (I ^ (n + 1))
  let V := ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  let r := ((adj n).homEquiv _ (DerivedCategory.Q.obj V)).symm
    (DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.inv.app V)
  have : IsIso r := adicOrdinaryTranspose_isIso q (L n) (adj n) P hP
  change IsIso ((DerivedCategory.adicLevelRestriction I n).map r ≫
    (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.hom.app V ≫
      DerivedCategory.Q.map (adicOrdinaryQuotientComplexIso I P n).hom)
  infer_instance

end AlgebraicGeometry.Scheme
