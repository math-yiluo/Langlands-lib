/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteComplexRealization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.KoszulDifferential
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
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
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompleted
/-! # Intrinsic completion over the completed coefficient sheaf

The ring and tensor product are those of Mod(A_T), with site object universe t+1
and morphism universe t. The mapping cocone of minus (1-shift) has differential
(dx, (1-shift)x-dy) after listing its degree-i terms as (x,y).

## Main definitions

* `completedKoszulPowerSheaf`: the completed-coefficient Koszul complex.
* `completedKoszulFiber`: the explicit completion complex.
* `completedIntrinsicCompletionMap`: its specified unit.
* `IsCompletedIntrinsicallyDerivedComplete`: invertibility of that unit.

## References

* Stacks Tags 099M and 091Z
* Tags 07KC and 05RU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

section TensorUnits
set_option backward.isDefEq.respectTransparency false
variable {M : Type*} [Category* M] [Preadditive M] [MonoidalCategory M]
  [MonoidalPreadditive M]
  (C D K L : CochainComplex M ℤ)
  [HomologicalComplex.HasMapBifunctor C K (curriedTensor M) (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor C L (curriedTensor M) (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor D K (curriedTensor M) (.up ℤ)]

private theorem tensorUnit_transition (u : 𝟙_ M ⟶ K.X 0) (v : 𝟙_ M ⟶ L.X 0)
    (τ : K ⟶ L) (h : u ≫ τ.f 0 = v) (p : ℤ) :
    ((ρ_ (C.X p)).inv ≫ C.X p ◁ u ≫
      HomologicalComplex.ιMapBifunctor C K (curriedTensor M) (.up ℤ) p 0 p (add_zero p)) ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 C) τ (curriedTensor M) (.up ℤ)).f p =
      (ρ_ (C.X p)).inv ≫ C.X p ◁ v ≫
        HomologicalComplex.ιMapBifunctor C L (curriedTensor M) (.up ℤ) p 0 p (add_zero p) := by
  rw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map]
  change (ρ_ (C.X p)).inv ≫ C.X p ◁ u ≫
    𝟙 (C.X p ⊗ K.X 0) ≫ C.X p ◁ τ.f 0 ≫ _ = _
  rw [Category.id_comp, ← whiskerLeft_comp_assoc, h]

private theorem tensorUnit_natural (u : 𝟙_ M ⟶ K.X 0) (α : C ⟶ D) (p : ℤ) :
    α.f p ≫ (ρ_ (D.X p)).inv ≫ D.X p ◁ u ≫
        HomologicalComplex.ιMapBifunctor D K (curriedTensor M) (.up ℤ) p 0 p (add_zero p) =
      ((ρ_ (C.X p)).inv ≫ C.X p ◁ u ≫
        HomologicalComplex.ιMapBifunctor C K (curriedTensor M) (.up ℤ) p 0 p (add_zero p)) ≫
          (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor M) (.up ℤ)).f p := by
  rw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    whiskerLeft_id]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  simp

private theorem tensorUnit_closed (u : 𝟙_ M ⟶ K.X 0)
    (hu : u ≫ K.d 0 1 = 0) (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    ((ρ_ (C.X p)).inv ≫ C.X p ◁ u ≫
      HomologicalComplex.ιMapBifunctor C K (curriedTensor M) (.up ℤ) p 0 p (add_zero p)) ≫
        (CochainComplex.mapBifunctor C K (curriedTensor M)).d p q =
      C.d p q ≫ (ρ_ (C.X q)).inv ≫ C.X q ◁ u ≫
        HomologicalComplex.ιMapBifunctor C K (curriedTensor M) (.up ℤ) q 0 q (add_zero q) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hpq 0 q (add_zero q),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (show
      (ComplexShape.up ℤ).Rel 0 1 from rfl) q (by
        change p + 1 = q
        exact hpq)]
  have hε : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, 0) = 1 := rfl
  rw [hε, one_smul]
  simp only [curriedTensor_obj_map, curriedTensor_map_app]
  have hz : C.X p ◁ u ≫ C.X p ◁ K.d 0 1 = 0 := by
    rw [← whiskerLeft_comp, hu, MonoidalPreadditive.whiskerLeft_zero]
  simp only [Linear.comp_units_smul]
  rw [← Category.assoc (C.X p ◁ u) (C.X p ◁ K.d 0 1), hz,
    zero_comp, comp_zero, smul_zero, add_zero]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

private theorem tensorMap_id :
    HomologicalComplex.mapBifunctorMap (𝟙 C) (𝟙 K) (curriedTensor M) (.up ℤ) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp

private theorem tensorMap_comp (E : CochainComplex M ℤ)
    [HomologicalComplex.HasMapBifunctor E K (curriedTensor M) (.up ℤ)]
    (α : C ⟶ D) (β : D ⟶ E) :
    HomologicalComplex.mapBifunctorMap (α ≫ β) (𝟙 K) (curriedTensor M) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor M) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap β (𝟙 K) (curriedTensor M) (.up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [Category.assoc]

private theorem tensorMap_exchange
    [HomologicalComplex.HasMapBifunctor D L (curriedTensor M) (.up ℤ)]
    (α : C ⟶ D) (τ : K ⟶ L) :
    HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor M) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 D) τ (curriedTensor M) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 C) τ (curriedTensor M) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap α (𝟙 L) (curriedTensor M) (.up ℤ) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [whisker_exchange_assoc, whiskerLeft_id]

end TensorUnits

attribute [instance] completedKoszulConstant_additive

/-- The cohomologically reindexed Koszul complex of the positive power m+1.
The module carrier has the same universe as the original coefficient ring. -/
def completedKoszulPower (r : ℕ) (f : Fin r → A) (m : ℕ) :
    CochainComplex (ModuleCat.{t + 1} (A)) ℤ :=
  (ExteriorAlgebra.koszulComplex (A) r
    (fun j ↦ f j ^ (m + 1))).extend ComplexShape.embeddingDownNat

/-- The constant Koszul sheaf complex. -/
def completedKoszulPowerSheaf (r : ℕ) (f : Fin r → A) (m : ℕ) :=
  ((completedKoszulConstant X d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (completedKoszulPower (A := A) r f m)

/-- Exterior map on the free generators, e_j ↦ f_j e_j. -/
def completedKoszulGenerator (r : ℕ) (f : Fin r → A) :
    (Fin r →₀ A) →ₗ[A] (Fin r →₀ A) :=
  Finsupp.linearCombination (A) (fun j ↦ Finsupp.single j (f j))

private theorem completedKoszulExteriorMap_coe (R : Type*) [CommRing R] (r n : ℕ)
    (g : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R)) (x : ⋀[R]^n (Fin r →₀ R)) :
    (exteriorPower.map n g x : ExteriorAlgebra R (Fin r →₀ R)) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra R (Fin r →₀ R)) := by
  have h : (⋀[R]^n (Fin r →₀ R)).subtype.comp (exteriorPower.map n g) =
      (ExteriorAlgebra.map g).toLinearMap.comp (⋀[R]^n (Fin r →₀ R)).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply,
      ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun h x

private theorem completedKoszulContract_natural (R : Type*) [CommRing R] (r : ℕ)
    (g : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R))
    (φ ψ : (Fin r →₀ R) →ₗ[R] R) (h : ψ.comp g = φ)
    (x : ExteriorAlgebra R (Fin r →₀ R)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R))) ψ
        (ExteriorAlgebra.map g x) =
      ExteriorAlgebra.map g
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R))) φ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    have hv : ψ (g v) = φ v := LinearMap.congr_fun h v
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      hv, hx, map_sub, map_smul]

/-- The power transition commutes with Koszul contraction. -/
theorem completedKoszulTransition_comm (r : ℕ) (f : Fin r → A) (m i j : ℕ) :
    ModuleCat.ofHom (exteriorPower.map i (completedKoszulGenerator (A := A) r f)) ≫
      (ExteriorAlgebra.koszulComplex (A) r
        (fun k ↦ f k ^ (m + 1))).d i j =
    (ExteriorAlgebra.koszulComplex (A) r
      (fun k ↦ f k ^ (m + 2))).d i j ≫
        ModuleCat.ofHom (exteriorPower.map j (completedKoszulGenerator (A := A) r f)) := by
  by_cases hij : i = j + 1
  · subst i
    dsimp only [ExteriorAlgebra.koszulComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (ExteriorAlgebra.koszulBoundary A r
        (fun k ↦ f k ^ (m + 1)) j
        (exteriorPower.map (j + 1) (completedKoszulGenerator (A := A) r f) x) :
          ExteriorAlgebra A (Fin r →₀ A)) =
      (exteriorPower.map j (completedKoszulGenerator (A := A) r f)
        (ExteriorAlgebra.koszulBoundary A r
          (fun k ↦ f k ^ (m + 2)) j x) : ExteriorAlgebra A (Fin r →₀ A))
    simp only [completedKoszulExteriorMap_coe, ExteriorAlgebra.koszulBoundary,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    apply completedKoszulContract_natural
    apply Finsupp.lhom_ext
    intro k c
    simp only [LinearMap.comp_apply, completedKoszulGenerator,
      Finsupp.linearCombination_single, map_smul, smul_eq_mul]
    congr 1
    simpa [Nat.add_assoc, mul_comm] using (pow_succ (f k) (m + 1)).symm
  · have hn : ¬ (ComplexShape.down ℕ).Rel i j := by
      simpa only [ComplexShape.down_Rel, eq_comm] using hij
    rw [HomologicalComplex.shape _ i j hn, HomologicalComplex.shape _ i j hn,
      zero_comp, comp_zero]

/-- The specified exterior-algebra transition, followed by cohomological reindexing. -/
def completedKoszulTransition (r : ℕ) (f : Fin r → A) (m : ℕ) :
    completedKoszulPower (A := A) r f (m + 1) ⟶ completedKoszulPower (A := A) r f m :=
  HomologicalComplex.extendMap
    { f := fun i ↦ ModuleCat.ofHom (exteriorPower.map i (completedKoszulGenerator (A := A) r f))
      comm' := fun i j _ ↦ completedKoszulTransition_comm (A := A) r f m i j }
    ComplexShape.embeddingDownNat

/-- Degree zero of the Koszul complex contains the identity coefficient unit. -/
def completedKoszulSheafUnitZero (r : ℕ) (f : Fin r → A) (m : ℕ) :
    SheafOfModules.unit ((adicLisseForget X).obj (adicDatumRing X d)) ⟶
      (completedKoszulPowerSheaf X d r f m).X 0 :=
  completedKoszulOne X d ≫ (completedKoszulConstant X d).map
    (ModuleCat.ofHom (exteriorPower.zeroEquiv (A)
      (Fin r →₀ A)).symm.toLinearMap) ≫
    (completedKoszulConstant X d).map
      ((ExteriorAlgebra.koszulComplex (A) r
        (fun k ↦ f k ^ (m + 1))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv

/-- The degree-zero unit is closed. -/
theorem completedKoszulSheafUnitZero_closed (r : ℕ) (f : Fin r → A) (m : ℕ)
    (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 0 j) :
    completedKoszulSheafUnitZero X d r f m ≫ (completedKoszulPowerSheaf X d r f m).d 0 j = 0 := by
  have _hj := hj
  have hd : (completedKoszulPower (A := A) r f m).d 0 j = 0 := by
    apply HomologicalComplex.extend_d_from_eq_zero _ ComplexShape.embeddingDownNat
      0 j 0 rfl
    simp [ComplexShape.down_Rel]
  change _ ≫ (completedKoszulConstant X d).map
    ((completedKoszulPower (A := A) r f m).d 0 j) = 0
  rw [hd, Functor.map_zero, comp_zero]

/-- Total tensor complex of the fixed representative and the constant Koszul complex. -/
def completedKoszulTensor (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  CochainComplex.mapBifunctor C (completedKoszulPowerSheaf X d r f m) (curriedTensor _)

/-- The transition 1_C tensor t_m. -/
def completedKoszulTensorTransition (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :
    completedKoszulTensor X d r f C (m + 1) ⟶ completedKoszulTensor X d r f C m :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  HomologicalComplex.mapBifunctorMap (𝟙 C)
    (((completedKoszulConstant X d).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (completedKoszulTransition (A := A) r f m)) (curriedTensor _) (ComplexShape.up ℤ)

/-- The component c ↦ c tensor 1, included in the total tensor summand (p,0). -/
def completedKoszulTensorUnitComponent (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) (p : ℤ) :
    C.X p ⟶ (completedKoszulTensor X d r f C m).X p :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  (ρ_ (C.X p)).inv ≫ (C.X p ◁ completedKoszulSheafUnitZero X d r f m) ≫
    HomologicalComplex.ιMapBifunctor C (completedKoszulPowerSheaf X d r f m) (curriedTensor _)
      (ComplexShape.up ℤ) p 0 p (add_zero p)

/-- Tensoring with the closed degree-zero unit commutes with the total differential. -/
theorem completedKoszulTensorUnitComponent_comm (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    completedKoszulTensorUnitComponent X d r f C m p ≫ (completedKoszulTensor X d r f C m).d p q =
      C.d p q ≫ completedKoszulTensorUnitComponent X d r f C m q := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  exact tensorUnit_closed C (completedKoszulPowerSheaf X d r f m)
    (completedKoszulSheafUnitZero X d r f m)
    (completedKoszulSheafUnitZero_closed X d r f m 1 rfl) p q hpq

/-- The tensor unit gives c ↦ c tensor 1 in each level. -/
def completedKoszulTensorUnit (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :
    C ⟶ completedKoszulTensor X d r f C m where
  f := completedKoszulTensorUnitComponent X d r f C m
  comm' := completedKoszulTensorUnitComponent_comm X d r f C m

/-- The termwise product of the positive-power tensor tower (index n means m=n+1). -/
def completedKoszulProduct (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :=
  ∏ᶜ (completedKoszulTensor X d r f C)

/-- One minus the transition shift, specified by its actual product components. -/
def completedKoszulOneSubShift (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    completedKoszulProduct X d r f C ⟶ completedKoszulProduct X d r f C :=
  𝟙 _ - Pi.lift (fun n ↦ Pi.π (completedKoszulTensor X d r f C) (n + 1) ≫
    completedKoszulTensorTransition X d r f C n)

/-- Explicit mapping fiber with differential (dx,(1-s)x-dy). -/
def completedKoszulFiber (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :=
  CochainComplex.mappingCocone (- completedKoszulOneSubShift X d r f C)

/-- The compatible units C to C tensor Q_m give the actual product augmentation. -/
def completedKoszulProductUnit (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :=
  Pi.lift (completedKoszulTensorUnit X d r f C)

set_option backward.isDefEq.respectTransparency false in
private theorem completedKoszulSheafUnitZero_transition (r : ℕ) (f : Fin r → A)
    (m : ℕ) :
    completedKoszulSheafUnitZero X d r f (m + 1) ≫
      (((completedKoszulConstant X d).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (completedKoszulTransition (A := A) r f m)).f 0 =
      completedKoszulSheafUnitZero X d r f m := by
  change completedKoszulSheafUnitZero X d r f (m + 1) ≫
    (completedKoszulConstant X d).map
      ((completedKoszulTransition (A := A) r f m).f 0) = _
  unfold completedKoszulSheafUnitZero completedKoszulTransition
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
    (i := 0) (i' := 0) rfl]
  simp only [Functor.map_comp, Category.assoc, ← Functor.mapIso_inv,
    ← Functor.mapIso_hom, Iso.inv_hom_id_assoc]
  have h :
      (exteriorPower.map 0 (completedKoszulGenerator (A := A) r f)).comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap =
      (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).injective
    have hn := LinearMap.congr_fun
      (exteriorPower.zeroEquiv_naturality
        (completedKoszulGenerator (A := A) r f))
      ((exteriorPower.zeroEquiv A (Fin r →₀ A)).symm x)
    simpa using hn
  have hh : ModuleCat.ofHom
      (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap ≫
      ModuleCat.ofHom (exteriorPower.map 0 (completedKoszulGenerator (A := A) r f)) =
      ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap := by
    exact ModuleCat.hom_ext h
  rw [← Functor.map_comp_assoc, hh]

set_option backward.isDefEq.respectTransparency false in
private theorem completedKoszulTensorUnit_transition (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :
    completedKoszulTensorUnit X d r f C (m + 1) ≫
      completedKoszulTensorTransition X d r f C m =
      completedKoszulTensorUnit X d r f C m := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  apply HomologicalComplex.hom_ext
  intro p
  exact tensorUnit_transition C (completedKoszulPowerSheaf X d r f (m + 1))
    (completedKoszulPowerSheaf X d r f m)
    (completedKoszulSheafUnitZero X d r f (m + 1))
    (completedKoszulSheafUnitZero X d r f m) _
    (completedKoszulSheafUnitZero_transition X d r f m) p

/-- The unit has zero homotopy component in the mapping fiber. -/
theorem completedKoszulLift_relation (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain C (completedKoszulProduct X d r f C) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (completedKoszulProductUnit X d r f C ≫
          (- completedKoszulOneSubShift X d r f C)) = 0 := by
  have hu : completedKoszulProductUnit X d r f C ≫
      completedKoszulOneSubShift X d r f C = 0 := by
    unfold completedKoszulOneSubShift
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero]
    apply Pi.hom_ext
    intro n
    simp only [completedKoszulProductUnit, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    exact (completedKoszulTensorUnit_transition X d r f C n).symm
  simp only [CochainComplex.HomComplex.δ_zero, zero_add, Preadditive.comp_neg,
    hu, neg_zero, CochainComplex.HomComplex.Cochain.ofHom_zero]

/-- The completion chain map c maps to (u(c),0) in the specified fiber coordinates. -/
def completedKoszulUnitComplex (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    C ⟶ completedKoszulFiber X d r f C :=
  CochainComplex.mappingCocone.lift _ (completedKoszulProductUnit X d r f C) 0
    (completedKoszulLift_relation X d r f C)

/-- The intrinsic completion of any representative, localized in D(Mod(A_T)). -/
def completedIntrinsicCompletion (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) : adicDatumDerived X d :=
  (completedConstantQ _).obj (completedKoszulFiber X d r f C)

/-- The intrinsic completion map, transported through a specified realization of C. -/
def completedIntrinsicCompletionMap (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) {K : adicDatumDerived X d}
    (e : (completedConstantQ _).obj C ≅ K) :
    K ⟶ completedIntrinsicCompletion X d r f C :=
  e.inv ≫ (completedConstantQ _).map (completedKoszulUnitComplex X d r f C)

/-- Derived I-completeness is invertibility of the specified Koszul completion map.
The finite generator tuple is explicitly required to generate I; it may be empty. -/
def IsCompletedIntrinsicallyDerivedComplete (r : ℕ) (f : Fin r → A)
    (_hf : Ideal.span (Set.range f) = d.ideal)
    (C : CochainComplex (adicDatumModules X d) ℤ) {K : adicDatumDerived X d}
    (e : (completedConstantQ _).obj C ≅ K) : Prop :=
  IsIso (completedIntrinsicCompletionMap X d r f C e)

section Descent
set_option backward.isDefEq.respectTransparency false

private theorem completedKoszulPower_flat (r : ℕ) (f : Fin r → A) (m : ℕ) (i : ℤ) :
    Module.Flat A ((completedKoszulPower (A := A) r f m).X i) := by
  classical
  have (n : ℕ) : CategoryTheory.Projective
      ((ExteriorAlgebra.koszulComplex A r (fun j ↦ f j ^ (m + 1))).X n) := by
    change CategoryTheory.Projective (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)))
    infer_instance
  have : CategoryTheory.Projective ((completedKoszulPower (A := A) r f m).X i) :=
    inferInstanceAs (CategoryTheory.Projective
      (((ExteriorAlgebra.koszulComplex A r (fun j ↦ f j ^ (m + 1))).extend
        ComplexShape.embeddingDownNat).X i))
  have : Module.Projective A ((completedKoszulPower (A := A) r f m).X i) :=
    ModuleCat.projective_of_module_projective _
  infer_instance

private theorem completedKoszulPower_bounded (r : ℕ) (f : Fin r → A) (m : ℕ) :
    (completedKoszulPower (A := A) r f m).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ 0).2
  intro i hi
  apply HomologicalComplex.isZero_extend_X
  intro n
  change -(n : ℤ) ≠ i
  omega

private theorem completedKoszulPowerSheaf_kflat (r : ℕ) (f : Fin r → A) (m : ℕ) :
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X) (R := adicDatumRing X d)
      (completedKoszulPowerSheaf X d r f m) := by
  let := CompletedConstantReduction.constant_additive X A
  let P := completedKoszulPower (A := A) r f m
  have : P.IsStrictlyLE 0 := completedKoszulPower_bounded (A := A) r f m
  have hf (i : ℤ) : Module.Flat A (P.X i) := completedKoszulPower_flat (A := A) r f m i
  have hb : (HomologicalComplex.quasiIso (ModuleCat.{t + 1} A) (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P 0
      (fun i ↦ (ModuleCat.flat_iff_flat (P.X i)).2 (hf i))
  let := HasDerivedCategory.standard (ModuleCat.{t + 1} A)
  let := HasDerivedCategory.standard
    (CategoryTheory.realizationModules (ProEt.topology X) A)
  have hc := (CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension
    (ProEt.topology X) (RingHom.id A)).2.1 P ⟨fun s hs ↦ hb.1 s hs, fun s hs ↦ hb.2 s hs⟩ hf
  have he : ((commutativeSiteConstantModuleFunctor (ProEt.topology X) A).mapHomologicalComplex
      (.up ℤ)).obj P =
      ((adicLisseConstantModules X A).mapHomologicalComplex (.up ℤ)).obj P := by
    rfl
  have hk : CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X)
      (R := adicLisseConstantRing X A)
      (((adicLisseConstantModules X A).mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [← he]
    exact hc.1
  have h := adicDatumExtension_kflat X (adicDatumScalar X d) _ hk
  have heq :
      (((completedConstantExtension X (adicDatumScalar X d)).mapHomologicalComplex
        (.up ℤ)).obj (((adicLisseConstantModules X A).mapHomologicalComplex (.up ℤ)).obj P)) =
      completedKoszulPowerSheaf X d r f m := by
    rfl
  simpa only [← adicDatumOrdinaryExtension_eq, heq] using h

private def completedTensorMap (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) (m : ℕ) :
    completedKoszulTensor X d r f C m ⟶ completedKoszulTensor X d r f D m :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  HomologicalComplex.mapBifunctorMap α (𝟙 (completedKoszulPowerSheaf X d r f m))
    (curriedTensor _) (.up ℤ)

private theorem completedTensorMap_id (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :
    completedTensorMap X d r f (𝟙 C) m = 𝟙 _ := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  exact tensorMap_id C (completedKoszulPowerSheaf X d r f m)

private theorem completedTensorMap_comp (r : ℕ) (f : Fin r → A)
    {C D E : CochainComplex (adicDatumModules X d) ℤ}
    (α : C ⟶ D) (β : D ⟶ E) (m : ℕ) :
    completedTensorMap X d r f (α ≫ β) m =
      completedTensorMap X d r f α m ≫ completedTensorMap X d r f β m := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  exact tensorMap_comp C D (completedKoszulPowerSheaf X d r f m) E α β

private def completedProductMap (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) :
    completedKoszulProduct X d r f C ⟶ completedKoszulProduct X d r f D :=
  Pi.lift (fun m ↦ Pi.π (completedKoszulTensor X d r f C) m ≫
    completedTensorMap X d r f α m)

private theorem completedProductMap_id (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    completedProductMap X d r f (𝟙 C) = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  simp [completedProductMap, completedTensorMap_id]

private theorem completedProductMap_comp (r : ℕ) (f : Fin r → A)
    {C D E : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) (β : D ⟶ E) :
    completedProductMap X d r f (α ≫ β) =
      completedProductMap X d r f α ≫ completedProductMap X d r f β := by
  apply Pi.hom_ext
  intro n
  simp [completedProductMap, completedTensorMap_comp, Category.assoc]

private theorem completedTensor_transition_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) (m : ℕ) :
    completedTensorMap X d r f α (m + 1) ≫ completedKoszulTensorTransition X d r f D m =
      completedKoszulTensorTransition X d r f C m ≫ completedTensorMap X d r f α m := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  exact tensorMap_exchange C D (completedKoszulPowerSheaf X d r f (m + 1))
    (completedKoszulPowerSheaf X d r f m) α _

private theorem completedProduct_shift_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) :
    completedKoszulOneSubShift X d r f C ≫ completedProductMap X d r f α =
      completedProductMap X d r f α ≫ completedKoszulOneSubShift X d r f D := by
  dsimp only [completedKoszulProduct]
  apply Pi.hom_ext
  intro n
  simp only [completedKoszulOneSubShift, completedProductMap, Preadditive.sub_comp,
    Preadditive.comp_sub, Category.assoc, Pi.lift_comp_π_assoc, Pi.lift_comp_π,
    Category.id_comp, Category.comp_id]
  rw [completedTensor_transition_natural]

private def completedArrowFunctor (r : ℕ) (f : Fin r → A) :
    CochainComplex (adicDatumModules X d) ℤ ⥤
      Arrow (CochainComplex (adicDatumModules X d) ℤ) where
  obj C := Arrow.mk (-completedKoszulOneSubShift X d r f C)
  map α := Arrow.homMk (completedProductMap X d r f α) (completedProductMap X d r f α)
    (by simpa only [Arrow.mk_hom, Preadditive.neg_comp, Preadditive.comp_neg] using
      congrArg Neg.neg (completedProduct_shift_natural X d r f α).symm)
  map_id C := by
    apply Arrow.hom_ext <;> exact completedProductMap_id X d r f C
  map_comp α β := by
    apply Arrow.hom_ext <;> exact completedProductMap_comp X d r f α β

private def completedConeFunctor (M : Type*) [Category* M] [Abelian M] :
    Arrow (CochainComplex M ℤ) ⥤ CochainComplex M ℤ where
  obj a := CochainComplex.mappingCone a.hom
  map α := CochainComplex.mappingCone.map _ _ α.left α.right α.w.symm
  map_id a := CochainComplex.mappingCone.map_id a.hom
  map_comp α β := CochainComplex.mappingCone.map_comp _ _ _ _ _ α.w.symm _ _ β.w.symm

private def completedFiberFunctor (r : ℕ) (f : Fin r → A) :
    CochainComplex (adicDatumModules X d) ℤ ⥤ CochainComplex (adicDatumModules X d) ℤ :=
  completedArrowFunctor X d r f ⋙ completedConeFunctor (adicDatumModules X d) ⋙
    shiftFunctor _ (-1 : ℤ)

private theorem completedTensorUnit_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) (m : ℕ) :
    α ≫ completedKoszulTensorUnit X d r f D m =
      completedKoszulTensorUnit X d r f C m ≫ completedTensorMap X d r f α m := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  apply HomologicalComplex.hom_ext
  intro p
  exact tensorUnit_natural C D (completedKoszulPowerSheaf X d r f m)
    (completedKoszulSheafUnitZero X d r f m) α p

private theorem completedProductUnit_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) :
    α ≫ completedKoszulProductUnit X d r f D =
      completedKoszulProductUnit X d r f C ≫ completedProductMap X d r f α := by
  apply Pi.hom_ext
  intro m
  simp only [completedKoszulProductUnit, completedProductMap, Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc]
  exact completedTensorUnit_natural X d r f α m

private theorem completedTensorMap_quasiIso (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D)
    [QuasiIso α] (m : ℕ) : QuasiIso (completedTensorMap X d r f α m) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let := SheafOfModules.tensorPreadditive (adicDatumRing X d)
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 inferInstance
  have ht := completedKoszulPowerSheaf_kflat X d r f m
    (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso α
    (completedKoszulPowerSheaf X d r f m) (curriedTensor _))

private theorem productMap_quasiIso (M : Type*) [Category* M] [Abelian M]
    [HasCountableProducts M]
    (hprod : ∀ (F G : ℕ → M) (a : ∀ n, F n ⟶ G n),
      (∀ n, Epi (a n)) → Epi (Limits.Pi.map a))
    {C D : ℕ → CochainComplex M ℤ} (α : ∀ n, C n ⟶ D n)
    [∀ n, QuasiIso (α n)] :
    QuasiIso (Pi.lift (fun n ↦ Pi.π C n ≫ α n)) := by
  have : (lim (J := Discrete ℕ) (C := M)).PreservesEpimorphisms :=
    { preserves := by
        intro F G a ha
        have := hprod (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ a.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map a = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ a.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi M (Discrete ℕ)
  let a : Discrete.functor C ⟶ Discrete.functor D :=
    Discrete.natTrans (fun n ↦ α n.as)
  have (n : Discrete ℕ) : QuasiIso (a.app n) := inferInstanceAs (QuasiIso (α n.as))
  exact HomologicalComplex.quasiIso_limMap a

private theorem completedProductMap_quasiIso (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D)
    [QuasiIso α] : QuasiIso (completedProductMap X d r f α) := by
  have (n : ℕ) : QuasiIso (completedTensorMap X d r f α n) :=
    completedTensorMap_quasiIso X d r f α n
  exact productMap_quasiIso (adicDatumModules X d)
    ((ProEt.countableProducts_exact.{t, t, 0} X (adicDatumRing X d)).2.2 ℕ)
    (fun n ↦ completedTensorMap X d r f α n)

private theorem completedConeMap_quasiIso (M : Type*) [Category* M] [Abelian M]
    [HasDerivedCategory M] {a b : Arrow (CochainComplex M ℤ)} (α : a ⟶ b)
    [QuasiIso α.left] [QuasiIso α.right] :
    QuasiIso ((completedConeFunctor M).map α) := by
  let τ := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap a.hom b.hom α.left α.right α.w.symm)
  have h₁ : IsIso τ.hom₁ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso M α.left).2 inferInstance
  have h₂ : IsIso τ.hom₂ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso M α.right).2 inferInstance
  have := Pretriangulated.isIso₃_of_isIso₁₂ τ
    (DerivedCategory.mappingCone_triangle_distinguished a.hom)
    (DerivedCategory.mappingCone_triangle_distinguished b.hom) h₁ h₂
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso M _).1 this

private theorem completedFiberMap_quasiIso (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D)
    [QuasiIso α] : QuasiIso ((completedFiberFunctor X d r f).map α) := by
  have := completedProductMap_quasiIso X d r f α
  have : QuasiIso (((completedArrowFunctor X d r f).map α).left) :=
    completedProductMap_quasiIso X d r f α
  have : QuasiIso (((completedArrowFunctor X d r f).map α).right) :=
    completedProductMap_quasiIso X d r f α
  have := completedConeMap_quasiIso (adicDatumModules X d)
    ((completedArrowFunctor X d r f).map α)
  exact (CochainComplex.quasiIso_shift_iff
    ((completedConeFunctor _).map ((completedArrowFunctor X d r f).map α)) (-1)).2 this

private theorem completedCoconeLift_f (M : Type*) [Category* M] [Abelian M]
    {C K L : CochainComplex M ℤ} (φ : K ⟶ L) (u : C ⟶ K)
    (hu : u ≫ φ = 0) (p : ℤ) :
    (CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])).f p =
      u.f p ≫ (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) := by
  let l := CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])
  have h := CochainComplex.mappingCocone.id_X φ p (p + -1) rfl
  calc
    l.f p = l.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ := by
      rw [← h, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        CochainComplex.mappingCocone.lift_f_fst_f,
        CochainComplex.mappingCocone.lift_f_snd_v]
      simp

private theorem completedCoconeLift_natural (M : Type*) [Category* M] [Abelian M]
    {C D K₁ K₂ L₁ L₂ : CochainComplex M ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (α : C ⟶ D) (u : C ⟶ K₁) (v : D ⟶ K₂)
    (hu : u ≫ φ₁ = 0) (hv : v ≫ φ₂ = 0) (hn : α ≫ v = u ≫ a) :
    α ≫ CochainComplex.mappingCocone.lift φ₂ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu]) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro p
  have hi : (CochainComplex.mappingCocone.inl φ₁).v p p (add_zero p) ≫
      ((CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧').f p =
      a.f p ≫ (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) := by
    simp [CochainComplex.mappingCocone.inl,
      CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
      CochainComplex.mappingCone.map]
  simp only [HomologicalComplex.comp_f]
  rw [completedCoconeLift_f M φ₂ v hv p, completedCoconeLift_f M φ₁ u hu p,
    Category.assoc, hi, ← Category.assoc]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun z ↦ z.f p ≫
      (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p)) hn

private theorem completedFiberUnit_natural (r : ℕ) (f : Fin r → A)
    {C D : CochainComplex (adicDatumModules X d) ℤ} (α : C ⟶ D) :
    α ≫ completedKoszulUnitComplex X d r f D =
      completedKoszulUnitComplex X d r f C ≫ (completedFiberFunctor X d r f).map α := by
  have hz (E : CochainComplex (adicDatumModules X d) ℤ) :
      completedKoszulProductUnit X d r f E ≫ (-completedKoszulOneSubShift X d r f E) = 0 := by
    have h := completedKoszulLift_relation X d r f E
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa using h
  exact completedCoconeLift_natural (adicDatumModules X d) _ _ _ _
    ((completedArrowFunctor X d r f).map α).w.symm α _ _ (hz C) (hz D)
    (completedProductUnit_natural X d r f α)

private theorem completedLocalization (M : Type*) [Category* M] [Abelian M]
    [HasDerivedCategory M] (G : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (τ : 𝟭 _ ⟶ G)
    (hG : ∀ {C D : CochainComplex M ℤ} (α : C ⟶ D),
      QuasiIso α → QuasiIso (G.map α)) :
    ∃ (F : DerivedCategory M ⥤ DerivedCategory M) (η : 𝟭 _ ⟶ F),
      ∀ C : CochainComplex M ℤ,
        ∃ e : F.obj (DerivedCategory.Q.obj C) ≅ DerivedCategory.Q.obj (G.obj C),
          η.app (DerivedCategory.Q.obj C) ≫ e.hom = DerivedCategory.Q.map (τ.app C) := by
  let Q := DerivedCategory.Q (C := M)
  let W := HomologicalComplex.quasiIso M (.up ℤ)
  have h : W.IsInvertedBy (G ⋙ Q) := by
    intro C D α hα
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso M (G.map α)).2 (hG α hα)
  let F := Localization.lift (G ⋙ Q) h Q
  let σ : Q ⟶ G ⋙ Q :=
    { app := fun C ↦ Q.map (τ.app C)
      naturality := by
        intro C D α
        simp only [Functor.comp_map, ← Q.map_comp]
        exact congrArg Q.map (τ.naturality α) }
  let : Localization.Lifting Q W Q (𝟭 _) := ⟨Functor.rightUnitor Q⟩
  let η := Localization.liftNatTrans Q W Q (G ⋙ Q) (𝟭 _) F σ
  refine ⟨F, η, fun C ↦ ⟨(Localization.fac (G ⋙ Q) h Q).app C, ?_⟩⟩
  dsimp only [η]
  rw [Localization.liftNatTrans_app]
  change ((𝟙 _) ≫ σ.app C ≫ (Localization.fac (G ⋙ Q) h Q).inv.app C) ≫
    (Localization.fac (G ⋙ Q) h Q).hom.app C = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, Category.id_comp]

/-- The explicit Koszul fiber and its unit descend through quasi-isomorphisms.
No arbitrary representative is chosen to define the data of the fiber complex. -/
theorem completedIntrinsicCompletion_descends (r : ℕ) (f : Fin r → A) :
    ∃ (F : adicDatumDerived X d ⥤ adicDatumDerived X d) (η : 𝟭 _ ⟶ F),
      ∀ C : CochainComplex (adicDatumModules X d) ℤ,
        ∃ e : F.obj ((completedConstantQ _).obj C) ≅
            completedIntrinsicCompletion X d r f C,
          η.app ((completedConstantQ _).obj C) ≫ e.hom =
            (completedConstantQ _).map (completedKoszulUnitComplex X d r f C) := by
  let τ : 𝟭 _ ⟶ completedFiberFunctor X d r f :=
    { app := completedKoszulUnitComplex X d r f
      naturality := by
        intro C D α
        exact completedFiberUnit_natural X d r f α }
  exact completedLocalization (adicDatumModules X d) (completedFiberFunctor X d r f) τ
    (by
      intro C D α hα
      let := hα
      exact completedFiberMap_quasiIso X d r f α)

end Descent

end AlgebraicGeometry.Scheme
