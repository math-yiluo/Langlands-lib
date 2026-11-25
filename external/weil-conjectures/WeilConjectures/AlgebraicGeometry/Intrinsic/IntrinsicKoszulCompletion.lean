/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Intrinsic Koszul completion
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]

/-- Constant commutative ring sheafification unit, forgetting commutativity. -/
def koszulConstantUnit :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} Λ)) ⟶
      (adicModuleRing X Λ).obj :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
    (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency false in
/-- Local bijectivity of the constant ring sheafification unit. -/
theorem koszulConstantUnit_local :
    Presheaf.IsLocallyInjective (ProEt.topology X) (koszulConstantUnit X Λ) ∧
    Presheaf.IsLocallySurjective (ProEt.topology X) (koszulConstantUnit X Λ) := by
  constructor
  · rw [← Presheaf.isLocallyInjective_forget_iff]
    change Presheaf.IsLocallyInjective (ProEt.topology X)
      (Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
        (CategoryTheory.forget CommRingCat))
    infer_instance
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
        (CategoryTheory.forget CommRingCat))
    infer_instance

/-- Constant module sheaves, obtained by actual module sheafification. -/
def koszulConstantFunctor :
    ModuleCat.{t + 1} (ULift.{t + 1} Λ) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X Λ) :=
  haveI := (koszulConstantUnit_local X Λ).1
  haveI := (koszulConstantUnit_local X Λ).2
  siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ) ⋙
    PresheafOfModules.sheafification (koszulConstantUnit X Λ)

/-- Constants preserve zero morphisms. -/
theorem koszulConstantFunctor_preservesZero :
    (koszulConstantFunctor X Λ).PreservesZeroMorphisms := by
  constructor
  intro M N
  apply (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X Λ)).map_injective
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).map
        (0 : M ⟶ N))) = 0
  have h : (PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).map
        (0 : M ⟶ N)) = 0 := by rfl
  rw [h, Functor.map_zero]

attribute [local instance] koszulConstantFunctor_preservesZero

/-- The cohomologically reindexed Koszul complex of the positive power m+1.
The lift changes only the carrier universe, not the coefficient ring. -/
def koszulPower (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    CochainComplex (ModuleCat.{t + 1} (ULift.{t + 1} Λ)) ℤ :=
  (ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
    (fun j ↦ ULift.up (f j ^ (m + 1)))).extend ComplexShape.embeddingDownNat

/-- The constant Koszul sheaf complex. -/
def koszulPowerSheaf (r : ℕ) (f : Fin r → Λ) (m : ℕ) :=
  ((koszulConstantFunctor X Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (koszulPower Λ r f m)

/-- Exterior map on the free generators, e_j ↦ f_j e_j. -/
def koszulPowerGenerator (r : ℕ) (f : Fin r → Λ) :
    (Fin r →₀ ULift.{t + 1} Λ) →ₗ[ULift.{t + 1} Λ] (Fin r →₀ ULift.{t + 1} Λ) :=
  Finsupp.linearCombination (ULift.{t + 1} Λ) (fun j ↦ Finsupp.single j (ULift.up (f j)))

private theorem koszulExteriorMap_coe (R : Type t) [CommRing R] (r n : ℕ)
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

private theorem koszulContract_natural (R : Type t) [CommRing R] (r : ℕ)
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
theorem koszulPowerTransition_comm (r : ℕ) (f : Fin r → Λ) (m i j : ℕ) :
    ModuleCat.ofHom (exteriorPower.map i (koszulPowerGenerator Λ r f)) ≫
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1)))).d i j =
    (ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
      (fun k ↦ ULift.up (f k ^ (m + 2)))).d i j ≫
        ModuleCat.ofHom (exteriorPower.map j (koszulPowerGenerator Λ r f)) := by
  by_cases hij : i = j + 1
  · subst i
    dsimp only [ExteriorAlgebra.koszulComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (ExteriorAlgebra.koszulBoundary (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1))) j
        (exteriorPower.map (j + 1) (koszulPowerGenerator Λ r f) x) :
          ExteriorAlgebra (ULift.{t + 1} Λ) (Fin r →₀ ULift.{t + 1} Λ)) =
      (exteriorPower.map j (koszulPowerGenerator Λ r f)
        (ExteriorAlgebra.koszulBoundary (ULift.{t + 1} Λ) r
          (fun k ↦ ULift.up (f k ^ (m + 2))) j x) :
            ExteriorAlgebra (ULift.{t + 1} Λ) (Fin r →₀ ULift.{t + 1} Λ))
    simp only [koszulExteriorMap_coe, ExteriorAlgebra.koszulBoundary,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    apply koszulContract_natural
    apply Finsupp.lhom_ext
    intro k c
    simp only [LinearMap.comp_apply, koszulPowerGenerator,
      Finsupp.linearCombination_single, map_smul, smul_eq_mul]
    congr 1
    exact congrArg ULift.up (by simpa [Nat.add_assoc, mul_comm] using
      (pow_succ (f k) (m + 1)).symm)
  · have hn : ¬ (ComplexShape.down ℕ).Rel i j := by
      simpa only [ComplexShape.down_Rel, eq_comm] using hij
    rw [HomologicalComplex.shape _ i j hn, HomologicalComplex.shape _ i j hn,
      zero_comp, comp_zero]

/-- The specified exterior-algebra transition, followed by cohomological reindexing. -/
def koszulPowerTransition (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    koszulPower Λ r f (m + 1) ⟶ koszulPower Λ r f m :=
  HomologicalComplex.extendMap
    { f := fun i ↦ ModuleCat.ofHom (exteriorPower.map i (koszulPowerGenerator Λ r f))
      comm' := fun i j _ ↦ koszulPowerTransition_comm Λ r f m i j }
    ComplexShape.embeddingDownNat

/-- The canonical section 1 identifies the constant coefficient module with the unit.
The equation at every site object determines the map, not merely its isomorphism class. -/
theorem koszulConstantOne_exists :
    ∃! u : SheafOfModules.unit (adicModuleRing X Λ) ⟶
        (koszulConstantFunctor X Λ).obj (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ)),
      ∀ U : X.ProEtᵒᵖ,
        u.val.app U (1 : (adicModuleRing X Λ).obj.obj U) =
          (toSheafify (ProEt.topology X)
            ((siteConstantModulePresheafGeneral (C := X.ProEt)
              (ULift.{t + 1} Λ)).obj
              (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))).presheaf).app U
                (1 : ULift.{t + 1} Λ) := by
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let M := (koszulConstantFunctor X Λ).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let η := toSheafify (ProEt.topology X) P.presheaf
  let s : M.sections := PresheafOfModules.sectionsMk (fun U ↦ η.app U (1 : ULift.{t + 1} Λ)) (by
    intro U V g
    exact (NatTrans.naturality_apply η g (1 : ULift.{t + 1} Λ)).symm)
  refine ⟨M.unitHomEquiv.symm s, ?_, ?_⟩
  · intro U
    exact congrArg (fun z : M.sections ↦ z.val U) (M.unitHomEquiv.apply_symm_apply s)
  · intro u hu
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (hu U).trans
      (congrArg (fun z : M.sections ↦ z.val U) (M.unitHomEquiv.apply_symm_apply s)).symm

/-- The canonical constant unit map selected by its unique section formula. -/
def koszulConstantOne := (koszulConstantOne_exists X Λ).exists.choose

/-- Degree zero of the Koszul complex contains the identity coefficient unit. -/
def koszulSheafUnitZero (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    SheafOfModules.unit (adicModuleRing X Λ) ⟶ (koszulPowerSheaf X Λ r f m).X 0 :=
  koszulConstantOne X Λ ≫ (koszulConstantFunctor X Λ).map
    (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap) ≫
    (koszulConstantFunctor X Λ).map
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv

end AlgebraicGeometry.Scheme
