import Langlands.Cohomology.PerfectModuleComplexHomotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The first differential of a punctual perfect complex -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex
open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra

section LocalIdeals

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A proper subideal of the maximal ideal is contained in a first-order
hyperplane after adjoining the square of the maximal ideal. -/
theorem exists_firstOrder_ideal_of_lt_maximal
    {I : Ideal R} (hI : I < maximalIdeal R) :
    ∃ J : Ideal R, I ≤ J ∧ maximalIdeal R ^ 2 ≤ J ∧ J ⋖ maximalIdeal R := by
  have hsup : I ⊔ maximalIdeal R ^ 2 < maximalIdeal R := by
    refine lt_of_le_of_ne (sup_le hI.le (Ideal.pow_le_self (by decide))) ?_
    intro heq
    have hle : maximalIdeal R ≤ I := by
      apply Submodule.le_of_le_smul_of_le_jacobson_bot
        (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson ⊥)
      simpa only [pow_two, Ideal.smul_eq_mul] using heq.ge
    exact hI.not_ge hle
  obtain ⟨J, hJ, hcov⟩ := exists_le_covBy_of_lt hsup
  exact ⟨J, le_sup_left.trans hJ, le_sup_right.trans hJ, hcov⟩

/-- First-order hyperplanes detect whether a subideal generates the maximal
ideal. This includes the case of a field. -/
theorem ideal_eq_maximal_of_firstOrder_test
    {I : Ideal R} (hI : I ≤ maximalIdeal R)
    (htest : ∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R → ¬ I ≤ J) :
    I = maximalIdeal R := by
  by_contra hne
  obtain ⟨J, hIJ, hsq, hcov⟩ :=
    exists_firstOrder_ideal_of_lt_maximal (lt_of_le_of_ne hI hne)
  exact htest J hsq hcov hIJ

end LocalIdeals

section OrderIdeal

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The order ideal of a vector is the image of evaluation on its module dual. -/
def vectorOrderIdeal (v : M) : Ideal R :=
  LinearMap.range (Module.Dual.eval R M v)

/-- Every functional sends a vector lying in `J M` into `J`. -/
theorem vectorOrderIdeal_le_of_mem_smul {J : Ideal R} {v : M}
    (hv : v ∈ J • (⊤ : Submodule R M)) : vectorOrderIdeal v ≤ J := by
  rintro _ ⟨φ, rfl⟩
  change φ v ∈ J
  refine Submodule.smul_induction_on hv
    (fun a ha m _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · simpa only [map_add] using J.add_mem hx hy

/-- In a free module, membership in `J M` can be tested on all
linear functionals. -/
theorem mem_smul_of_vectorOrderIdeal_le [Module.Free R M]
    {J : Ideal R} {v : M} (hv : vectorOrderIdeal v ≤ J) :
    v ∈ J • (⊤ : Submodule R M) := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [← b.linearCombination_repr v]
  change (∑ i ∈ (b.repr v).support, (b.repr v) i • b i) ∈ _
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem_smul _ (Submodule.mem_top)
  exact hv ⟨b.coord i, rfl⟩

theorem vectorOrderIdeal_le_iff [Module.Free R M]
    (J : Ideal R) (v : M) :
    vectorOrderIdeal v ≤ J ↔ v ∈ J • (⊤ : Submodule R M) :=
  ⟨mem_smul_of_vectorOrderIdeal_le, vectorOrderIdeal_le_of_mem_smul⟩

end OrderIdeal

section FirstDifferential

variable {R : Type u} [CommRing R]
variable (L : CochainComplex (ModuleCat.{u} R) ℤ) (e₀ : L.X 0 ≃ₗ[R] R)

/-- The order ideal of the first differential of a complex with a chosen
rank-one degree-zero term. -/
def firstDifferentialOrderIdeal : Ideal R :=
  vectorOrderIdeal ((L.d 0 1).hom (e₀.symm 1))

theorem firstDifferential_apply (x : L.X 0) :
    (L.d 0 1).hom x = e₀ x • (L.d 0 1).hom (e₀.symm 1) := by
  have hx : x = e₀ x • e₀.symm 1 := by
    apply e₀.injective
    simp
  conv_lhs => rw [hx]
  exact map_smul _ _ _

/-- The order ideal controls the whole image of the rank-one first term. -/
theorem firstDifferential_mem_smul [Module.Free R (L.X 1)]
    {J : Ideal R} (hJ : firstDifferentialOrderIdeal L e₀ ≤ J) (x : L.X 0) :
    (L.d 0 1).hom x ∈ J • (⊤ : Submodule R (L.X 1)) := by
  rw [firstDifferential_apply L e₀ x]
  exact Submodule.smul_mem _ _
    (mem_smul_of_vectorOrderIdeal_le hJ)

/-- Quotient scalar extension kills a differential taking values in `J M`. -/
theorem quotient_baseChange_d_eq_zero
    (J : Ideal R) (i j : ℤ)
    (hJ : ∀ x : L.X i, (L.d i j).hom x ∈ J • (⊤ : Submodule R (L.X j))) :
    ((baseChange (Ideal.Quotient.mk J)).obj L).d i j = 0 := by
  let ψ := Ideal.Quotient.mk J
  apply ModuleCat.ExtendScalars.hom_ext (M := L.X i)
  intro x
  change (1 : R ⧸ J) ⊗ₜ[R] (L.d i j).hom x = 0
  refine Submodule.smul_induction_on (hJ x)
    (fun r hr n _ ↦ ?_) (fun _ _ h₁ h₂ ↦ ?_)
  · rw [TensorProduct.tmul_smul]
    change (ψ r * 1) ⊗ₜ[R] n = 0
    have hr0 : ψ r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hr
    rw [hr0, zero_mul, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, h₁, h₂, add_zero]

/-- If the first differential vanishes modulo `J`, the degree-zero quotient
homology of a complex supported in nonnegative degrees is `R/J`. -/
def quotientHomologyZeroIsoOfFirstDifferential
    (hGE : L.IsStrictlyGE 0) [Module.Free R (L.X 1)]
    (J : Ideal R) (hJ : firstDifferentialOrderIdeal L e₀ ≤ J) :
    ((baseChange (Ideal.Quotient.mk J)).obj L).homology 0 ≅
      ModuleCat.of (R ⧸ J) (R ⧸ J) := by
  let N := (baseChange (Ideal.Quotient.mk J)).obj L
  have hneg : IsZero (L.X (-1)) :=
    (CochainComplex.isStrictlyGE_iff L 0).1 hGE (-1) (by norm_num)
  have hprev : N.d (-1) 0 = 0 := by
    change (ModuleCat.extendScalars (Ideal.Quotient.mk J)).map (L.d (-1) 0) = 0
    rw [hneg.eq_of_src (L.d (-1) 0) 0, Functor.map_zero]
  have hnext : N.d 0 1 = 0 :=
    quotient_baseChange_d_eq_zero L J 0 1 (firstDifferential_mem_smul L e₀ hJ)
  let E : N.homology 0 ≅ N.X 0 :=
    (N.isoHomologyπ (-1) 0 (by norm_num) hprev).symm ≪≫
      N.iCyclesIso 0 1 (by norm_num) hnext
  exact E ≪≫ (LinearEquiv.baseChange R (R ⧸ J) _ _ e₀ ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid R (R ⧸ J) (R ⧸ J)).toModuleIso

end FirstDifferential

section FirstOrderTest

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (L K : CochainComplex (ModuleCat.{u} R) ℤ)

omit [IsNoetherianRing R] in
/-- The first-order nonfreeness condition is invariant under homotopy
equivalence, before and after quotient scalar extension. -/
theorem firstOrder_nonfree_of_homotopyEquiv
    (e : HomotopyEquiv L K)
    (hK : ∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R →
      IsEmpty (((baseChange (Ideal.Quotient.mk J)).obj K).homology 0 ≅
        ModuleCat.of (R ⧸ J) (R ⧸ J))) :
    ∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R →
      IsEmpty (((baseChange (Ideal.Quotient.mk J)).obj L).homology 0 ≅
        ModuleCat.of (R ⧸ J) (R ⧸ J)) := by
  intro J hsq hcov
  constructor
  intro α
  exact (hK J hsq hcov).false
    (((baseChangeHomotopyEquiv (Ideal.Quotient.mk J) e).toHomologyIso 0).symm ≪≫ α)

/-- Condition (4) forces the order ideal of the first differential to be the
entire maximal ideal. Only local Noetherian hypotheses are needed. -/
theorem firstDifferentialOrderIdeal_eq_maximal
    (hGE : L.IsStrictlyGE 0) (e₀ : L.X 0 ≃ₗ[R] R)
    [Module.Free R (L.X 1)]
    (hmin : ∀ x : L.X 0,
      (L.d 0 1).hom x ∈ maximalIdeal R • (⊤ : Submodule R (L.X 1)))
    (hL : ∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R →
      IsEmpty (((baseChange (Ideal.Quotient.mk J)).obj L).homology 0 ≅
        ModuleCat.of (R ⧸ J) (R ⧸ J))) :
    firstDifferentialOrderIdeal L e₀ = maximalIdeal R := by
  apply ideal_eq_maximal_of_firstOrder_test
    (vectorOrderIdeal_le_of_mem_smul (hmin (e₀.symm 1)))
  intro J hsq hcov hJ
  exact (hL J hsq hcov).false
    (quotientHomologyZeroIsoOfFirstDifferential L e₀ hGE J hJ)

end FirstOrderTest

end Langlands.CommutativeAlgebra
