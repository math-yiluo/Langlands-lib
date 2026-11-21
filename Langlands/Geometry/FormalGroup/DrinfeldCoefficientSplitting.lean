import Langlands.Geometry.FormalGroup.DrinfeldSubfieldCharacters
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.LocalRing.Module

/-! # Splitting the Drinfeld coefficient algebra -/

noncomputable section

open scoped BigOperators TensorProduct

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision
open CategoryTheory

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

local instance : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {π : 𝒪[K]} {B B' : Nilp.{u, v} 𝒪[K] π}
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
  (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
  (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)

/-- Evaluation on the lifted characters of the actual unramified coefficient algebra. -/
def subfieldCyclicEvaluation :
    B.obj ⊗[𝒪[K]] SubfieldIntegerRing K D ι →ₐ[B.obj]
      (Fin (CentralSimple.reducedDegree K D) → B.obj) :=
  AlgHom.pi fun i => AlgHom.liftEquiv 𝒪[K] B.obj _ B.obj
    (subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i) ψ)

@[simp]
theorem subfieldCyclicEvaluation_tmul (b : B.obj) (a : SubfieldIntegerRing K D ι)
    (i : Fin (CentralSimple.reducedDegree K D)) :
    subfieldCyclicEvaluation hL j ψ (b ⊗ₜ[𝒪[K]] a) i =
      b * subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i) ψ a := rfl

private theorem subfieldCyclicEvaluation_surjective :
    Function.Surjective (subfieldCyclicEvaluation hL j ψ) := by
  classical
  let d := CentralSimple.reducedDegree K D
  let ev := subfieldCyclicEvaluation hL j ψ
  let χ := fun i => subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i) ψ
  have coordinate (i : Fin d) :
      ∃ z : B.obj ⊗[𝒪[K]] SubfieldIntegerRing K D ι, ev z = Pi.single i 1 := by
    have factor (k : Fin d) :
        ∃ t : B.obj ⊗[𝒪[K]] SubfieldIntegerRing K D ι, ev t i = 1 ∧ (k ≠ i → ev t k = 0) := by
      by_cases hk : k = i
      · exact ⟨1, by simp [ev], fun h => (h hk).elim⟩
      obtain ⟨a, u, hu⟩ := subfieldCyclicCharacter_lifts_separated hL j ψ (Ne.symm hk)
      refine ⟨((↑(u⁻¹) : B.obj) ⊗ₜ[𝒪[K]] a) -
        ((↑(u⁻¹) * χ k a) ⊗ₜ[𝒪[K]] (1 : SubfieldIntegerRing K D ι)), ?_, ?_⟩
      · change ↑u = χ i a - χ k a at hu
        simp only [ev, map_sub, Pi.sub_apply, subfieldCyclicEvaluation_tmul, map_one, mul_one]
        change ↑(u⁻¹) * χ i a - ↑(u⁻¹) * χ k a = 1
        rw [← mul_sub, ← hu, Units.inv_mul]
      · intro _
        simp [ev, χ]
    choose t ht using factor
    refine ⟨∏ k, t k, ?_⟩
    funext k
    rw [map_prod, Finset.prod_apply]
    by_cases hk : k = i
    · subst k
      simp [Pi.single_eq_same, fun l => (ht l).1]
    · rw [Pi.single_eq_of_ne hk]
      exact Finset.prod_eq_zero (Finset.mem_univ k) ((ht k).2 hk)
  choose z hz using coordinate
  intro g
  refine ⟨∑ i, g i • z i, ?_⟩
  funext k
  change ev (∑ i, g i • z i) k = g k
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, hz, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi.symm]
  · simp

/-- The residue coordinate splits the base change of the actual coefficient algebra. -/
def subfieldCyclicSplitting (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) :
    B.obj ⊗[𝒪[K]] SubfieldIntegerRing K D ι ≃ₐ[B.obj]
      (Fin (CentralSimple.reducedDegree K D) → B.obj) := by
  let C := SubfieldIntegerRing K D ι
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  let : Module.Free 𝒪[K] C := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasisOfFinrankEq 𝒪[K] C (subfieldInteger_finrank ι hL)
  let ev := subfieldCyclicEvaluation hL j ψ
  let e := (b.baseChange B.obj).equivFun
  exact AlgEquiv.ofBijective ev (OrzechProperty.bijective_of_surjective_of_injective
    e.toLinearMap ev.toLinearMap e.injective (subfieldCyclicEvaluation_surjective hL j ψ))

@[simp]
theorem subfieldCyclicSplitting_tmul (b : B.obj) (a : SubfieldIntegerRing K D ι)
    (i : Fin (CentralSimple.reducedDegree K D)) :
    subfieldCyclicSplitting hL j ψ (b ⊗ₜ[𝒪[K]] a) i =
      b * subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i) ψ a := rfl

/-- The splitting is compatible with every affine base change and its induced residue coordinate. -/
theorem subfieldCyclicSplitting_natural (f : B ⟶ B')
    (t : B.obj ⊗[𝒪[K]] SubfieldIntegerRing K D ι)
    (i : Fin (CentralSimple.reducedDegree K D)) :
    subfieldCyclicSplitting hL j ((Nilp.reductionMap f.hom.hom).comp ψ)
        (Algebra.TensorProduct.map f.hom.hom (AlgHom.id 𝒪[K] _) t) i =
      f.hom.hom (subfieldCyclicSplitting hL j ψ t i) := by
  induction t using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, subfieldCyclicSplitting_tmul,
      map_mul]
    exact congrArg ((f.hom.hom b) * ·) (AlgHom.congr_fun (subfieldCoefficientLift_natural hL
      (subfieldCyclicCharacter ι hL j i) f ψ) a).symm
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

end Langlands.FormalGroup.LocalDivision
