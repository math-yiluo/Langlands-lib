import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentOrderStatement
import Langlands.HarmonicAnalysis.UnitConjugation.DivisionIntegers
import Langlands.HarmonicAnalysis.UnitConjugation.MatrixIdempotentOrder
import Langlands.HarmonicAnalysis.UnitConjugation.KernelFlagCommutator
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# A compact open order containing idempotent generators of all left ideals

This module proves `SemisimpleIdempotentOrderStatement` (`semisimpleIdempotentOrder`): by the
Wedderburn–Artin theorem a finite-dimensional semisimple algebra `A` over a nonarchimedean local
field `F` is a product of matrix algebras `M_{d_i}(D_i)` over finite-dimensional division
algebras; the matrices with entries in the integer rings `divisionIntegers (D i)` form a compact
open order, and integral Gaussian elimination gives idempotent generators of all left ideals.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open ValuativeRel

/-- **Idempotent generators in a compact open order** (`SemisimpleIdempotentOrderStatement`). -/
theorem semisimpleIdempotentOrder : SemisimpleIdempotentOrderStatement.{u, v} := by
  intro F _ _ _ _ A _ _ _ _ _ _
  classical
  have := IsModuleTopology.isTopologicalRing F A
  have := IsModuleTopology.toContinuousAdd F A
  obtain ⟨n, D, d, _, _, _, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F A
  let _ : ∀ i, TopologicalSpace (D i) := fun i => moduleTopology F (D i)
  have _ : ∀ i, IsModuleTopology F (D i) := fun i => ⟨rfl⟩
  let O : ∀ i, Subring (D i) := fun i => divisionIntegers (F := F) (D i)
  -- the order
  let R : Subring A :=
    { carrier := {x | ∀ i a b, φ x i a b ∈ O i}
      mul_mem' := fun {x y} hx hy i a b => by
        simp only [Set.mem_ofPred_eq] at hx hy
        rw [map_mul, Pi.mul_apply, Matrix.mul_apply]
        exact (O i).sum_mem fun k _ => (O i).mul_mem (hx i a k) (hy i k b)
      one_mem' := fun i a b => by
        rw [map_one, Pi.one_apply, Matrix.one_apply]
        split_ifs
        · exact (O i).one_mem
        · exact (O i).zero_mem
      add_mem' := fun {x y} hx hy i a b => by
        simp only [Set.mem_ofPred_eq] at hx hy
        rw [map_add]
        exact (O i).add_mem (hx i a b) (hy i a b)
      zero_mem' := fun i a b => by
        rw [map_zero]
        exact (O i).zero_mem
      neg_mem' := fun {x} hx i a b => by
        simp only [Set.mem_ofPred_eq] at hx
        rw [map_neg]
        exact (O i).neg_mem (hx i a b) }
  have hmemR : ∀ x, x ∈ R ↔ ∀ i a b, φ x i a b ∈ O i := fun x => Iff.rfl
  -- coordinates are continuous
  have := IsModuleTopology.toContinuousSMul F A
  have hcoord : ∀ i a b, Continuous fun x : A => φ x i a b := by
    intro i a b
    have := IsModuleTopology.toContinuousAdd F (D i)
    have := IsModuleTopology.toContinuousSMul F (D i)
    let c : A →ₗ[F] D i :=
      { toFun := fun x => φ x i a b
        map_add' := fun x y => by simp
        map_smul' := fun r x => by simp }
    exact IsModuleTopology.continuous_of_linearMap c
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · -- compactness: `R` is the image of a product of compact sets
    let B' := ∀ i, Fin (d i) → Fin (d i) → D i
    let Ψ : B' →ₗ[F] A :=
      { toFun := fun M => φ.symm fun i => Matrix.of (M i)
        map_add' := fun M N => by rw [← map_add]; rfl
        map_smul' := fun r M => by rw [← map_smul]; rfl }
    have hΨ : Continuous Ψ := IsModuleTopology.continuous_of_linearMap Ψ
    let K : Set B' := Set.univ.pi fun i => Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (O i : Set (D i))
    have hK : IsCompact K := isCompact_univ_pi fun i => isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_divisionIntegers (D i)
    have hRK : (R : Set A) = Ψ '' K := by
      ext x
      constructor
      · intro hx
        refine ⟨fun i a b => φ x i a b, ?_, ?_⟩
        · intro i _ a _ b _
          exact (hmemR x).mp hx i a b
        · change φ.symm (fun i => Matrix.of fun a b => φ x i a b) = x
          exact φ.symm_apply_apply x
      · rintro ⟨M, hM, rfl⟩
        intro i a b
        change φ (φ.symm fun i => Matrix.of (M i)) i a b ∈ O i
        rw [φ.apply_symm_apply, Matrix.of_apply]
        exact hM i trivial a trivial b trivial
    rw [hRK]
    exact hK.image hΨ
  · -- openness: a finite intersection of preimages of open sets
    have : (R : Set A) = ⋂ i, ⋂ a, ⋂ b, (fun x : A => φ x i a b) ⁻¹' (O i : Set (D i)) := by
      ext x; simp [hmemR]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => (isOpen_divisionIntegers (D i)).preimage (hcoord i a b)
  · -- stability under the integers of `F`
    intro c hc x hx i a b
    rw [map_smul, Pi.smul_apply, Matrix.smul_apply]
    exact smul_mem_divisionIntegers (D i) hc ((hmemR x).mp hx i a b)
  · -- idempotent generators
    intro J
    let B := ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)
    let J' : Submodule B B :=
      { carrier := {y | φ.symm y ∈ J}
        add_mem' := fun {y z} hy hz => by
          simp only [Set.mem_ofPred_eq, map_add] at hy hz ⊢
          exact J.add_mem hy hz
        zero_mem' := by simp
        smul_mem' := fun c y hy => by
          simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hy ⊢
          exact J.smul_mem _ hy }
    obtain ⟨e', he'O, he'2, he'J⟩ := exists_idempotent_pi
      (fun i (P : Matrix (Fin (d i)) (Fin (d i)) (D i)) => ∀ a b, P a b ∈ O i)
      (fun i Ji => by
        obtain ⟨P, hP, hP2, hPJ⟩ :=
          exists_integral_idempotent_matrix (divisionNormValuation (F := F) (D i)) Ji
        exact ⟨P, fun a b => hP a b, hP2, hPJ⟩) J'
    have hidem : IsIdempotentElem (φ.symm e') := by
      show φ.symm e' * φ.symm e' = φ.symm e'
      rw [← map_mul, he'2]
    refine ⟨φ.symm e', ?_, hidem, ?_⟩
    · intro i a b
      rw [φ.apply_symm_apply]
      exact he'O i a b
    · ext x
      rw [mem_span_singleton_iff_mul_eq hidem]
      have h1 : x ∈ J ↔ φ x ∈ J' := by
        change x ∈ J ↔ φ.symm (φ x) ∈ J
        rw [φ.symm_apply_apply]
      rw [h1, he'J]
      constructor
      · intro h
        apply φ.injective
        rw [map_mul, φ.apply_symm_apply, h]
      · intro h
        rw [← h, map_mul, φ.apply_symm_apply, mul_assoc, he'2]

end Langlands.HarmonicAnalysis.UnitConjugation
