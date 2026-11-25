/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Topology.Algebra.MulAction

/-!
# Scalar extraction from matrix descent defects

Source: Stacks Project, Tag 03R6 and the two-cocycle construction before Tag 03R7.
(blueprint: lem-sc-brauer-scalar-defect-scalar-data).
-/

@[expose] public section
universe u
namespace Field
open scoped TensorProduct

private theorem scalar_injective (K : Type u) [Field K] (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) (R := K)) := by
  intro x y h
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  apply Units.ext
  have hh := congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) K ↦ M.val i i) h
  simpa using hh

private theorem conjugation_defect_commutes {R : Type*} [Monoid R]
    (P Q : Rˣ) (X : R) (h : ↑P⁻¹ * X * ↑P = ↑Q⁻¹ * X * ↑Q) :
    ↑(P * Q⁻¹) * X = X * ↑(P * Q⁻¹) := by
  have hh := congrArg (fun Y : R ↦ ↑P * Y * ↑Q⁻¹) h
  have hp (Y : R) : ↑P * (↑P⁻¹ * Y) = Y := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  simpa only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one, hp] using hh.symm

/-- Scalar extraction from locally constant matrix descent lifts.
Proof: put X_a = e(1 ⊗ a). Apply g to the descent equation for h and substitute
that for g. Then P = b_g g(b_h) and b_(gh) induce the same conjugation on X_a,
so D = P b_(gh)⁻¹ commutes with X_a. The tensors 1 ⊗ a span after scalar
extension, and e is surjective, so D commutes with every matrix. Commutation
with the diagonal matrix units kills off-diagonal entries; commutation with
the remaining units makes all diagonal entries equal. Since n > 0 and D is
invertible, its common diagonal entry is a unique unit c(g,h).
Near (g,h), local constancy of b and continuity of multiplication fix b_g,
b_h and b_(gh). Each entry of the fixed b_h is algebraic over K, and its
stabilizer is Krull-open. Intersecting these finitely many stabilizers fixes
g(b_h), hence D and its diagonal unit. Thus c is jointly locally constant.
Expand b_g g(b_h) gh(b_k) in both associative orders, substitute the scalar
relations, and cancel b_(ghk). Injectivity of scalar matrices for n > 0 gives
the displayed cocycle identity. No normalization at the identity is required.
Source: Stacks Project, Tag 03R6 and the two-cocycle construction before Tag 03R7.
(blueprint: lem-sc-brauer-scalar-defect-scalar-data). -/
theorem exists_brauerScalarDefect_scalar_data (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) :
    ∃ c : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        (SeparableClosure K ≃ₐ[K] SeparableClosure K) → (SeparableClosure K)ˣ,
      IsLocallyConstant (Function.uncurry c) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (c g h) * b (g * h)) ∧
      (∀ g h k, c g h * c (g * h) k =
        g (c h k) * c g (h * k)) := by
  classical
  let D (g h : SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
    b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) * (b (g * h))⁻¹
  -- The two descent lifts have equal conjugation on all matrices.
  have hD (g h : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      D g h ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)) := by
    have hX (a : A) :
        (D g h).val * e (1 ⊗ₜ[K] a) = e (1 ⊗ₜ[K] a) * (D g h).val := by
      apply conjugation_defect_commutes
        (b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h)) (b (g * h))
      have hh := congrArg (fun M : Matrix (Fin n) (Fin n) (SeparableClosure K) ↦
        M.map g) (hdesc h a)
      rw [Matrix.map_mul, Matrix.map_mul, hdesc g a] at hh
      have hgh : (e (1 ⊗ₜ[K] a)).map (g * h) =
          ((e (1 ⊗ₜ[K] a)).map h).map g := rfl
      calc
        _ = ((b h)⁻¹).val.map g *
            (((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) * (b h).val.map g := by
          simp [Units.val_mul, mul_assoc, Matrix.GeneralLinearGroup.map]
        _ = (e (1 ⊗ₜ[K] a)).map (g * h) := by rw [hgh, hh]
        _ = _ := hdesc (g * h) a
    have hall (T : SeparableClosure K ⊗[K] A) :
        (D g h).val * e T = e T * (D g h).val := by
      induction T using TensorProduct.inductionOn with
      | tmul s a =>
          have ht : s ⊗ₜ[K] a = s • (1 ⊗ₜ[K] a) := by
            simp [TensorProduct.smul_tmul']
          rw [ht, map_smul, mul_smul_comm, smul_mul_assoc, hX]
      | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
    apply Subgroup.mem_center_iff.mpr
    intro M
    apply Units.ext
    simpa using (hall (e.symm M.val)).symm
  have hex (g h : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      ∃ c : (SeparableClosure K)ˣ,
        Matrix.GeneralLinearGroup.scalar (Fin n) c = D g h := by
    have hd := hD g h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hd
    exact hd
  -- The scalar is uniquely determined because n is positive.
  choose c hc using hex
  have hrel (g h : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (c g h) * b (g * h) := by
    rw [hc]
    simp [D, mul_assoc]
  refine ⟨c, ?_, hrel, ?_⟩
  · have hfixed (M : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)) :
        IsLocallyConstant (fun g : SeparableClosure K ≃ₐ[K] SeparableClosure K ↦
          Matrix.GeneralLinearGroup.map g.toRingHom M) := by
      have hv : IsLocallyConstant (fun g : SeparableClosure K ≃ₐ[K] SeparableClosure K ↦
          M.val.map g) :=
        (LocallyConstant.unflip (fun i ↦ LocallyConstant.unflip (fun j ↦
          ⟨_, by
            let : TopologicalSpace (SeparableClosure K) := ⊥
            let : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
            let : ContinuousSMul (SeparableClosure K ≃ₐ[K] SeparableClosure K)
                (SeparableClosure K) :=
              continuousSMul_iff_stabilizer_isOpen.mpr
                (fun y ↦ stabilizer_isOpen_of_isIntegral y)
            exact (IsLocallyConstant.iff_continuous _).mpr
              (continuous_id.smul continuous_const)⟩))).isLocallyConstant
      exact IsLocallyConstant.desc _ Units.val hv Units.val_injective
    have hact : IsLocallyConstant (fun p :
        (SeparableClosure K ≃ₐ[K] SeparableClosure K) ×
          (SeparableClosure K ≃ₐ[K] SeparableClosure K) ↦
        Matrix.GeneralLinearGroup.map p.1.toRingHom (b p.2)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro p
      have hb₂ := (hb.comp_continuous continuous_snd).eventually_eq p
      have hg := ((hfixed (b p.2)).comp_continuous continuous_fst).eventually_eq p
      filter_upwards [hb₂, hg] with q hq₁ hq₂
      change b q.2 = b p.2 at hq₁
      rw [hq₁]
      exact hq₂
    have hd : IsLocallyConstant (Function.uncurry D) :=
      ((hb.comp_continuous continuous_fst).mul hact).mul
        ((hb.comp_continuous (continuous_fst.mul continuous_snd)).inv)
    have hs : IsLocallyConstant
        (Matrix.GeneralLinearGroup.scalar (Fin n) ∘ Function.uncurry c) := by
      convert hd using 1
      funext ⟨g, h⟩
      exact hc g h
    exact IsLocallyConstant.desc _ (Matrix.GeneralLinearGroup.scalar (Fin n)) hs
      (scalar_injective (SeparableClosure K) n hn)
  · intro g h k
    suffices hu : c g h * c (g * h) k =
        Units.map g.toRingHom (c h k) * c g (h * k) by
      exact congrArg Units.val hu
    apply scalar_injective (SeparableClosure K) n hn
    apply (mul_right_cancel_iff (a := b (g * h * k))).mp
    rw [map_mul, map_mul, mul_assoc, ← hrel (g * h) k, ← mul_assoc,
      ← hrel g h]
    have hcomp : Matrix.GeneralLinearGroup.map (g * h).toRingHom (b k) =
        Matrix.GeneralLinearGroup.map g.toRingHom
          (Matrix.GeneralLinearGroup.map h.toRingHom (b k)) := rfl
    rw [mul_assoc, hcomp, ← map_mul, hrel h k, map_mul,
      Matrix.GeneralLinearGroup.map_scalar]
    rw [← mul_assoc (b g),
      ← Matrix.GeneralLinearGroup.scalar_commute (Units.map g.toRingHom (c h k)) (b g),
      mul_assoc, hrel g (h * k), ← mul_assoc, mul_assoc g h k]

end Field
