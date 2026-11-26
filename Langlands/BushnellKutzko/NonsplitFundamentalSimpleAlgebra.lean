import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Centralizers of endomorphisms annihilated by a maximal ideal

For an endomorphism `φ` of a module `M` over a commutative ring `R`, the centralizer of `φ` is
the endomorphism ring of the `R[X]`-module defined by `φ` (`centralizerEquivAEval`). When a
maximal ideal of `R[X]` annihilates this module and `M` is finite over `R`, the centralizer is a
semisimple ring (`isSemisimpleRing_centralizer`). A central nilpotent element of a semisimple
ring is zero (`eq_zero_of_isNilpotent_of_commute`).
-/

noncomputable section

open Polynomial

namespace Langlands.BushnellKutzko.NonsplitSimple

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- An element commuting with `φ` commutes with every polynomial in `φ`. -/
theorem commute_aeval_of_commute {A : Type*} [Ring A] [Algebra R A] {ψ φ : A} (h : Commute ψ φ)
    (q : R[X]) : Commute ψ (aeval φ q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a ψ).mul_right (h.pow_right n)

/-- The centralizer of `φ` is the endomorphism ring of the `R[X]`-module defined by `φ`. -/
def centralizerEquivAEval (φ : Module.End R M) :
    Subalgebra.centralizer R ({φ} : Set (Module.End R M)) ≃+*
      Module.End R[X] (Module.AEval' φ) where
  toFun ψ :=
    { toFun := fun x => Module.AEval'.of φ (ψ.1 ((Module.AEval'.of φ).symm x))
      map_add' := fun x y => by simp
      map_smul' := fun q x => by
        have hψ : Commute ψ.1 φ :=
          ((Subalgebra.mem_centralizer_iff R).mp ψ.2 φ (Set.mem_singleton φ)).symm
        obtain ⟨m, rfl⟩ := (Module.AEval'.of φ).surjective x
        rw [← Module.AEval.of_aeval_smul, LinearEquiv.symm_apply_apply,
          LinearEquiv.symm_apply_apply, RingHom.id_apply, ← Module.AEval.of_aeval_smul]
        congr 1
        exact LinearMap.congr_fun (commute_aeval_of_commute hψ q).eq m }
  invFun χ := ⟨(Module.AEval'.of φ).symm.toLinearMap ∘ₗ (χ.restrictScalars R) ∘ₗ
      (Module.AEval'.of φ).toLinearMap, by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    ext m
    simp only [Module.End.mul_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.coe_restrictScalars]
    rw [← Module.AEval'.of_symm_X_smul, ← map_smul, Module.AEval'.X_smul_of]⟩
  left_inv ψ := by
    ext m
    simp
  right_inv χ := by
    ext x
    simp
  map_mul' ψ ψ' := by
    ext x
    simp
  map_add' ψ ψ' := by
    ext x
    simp

/-- If a maximal ideal of `R[X]` annihilates `M` through `φ`, the centralizer of `φ` is a
semisimple ring. -/
theorem isSemisimpleRing_centralizer [Module.Finite R M] (φ : Module.End R M) (I : Ideal R[X])
    [I.IsMaximal] (hI : ∀ q ∈ I, aeval φ q = 0) :
    IsSemisimpleRing (Subalgebra.centralizer R ({φ} : Set (Module.End R M))) := by
  have hN : Module.IsTorsionBySet R[X] (Module.AEval' φ) (I : Set R[X]) := by
    intro x q
    obtain ⟨m, rfl⟩ := (Module.AEval'.of φ).surjective x
    rw [← Module.AEval.of_aeval_smul, hI q.1 q.2]
    simp
  let := Ideal.Quotient.field I
  let := hN.module
  have : IsSemisimpleModule (R[X] ⧸ I) (Module.AEval' φ) := inferInstance
  have : IsSemisimpleModule R[X] (Module.AEval' φ) := hN.isSemisimpleModule_iff.mp this
  have := IsSemisimpleRing.moduleEnd R[X] (Module.AEval' φ)
  exact (centralizerEquivAEval φ).symm.isSemisimpleRing

/-- A central nilpotent element of a semisimple ring vanishes. -/
theorem eq_zero_of_isNilpotent_of_commute {A : Type*} [Ring A] [IsSemisimpleRing A] {w : A}
    (hw : IsNilpotent w) (hc : ∀ y, Commute w y) : w = 0 := by
  obtain ⟨m, hm⟩ := hw
  obtain ⟨e, he, hspan⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {w})
  have he0 : e = 0 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ Ideal.mem_span_singleton_self e)
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact (subsingleton_of_zero_eq_one (by simpa using hm.symm)).elim _ _
    · rw [← he.pow_eq hm0.ne', ← ha, ((hc a).symm).mul_pow, hm, mul_zero]
  have hw : w ∈ Ideal.span {w} := Ideal.mem_span_singleton_self w
  rw [hspan, he0, Ideal.span_singleton_eq_bot.mpr rfl] at hw
  exact (Submodule.mem_bot A).mp hw

end Langlands.BushnellKutzko.NonsplitSimple
