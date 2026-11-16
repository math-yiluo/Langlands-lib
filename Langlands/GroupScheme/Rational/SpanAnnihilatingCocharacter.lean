import Langlands.GroupScheme.Rational.GenericCocharacter
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Integral cocharacters detecting a rational character subspace -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A rational character subspace is annihilated by an actual integral
cocharacter which is nonzero on every member of a specified finite set
outside that subspace. -/
theorem IsSplitTorus.exists_cocharacter_zero_iff_mem_subspace
    (hT : IsSplitTorus T.toGrp)
    (W : Submodule ℚ (ℚ ⊗[ℤ] characterLattice T))
    (R : Set (characterLattice T)) (hR : R.Finite) :
    ∃ ν : cocharacterLattice T,
      (∀ α : characterLattice T, toRat α ∈ W → latticePairing T α ν = 0) ∧
      ∀ α ∈ R, latticePairing T α ν = 0 ↔ toRat α ∈ W := by
  classical
  let s : Set (characterLattice T) := {α | α ∈ R ∧ toRat α ∉ W}
  have hs : s.Finite := hR.subset (fun _ hα => hα.1)
  let := hs.fintype
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ)
    (fun α : s => W.mkQ (toRat (α : characterLattice T))) (fun α h => by
      exact α.property.2 ((Submodule.Quotient.mk_eq_zero W).mp h))
  obtain ⟨d, hd, ν, hν⟩ := hT.exists_positive_multiple_pairing (f.comp W.mkQ)
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hvanish (α : characterLattice T) (hα : toRat α ∈ W) :
      latticePairing T α ν = 0 := by
    have h := hν α
    have hq : W.mkQ (toRat α) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hα
    simp only [LinearMap.comp_apply, hq, map_zero, mul_zero] at h
    exact_mod_cast h
  refine ⟨ν, hvanish, fun α hα => ⟨?_, hvanish α⟩⟩
  intro hzero
  by_contra hnot
  have h := hν α
  rw [hzero, Int.cast_zero] at h
  exact (mul_ne_zero hd0 (hf ⟨α, hα, hnot⟩)) h.symm

/-- A single integral cocharacter detects the rational span of any chosen
character set among finitely many test characters. -/
theorem IsSplitTorus.exists_cocharacter_zero_iff_mem_ratSpan
    (hT : IsSplitTorus T.toGrp)
    (J R : Set (characterLattice T)) (hR : R.Finite) :
    ∃ ν : cocharacterLattice T,
      (∀ β ∈ J, latticePairing T β ν = 0) ∧
      ∀ α ∈ R, latticePairing T α ν = 0 ↔ toRat α ∈ ratSpan J := by
  obtain ⟨ν, hvanish, htest⟩ :=
    hT.exists_cocharacter_zero_iff_mem_subspace (ratSpan J) R hR
  exact ⟨ν, fun β hβ => hvanish β (toRat_mem_ratSpan hβ), htest⟩

/-- Uniform finite zero-set choice on the actual integral lattices of a split torus. -/
def SpanAnnihilatingCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp →
      ∀ J R : Set (characterLattice T), R.Finite →
        ∃ ν : cocharacterLattice T,
          (∀ β ∈ J, latticePairing T β ν = 0) ∧
          ∀ α ∈ R, latticePairing T α ν = 0 ↔ toRat α ∈ ratSpan J

/-- Quotient-space hyperplane avoidance and positive denominator clearing
give an actual integral cocharacter with the specified finite zero set. -/
theorem spanAnnihilatingCocharacter : SpanAnnihilatingCocharacterStatement.{u} := by
  intro k _ T hT J R hR
  exact hT.exists_cocharacter_zero_iff_mem_ratSpan J R hR

end Langlands.GroupScheme
