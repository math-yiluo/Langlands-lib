import Langlands.Representation.IntegerLattice.GeneralizedWeightStatement
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Proof of the simultaneous generalized-weight decomposition -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- The intersections of the maximal generalized eigenspaces of a commuting
invertible tuple, labelled by unit tuples, have finite nonzero support, are
independent, span the space, and are mapped bijectively onto themselves by
every point of the integer lattice. -/
theorem commutingTupleGeneralizedWeightDecomposition :
    CommutingTupleGeneralizedWeightDecompositionStatement.{u} := by
  intro d V _ _ _ A
  let f : Fin d → Module.End ℂ V := fun i => (A.1 i : Module.End ℂ V)
  let W' : (Fin d → ℂ) → Submodule ℂ V := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i)
  let W : (Fin d → ℂˣ) → Submodule ℂ V := fun c => W' (fun i => (c i : ℂ))
  have hcomm : ∀ i j, Commute (f i) (f j) := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl _
    · exact (A.2 hij).map (Units.coeHom _)
  have hindC : iSupIndep W' :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ)
  have hinj : Function.Injective (fun (c : Fin d → ℂˣ) (i : Fin d) => (c i : ℂ)) := by
    intro c c' h
    funext i
    exact Units.ext (congrFun h i)
  have hind : iSupIndep W := hindC.comp hinj
  have htopC : ⨆ χ, W' χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j) (fun i => (f i).iSup_maxGenEigenspace_eq_top)
  have htop : ⨆ c, W c = ⊤ := by
    apply top_unique
    rw [← htopC]
    apply iSup_le
    intro χ
    by_cases hχ : ∀ i, χ i ≠ 0
    · have hW : W' χ = W (fun i => Units.mk0 (χ i) (hχ i)) := by
        simp only [W, Units.val_mk0]
      rw [hW]
      exact le_iSup W _
    · push Not at hχ
      obtain ⟨i, hi⟩ := hχ
      intro x hx
      have hx' : x ∈ (f i).maxGenEigenspace 0 := by
        have := (Submodule.mem_iInf _).mp hx i
        rwa [hi] at this
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx'
      rw [zero_smul, sub_zero] at hk
      have hunit : IsUnit (f i ^ k) := ((A.1 i).isUnit).pow k
      have hx0 : x = 0 := (Module.End.isUnit_iff _).mp hunit |>.injective (by rw [hk, map_zero])
      rw [hx0]
      exact Submodule.zero_mem _
  refine ⟨Submodule.finite_ne_bot_of_iSupIndep hind, hind, htop, ?_⟩
  intro c n
  let ρ := tupleRepresentationEquiv d V A
  have hmaps : ∀ m : Lattice d, Set.MapsTo (ρ m) (W c) (W c) := by
    intro m x hx
    simp only [W, W', SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
    intro i
    have hc : Commute (f i) (ρ m) := by
      have h := (Commute.all (generator d i) m).map ρ
      simpa only [ρ, tupleRepresentationEquiv_generator] using h
    exact Module.End.mapsTo_maxGenEigenspace_of_comm hc _ (hx i)
  have hinv : ∀ m : Lattice d, ∀ x, ρ m⁻¹ (ρ m x) = x := by
    intro m x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ m : Lattice d, ∀ x, ρ m (ρ m⁻¹ x) = x := by
    intro m x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  exact Set.InvOn.bijOn ⟨fun x _ => hinv n x, fun x _ => hinv' n x⟩ (hmaps n) (hmaps n⁻¹)

end Langlands
