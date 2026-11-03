import Langlands.Representation.Character.ExactK0Targets
import Langlands.Representation.Character.SeparationProof
import Langlands.LinearAlgebra.FiniteSimpleTrace

/-! # Linear independence of finite families of actual distribution characters -/

noncomputable section

universe uG uV

namespace Langlands.Character

open MeasureTheory

/-- Bernstein--Zelevinsky (1976), Proposition 2.19, for the actual distribution
characters, without restricting the representation carriers to finite dimension. -/
theorem finiteFamilyLinearIndependence :
    FiniteFamilyLinearIndependenceStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ r A hA hirr hne
  classical
  have hvex : ∀ i, ∃ v : A i, v ≠ 0 := fun i => by
    have := CharacterSeparation.nontrivial_of_isIrreducible (hirr i)
    exact exists_ne 0
  choose v hv using hvex
  choose U hU using fun i => (A i).isSmooth (v i)
  obtain ⟨K, hKU, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅
    (Finset.univ.inf U)
  have hvK (i) : v i ∈ fixedVectors (A i).representation K.toSubgroup := by
    intro k
    have hKi : K ≤ U i := hKU.trans (Finset.inf_le (Finset.mem_univ i))
    exact hU i ⟨k, hKi k.property⟩
  let M : Fin r → Type uV := fun i => fixedVectors (A i).representation K.toSubgroup
  let : ∀ i, Module (Hecke.HeckeAlgebra.Corner μ K hK) (M i) :=
    fun i => Hecke.cornerModule μ (A i).representation (A i).isSmooth K hK
  have : ∀ i, IsScalarTower ℂ (Hecke.HeckeAlgebra.Corner μ K hK) (M i) :=
    fun i => Hecke.cornerModule_isScalarTower μ (A i).representation (A i).isSmooth K hK
  have : ∀ i, FiniteDimensional ℂ (M i) := fun i => (hA i).2 K
  have : ∀ i, IsSimpleModule (Hecke.HeckeAlgebra.Corner μ K hK) (M i) := by
    intro i
    apply CompactCoefficientClass.isSimpleModule_fixedVectors μ
      (A i).representation (A i).isSmooth K hK (hirr i)
    intro h
    exact hv i ((Submodule.mem_bot ℂ).mp (h ▸ hvK i))
  have hcorner : Pairwise (fun i j =>
      ¬ Nonempty (M i ≃ₗ[Hecke.HeckeAlgebra.Corner μ K hK] M j)) := by
    intro i j hij ⟨φ⟩
    apply hne hij
    let a : M i := ⟨v i, hvK i⟩
    have hb : ((φ a : M j) : A j) ≠ 0 := by
      intro h
      have h0 : φ a = 0 := Subtype.ext h
      exact hv i (congrArg Subtype.val (φ.map_eq_zero_iff.mp h0))
    refine Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff μ K hK
      (A i).isSmooth (hirr i) (A j).isSmooth (hirr j) a (φ a) (hv i) hb
      fun e => ?_
    have hφ : φ (Hecke.cornerAction μ (A i).representation (A i).isSmooth K hK e a) =
        Hecke.cornerAction μ (A j).representation (A j).isSmooth K hK e (φ a) :=
      φ.map_smul e a
    rw [← hφ, φ.map_eq_zero_iff]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply FiniteSimpleTrace.eq_zero_of_sum_trace_eq_zero M hcorner c
  intro e
  change ∑ i, c i * LinearMap.trace ℂ (M i)
    (Hecke.cornerAction μ (A i).representation (A i).isSmooth K hK e) = 0
  have hf := LinearMap.congr_fun hc
    (Hecke.HeckeAlgebra.toTestFunction μ
      (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e))
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply] at hf
  calc
    _ = ∑ i, c i * distribution μ (A i).representation (hA i)
        (Hecke.HeckeAlgebra.toTestFunction μ
          (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℂ => c i * z)
        (CharacterSeparation.distribution_corner μ (A i).representation
          (hA i) K hK e).symm
    _ = 0 := hf

end Langlands.Character
