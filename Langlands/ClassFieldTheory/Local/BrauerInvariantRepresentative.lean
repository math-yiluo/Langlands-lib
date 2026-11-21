import Langlands.ClassFieldTheory.Local.LocalDivisionBrauerOrder

/-! # Central simple representatives of prescribed local degree and invariant -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open Langlands.Brauer Langlands.CentralDivision Langlands.CentralSimple Langlands.LocalField

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

private theorem exists_csaOfInvariant (hn : 0 < n) (x : denominatorSubgroup n) :
    ∃ B : CSA.{u, u} K, Module.finrank K B = n * n ∧
      localBrauerInvariant K (classOf B) = (x : RationalModIntegers) := by
  let b := (localBrauerInvariant K).symm (x : RationalModIntegers)
  obtain ⟨A, hA⟩ := Quotient.mk_surjective b
  change classOf A = b at hA
  have hAinv : localBrauerInvariant K (classOf A) = (x : RationalModIntegers) := by
    rw [hA, AddEquiv.apply_symm_apply]
  have := IsArtinianRing.of_finite K A
  obtain ⟨r, hr, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  let : NeZero r := hr
  let : Algebra.IsCentral K D := isCentral_of_algEquiv_matrix e
  let C := divisionAlgebraCSA K D
  have hC : classOf A = classOf C :=
    (classOf_eq_of_algEquiv (B := matrix C r) e).trans (classOf_matrix C r)
  let d := reducedDegree K D
  have hdim : Module.finrank K D = d * d := finrank_eq_reducedDegree_mul_self K D
  have horder : addOrderOf (classOf C) = d := addOrderOf_localDivisionClass K D hdim
  have hdvd : d ∣ n := by
    rw [← horder, ← hC, addOrderOf_dvd_iff_nsmul_eq_zero]
    apply (localBrauerInvariant K).injective
    rw [map_nsmul, hAinv, map_zero]
    exact x.property
  obtain ⟨m, hm⟩ := hdvd
  have hm_ne : m ≠ 0 := by
    intro hm_zero
    simp [hm_zero, hn.ne'] at hm
  let : NeZero m := ⟨hm_ne⟩
  refine ⟨matrix C m, ?_, ?_⟩
  · change Module.finrank K (Matrix (Fin m) (Fin m) D) = n * n
    rw [Module.finrank_matrix, Fintype.card_fin, hdim, hm]
    ac_rfl
  · rw [classOf_matrix, ← hC, hAinv]

/-- A degree-`n` central simple algebra realizing an `n`-torsion local invariant. -/
def csaOfInvariant (hn : 0 < n) (x : denominatorSubgroup n) : CSA.{u, u} K :=
  (exists_csaOfInvariant K hn x).choose

theorem finrank_csaOfInvariant (hn : 0 < n) (x : denominatorSubgroup n) :
    Module.finrank K (csaOfInvariant K hn x) = n * n :=
  (exists_csaOfInvariant K hn x).choose_spec.1

theorem localBrauerInvariant_csaOfInvariant (hn : 0 < n) (x : denominatorSubgroup n) :
    localBrauerInvariant K (classOf (csaOfInvariant K hn x)) = (x : RationalModIntegers) :=
  (exists_csaOfInvariant K hn x).choose_spec.2

theorem localBrauerInvariant_opposite_csaOfInvariant (hn : 0 < n) (x : denominatorSubgroup n) :
    localBrauerInvariant K (classOf (opposite (csaOfInvariant K hn x))) =
      -(x : RationalModIntegers) := by
  rw [classOf_opposite, map_neg, localBrauerInvariant_csaOfInvariant]

end Langlands.ClassFieldTheory.Local
