import Langlands.Geometry.FormalGroup.DivisionUniformizerLevels

/-! # Transition maps of the finite division-uniformizer level groups -/

noncomputable section
universe u v

namespace Langlands.Shimura.LocalDivision
open Langlands.CentralDivision

variable (k : Type u) (D : Type v)
variable [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k] [LocallyCompactSpace k]
variable [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
variable [TopologicalSpace D] [IsModuleTopology k D]
variable (uniformizer : Dˣ) (hsmall : regularAbsoluteValue k D (uniformizer : D) < 1)

private abbrev integralUnitGroup := (maximalCompactLevel k D).subgroup
private abbrev restrictedLevel (N : ℕ) (hN : 0 < N) :=
  (uniformizerLevel k D uniformizer hsmall N hN).subgroup.subgroupOf (integralUnitGroup k D)

/-- Higher powers of the same division uniformizer give smaller congruence levels. -/
theorem uniformizerLevel_antitone {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hNM : N ≤ M) :
    (uniformizerLevel k D uniformizer hsmall M hM).subgroup ≤
      (uniformizerLevel k D uniformizer hsmall N hN).subgroup := by
  intro g hg
  change regularAbsoluteValue k D ((g : D) - 1) ≤
      regularAbsoluteValue k D (uniformizer : D) ^ M at hg
  change regularAbsoluteValue k D ((g : D) - 1) ≤
      regularAbsoluteValue k D (uniformizer : D) ^ N
  exact hg.trans (pow_le_pow_of_le_one ((regularAbsoluteValue k D).nonneg _) hsmall.le hNM)

/-- The transition from a finer to a coarser finite level is induced by the identity
on the integral unit group. -/
def uniformizerLevelTransition {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hNM : N ≤ M) :
    UniformizerLevelQuotient k D uniformizer hsmall M hM →*
      UniformizerLevelQuotient k D uniformizer hsmall N hN :=
  QuotientGroup.map (restrictedLevel k D uniformizer hsmall M hM) (restrictedLevel k D uniformizer hsmall N hN)
    (MonoidHom.id (integralUnitGroup k D)) (fun _ hg => uniformizerLevel_antitone k D uniformizer hsmall hM hN hNM hg)

@[simp]
theorem uniformizerLevelTransition_mk {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hNM : N ≤ M)
    (g : (maximalCompactLevel k D).subgroup) :
    uniformizerLevelTransition k D uniformizer hsmall hM hN hNM (QuotientGroup.mk g) =
      QuotientGroup.mk g := rfl

/-- Every coarser class has the class of the same integral unit as a preimage. -/
theorem uniformizerLevelTransition_surjective {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hNM : N ≤ M) :
    Function.Surjective (uniformizerLevelTransition k D uniformizer hsmall hM hN hNM) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, rfl⟩

@[simp]
theorem uniformizerLevelTransition_id {N : ℕ} (hN : 0 < N) :
    uniformizerLevelTransition k D uniformizer hsmall hN hN le_rfl = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  ext g
  rfl

/-- The quotient transitions form an inverse system indexed by positive integers. -/
theorem uniformizerLevelTransition_comp {L M N : ℕ} (hL : 0 < L) (hM : 0 < M) (hN : 0 < N)
    (hNM : N ≤ M) (hML : M ≤ L) :
    (uniformizerLevelTransition k D uniformizer hsmall hM hN hNM).comp
        (uniformizerLevelTransition k D uniformizer hsmall hL hM hML) =
      uniformizerLevelTransition k D uniformizer hsmall hL hN (hNM.trans hML) := by
  apply QuotientGroup.monoidHom_ext
  ext g
  rfl

/-- The kernel of reduction is the image of the coarser congruence subgroup
in the finer integral-unit quotient. -/
theorem uniformizerLevelTransition_ker {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hNM : N ≤ M) :
    (uniformizerLevelTransition k D uniformizer hsmall hM hN hNM).ker =
      (restrictedLevel k D uniformizer hsmall N hN).map (QuotientGroup.mk' (restrictedLevel k D uniformizer hsmall M hM)) := by
  unfold uniformizerLevelTransition
  erw [QuotientGroup.ker_map]
  rw [Subgroup.comap_id]

variable (d : ℕ) (hd : 0 < d)
variable (hsmallPow : regularAbsoluteValue k D ((uniformizer ^ d : Dˣ) : D) < 1)

/-- Replacing the generator by its d-th power reindexes the finite quotient by `d * N`. -/
def uniformizerLevelQuotientPowEquiv (N : ℕ) (hN : 0 < N) :
    UniformizerLevelQuotient k D (uniformizer ^ d) hsmallPow N hN ≃*
      UniformizerLevelQuotient k D uniformizer hsmall (d * N) (Nat.mul_pos hd hN) :=
  QuotientGroup.quotientMulEquivOfEq (congrArg (fun H : Subgroup Dˣ => H.subgroupOf (integralUnitGroup k D))
    (uniformizerLevel_pow_subgroup k D uniformizer hsmall N hN d hd hsmallPow))

@[simp]
theorem uniformizerLevelQuotientPowEquiv_mk (N : ℕ) (hN : 0 < N)
    (g : (maximalCompactLevel k D).subgroup) :
    uniformizerLevelQuotientPowEquiv k D uniformizer hsmall d hd hsmallPow N hN
      (QuotientGroup.mk g) = QuotientGroup.mk g :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

/-- Reindexing by a power commutes with every reduction map. -/
theorem uniformizerLevelQuotientPowEquiv_transition {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hNM : N ≤ M) (x : UniformizerLevelQuotient k D (uniformizer ^ d) hsmallPow M hM) :
    uniformizerLevelQuotientPowEquiv k D uniformizer hsmall d hd hsmallPow N hN
        (uniformizerLevelTransition k D (uniformizer ^ d) hsmallPow hM hN hNM x) =
      uniformizerLevelTransition k D uniformizer hsmall (Nat.mul_pos hd hM) (Nat.mul_pos hd hN)
        (Nat.mul_le_mul_left d hNM)
        (uniformizerLevelQuotientPowEquiv k D uniformizer hsmall d hd hsmallPow M hM x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [uniformizerLevelTransition_mk, uniformizerLevelQuotientPowEquiv_mk]

end Langlands.Shimura.LocalDivision
