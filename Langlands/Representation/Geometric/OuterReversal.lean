import Langlands.Representation.Geometric.CoarseLeviReversal
import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Tensor.FiniteRegrouping
import Langlands.Representation.Aubert.RefinedAlternatingConstruction
import Langlands.Group.GL.ReverseBlocks

/-! Outer reversal of refinements and their actual product subgroups. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear OppositeCuspidalJacquetFiltration

universe uF
variable {n : ℕ} (B : BlockShape n)

/-- Reindex the outer blocks; each inner ordered block shape is retained. -/
def outerReverseRefinement : BlockRefinement B ≃ BlockRefinement B.reverse :=
  (Equiv.piCongrLeft (fun i => BlockShape (B.size i)) Fin.revPerm).symm

@[simp] theorem outerReverseRefinement_apply (S : BlockRefinement B) (i : Fin B.length) :
    outerReverseRefinement B S i = S i.rev := rfl

@[simp] theorem outerReverseRefinement_symm_apply_image
    (S : BlockRefinement B.reverse) (i : Fin B.length) :
    (outerReverseRefinement B).symm S i.rev = S i :=
  Equiv.piCongrLeft_apply_apply (fun i => BlockShape (B.size i)) Fin.revPerm S i

/-- The product-Levi sign is unchanged by outer reversal. -/
theorem refinementSignExponent_outerReverse (S : BlockRefinement B) :
    Aubert.refinementSignExponent B.reverse (outerReverseRefinement B S) =
      Aubert.refinementSignExponent B S :=
  Equiv.sum_comp Fin.revPerm (fun i => B.size i - (S i).length)

section Groups

variable (F : Type uF) [CommRing F] (S : BlockRefinement B)

@[simp] theorem outerReverseLeviEquiv_symm_apply_image
    (m : B.reverse.Levi F) (i : Fin B.length) :
    (leviReverseEquiv (R := F) B).symm m i.rev = m i :=
  FiniteTensor.reindexGroup_symm_apply_image
    (fun i => GeneralLinear (B.size i) F) Fin.revPerm m i

/-- Outer reindexing preserves the actual refined upper parabolic. -/
theorem outerReverseLeviEquiv_mem_refinedParabolic_iff (m : B.Levi F) :
    leviReverseEquiv (R := F) B m ∈
        refinedParabolic F B.reverse (outerReverseRefinement B S) ↔
      m ∈ refinedParabolic F B S := by
  simp only [mem_refinedParabolic]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective i
    exact h j
  · intro h i
    exact h i.rev

/-- Outer reindexing preserves the actual refined diagonal Levi subgroup. -/
theorem outerReverseLeviEquiv_mem_refinedLevi_iff (m : B.Levi F) :
    leviReverseEquiv (R := F) B m ∈
        refinedLevi F B.reverse (outerReverseRefinement B S) ↔
      m ∈ refinedLevi F B S := by
  simp only [mem_refinedLevi]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective i
    exact h j
  · intro h i
    exact h i.rev

/-- Restrict outer reindexing to the two actual refined parabolic subgroups. -/
def outerReverseRefinedParabolicEquiv :
    refinedParabolic F B S ≃*
      refinedParabolic F B.reverse (outerReverseRefinement B S) where
  toFun q := ⟨leviReverseEquiv (R := F) B q.val,
    (outerReverseLeviEquiv_mem_refinedParabolic_iff B F S q.val).mpr q.property⟩
  invFun q := ⟨(leviReverseEquiv (R := F) B).symm q.val,
    (outerReverseLeviEquiv_mem_refinedParabolic_iff B F S _).mp
      (by simpa only [MulEquiv.apply_symm_apply] using q.property)⟩
  left_inv q := Subtype.ext ((leviReverseEquiv (R := F) B).symm_apply_apply q.val)
  right_inv q := Subtype.ext ((leviReverseEquiv (R := F) B).apply_symm_apply q.val)
  map_mul' _ _ := rfl

/-- Restrict outer reindexing to the two actual refined diagonal Levi subgroups. -/
def outerReverseRefinedLeviEquiv :
    refinedLevi F B S ≃* refinedLevi F B.reverse (outerReverseRefinement B S) where
  toFun m := ⟨leviReverseEquiv (R := F) B m.val,
    (outerReverseLeviEquiv_mem_refinedLevi_iff B F S m.val).mpr m.property⟩
  invFun m := ⟨(leviReverseEquiv (R := F) B).symm m.val,
    (outerReverseLeviEquiv_mem_refinedLevi_iff B F S _).mp
      (by simpa only [MulEquiv.apply_symm_apply] using m.property)⟩
  left_inv m := Subtype.ext ((leviReverseEquiv (R := F) B).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((leviReverseEquiv (R := F) B).apply_symm_apply m.val)
  map_mul' _ _ := rfl

@[simp] theorem outerReverseRefinedParabolicEquiv_val
    (q : refinedParabolic F B S) :
    (outerReverseRefinedParabolicEquiv B F S q).val =
      leviReverseEquiv (R := F) B q.val := rfl

@[simp] theorem outerReverseRefinedLeviEquiv_val (m : refinedLevi F B S) :
    (outerReverseRefinedLeviEquiv B F S m).val = leviReverseEquiv (R := F) B m.val := rfl

/-- The actual subgroup-valued diagonal projection commutes with outer reversal. -/
theorem refinedLeviProjection_outerReverse (q : refinedParabolic F B S) :
    refinedLeviProjection F B.reverse (outerReverseRefinement B S)
        (outerReverseRefinedParabolicEquiv B F S q) =
      outerReverseRefinedLeviEquiv B F S (refinedLeviProjection F B S q) := rfl

variable [TopologicalSpace F]

/-- Outer reversal is bicontinuous for the product topology. -/
def outerReverseLeviEquivContinuous : B.Levi F ≃ₜ* B.reverse.Levi F :=
  FiniteTensor.reindexGroupContinuous (fun i => GeneralLinear (B.size i) F) Fin.revPerm

/-- The refined parabolic restriction has its actual subgroup topologies. -/
def outerReverseRefinedParabolicEquivContinuous :
    refinedParabolic F B S ≃ₜ*
      refinedParabolic F B.reverse (outerReverseRefinement B S) where
  toMulEquiv := outerReverseRefinedParabolicEquiv B F S
  continuous_toFun := ((outerReverseLeviEquivContinuous B F).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((outerReverseLeviEquivContinuous B F).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

/-- The refined diagonal restriction has its actual subgroup topologies. -/
def outerReverseRefinedLeviEquivContinuous :
    refinedLevi F B S ≃ₜ* refinedLevi F B.reverse (outerReverseRefinement B S) where
  toMulEquiv := outerReverseRefinedLeviEquiv B F S
  continuous_toFun := ((outerReverseLeviEquivContinuous B F).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((outerReverseLeviEquivContinuous B F).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

end Groups
end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open Geometric GeneralLinear
open scoped BigOperators

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Reindexing the outer factors leaves the full positive refined modulus unchanged. -/
theorem refinedLeviModulus_outerReverse (m : refinedLevi F.Carrier B S) :
    T.refinedLeviModulus B.reverse (outerReverseRefinement B S)
        (outerReverseRefinedLeviEquiv B F.Carrier S m) =
      T.refinedLeviModulus B S m := by
  rw [T.refinedLeviModulus_apply, T.refinedLeviModulus_apply]
  exact Equiv.prod_comp Fin.revPerm
    (fun i => T.leviModulus (S i) (refinedLeviBlock B S i m))

/-- The canonical positive complex half modulus obeys the same equality. -/
theorem refinedLeviHalfModulus_outerReverse (m : refinedLevi F.Carrier B S) :
    T.refinedLeviHalfModulus B.reverse (outerReverseRefinement B S)
        (outerReverseRefinedLeviEquiv B F.Carrier S m) =
      T.refinedLeviHalfModulus B S m := by
  apply Units.ext
  simp only [refinedLeviHalfModulus_apply, T.refinedLeviModulus_outerReverse]

/-- Outer reversal preserves the positive normalized-induction covariance character. -/
theorem refinedParabolicHalfModulus_outerReverse (q : refinedParabolic F.Carrier B S) :
    T.refinedParabolicHalfModulus B.reverse (outerReverseRefinement B S)
        (outerReverseRefinedParabolicEquiv B F.Carrier S q) =
      T.refinedParabolicHalfModulus B S q := by
  rw [refinedParabolicHalfModulus_apply, refinedParabolicHalfModulus_apply,
    refinedLeviProjection_outerReverse, T.refinedLeviHalfModulus_outerReverse]

end Langlands.PadicField.TopologicalData
