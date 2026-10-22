import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Classification.SupercuspidalTwist

/-! The outer block modulus on an actual Levi refinement. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric
open scoped NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
variable (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)

/-- Each outer component of a refined unipotent element has determinant norm one. -/
@[simp]
theorem determinantNorm_refinedUnipotent
    (v : refinedUnipotent F.Carrier B S) (i : Fin B.length) :
    T.determinantNorm (B.size i) (v.val i) = 1 := by
  have hv : v.val i ∈ (S i).unipotentSubgroup F.Carrier :=
    v.property i (Set.mem_univ i)
  change T.normalizedAbsUnits (determinant (v.val i)) = 1
  rw [(S i).determinant_eq_one_of_mem_unipotentSubgroup hv, map_one]

/-- The whole refined radical lies in the simultaneous norm-one determinant subgroup. -/
theorem refinedUnipotent_le_normOneLevi :
    refinedUnipotent F.Carrier B S ≤ T.normOneLevi B := by
  intro v hv
  exact (T.mem_normOneLevi B v).mpr
    (fun i => T.determinantNorm_refinedUnipotent B S ⟨v, hv⟩ i)

/-- The full outer modulus is trivial on the actual inner radical. -/
theorem refinedUnipotent_le_ker_leviModulus :
    refinedUnipotent F.Carrier B S ≤ (T.leviModulus B).ker :=
  (T.refinedUnipotent_le_normOneLevi B S).trans
    (T.normOneLevi_le_ker_leviModulus B)

@[simp]
theorem leviModulus_refinedUnipotent (v : refinedUnipotent F.Carrier B S) :
    T.leviModulus B v.val = 1 :=
  T.refinedUnipotent_le_ker_leviModulus B S v.property

/-- Thus the positive half used by outer induction is trivial on the inner radical. -/
@[simp]
theorem leviHalfModulus_refinedUnipotent (v : refinedUnipotent F.Carrier B S) :
    T.leviHalfModulus B v.val = 1 :=
  (T.leviHalfModulus_eq_one B v.val).mpr (T.leviModulus_refinedUnipotent B S v)

/-- The inverse half used by outer Jacquet normalization is trivial there as well. -/
@[simp]
theorem inverseHalfModulus_refinedUnipotent (v : refinedUnipotent F.Carrier B S) :
    Jacquet.inverseHalfCharacter (T.leviModulus B) v.val = 1 :=
  (Jacquet.inverseHalfCharacter_eq_one (T.leviModulus B) v.val).mpr
    (T.leviModulus_refinedUnipotent B S v)

/-- The outer full modulus restricted to the actual refined Levi subgroup. -/
def refinedOuterModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  (T.leviModulus B).comp (refinedLevi F.Carrier B S).subtype

@[simp]
theorem refinedOuterModulus_apply (l : refinedLevi F.Carrier B S) :
    T.refinedOuterModulus B S l = T.leviModulus B l.val := rfl

/-- The corresponding positive half, restricted using the same subgroup inclusion. -/
def refinedOuterHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  (T.leviHalfModulus B).comp (refinedLevi F.Carrier B S).subtype

@[simp]
theorem refinedOuterHalfModulus_apply (l : refinedLevi F.Carrier B S) :
    T.refinedOuterHalfModulus B S l = T.leviHalfModulus B l.val := rfl

/-- Restriction commutes with the canonical positive square root. -/
theorem refinedOuterHalfModulus_eq :
    T.refinedOuterHalfModulus B S =
      Jacquet.complexCharacter
        (Jacquet.positiveHalfCharacter (T.refinedOuterModulus B S)) := rfl

theorem refinedOuterHalfModulus_sq (l : refinedLevi F.Carrier B S) :
    T.refinedOuterHalfModulus B S l ^ 2 =
      Jacquet.complexCharacter (T.refinedOuterModulus B S) l :=
  T.leviHalfModulus_sq B l.val

/-- The inverse half convention also commutes with this actual restriction. -/
theorem inverseHalf_refinedOuterModulus :
    Jacquet.inverseHalfCharacter (T.refinedOuterModulus B S) =
      (T.refinedOuterHalfModulus B S)⁻¹ := rfl

theorem continuous_refinedOuterModulus :
    letI := T.topology
    Continuous (T.refinedOuterModulus B S) := by
  let := T.topology
  exact (T.continuous_leviModulus B).comp continuous_subtype_val

theorem isOpen_ker_refinedOuterModulus :
    letI := T.topology
    IsOpen ((T.refinedOuterModulus B S).ker :
      Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  exact (T.isOpen_ker_leviModulus B).preimage continuous_subtype_val

theorem isOpen_ker_refinedOuterHalfModulus :
    letI := T.topology
    IsOpen ((T.refinedOuterHalfModulus B S).ker :
      Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  exact (T.isOpen_ker_leviHalfModulus B).preimage continuous_subtype_val

theorem refinedOuterModulus_eq_topologicalData (U : F.TopologicalData) :
    T.refinedOuterModulus B S = U.refinedOuterModulus B S := by
  simp only [refinedOuterModulus, T.leviModulus_eq B U]

theorem refinedOuterHalfModulus_eq_topologicalData (U : F.TopologicalData) :
    T.refinedOuterHalfModulus B S = U.refinedOuterHalfModulus B S := by
  simp only [refinedOuterHalfModulus, T.leviHalfModulus_eq B U]

end Langlands.PadicField.TopologicalData
