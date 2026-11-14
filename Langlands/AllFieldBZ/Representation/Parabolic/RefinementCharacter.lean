import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Parabolic.RefinementCharacter

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinementCharacter`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinementCharacter` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric
open scoped NNReal
universe u

variable {F : LocalFieldPackage.{u}}
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

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
