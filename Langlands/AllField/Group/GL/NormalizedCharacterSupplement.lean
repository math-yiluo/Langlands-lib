import Langlands.Group.GL.NormalizedCharacter
import Langlands.AllField.Group.GL.PadicSupplement
import Langlands.AllField.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof
/-!
# The residue-normalized determinant character

The value is the actual residue-cardinality-normalized absolute value of the
usual determinant. No unadjusted spectral norm is substituted.
-/

noncomputable section

open scoped NNReal

namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

variable (T : LocalFieldData F)

theorem determinantNorm_eq_residue_pow (n : ℕ) (g : GeneralLinear n F) :
    ((T.determinantNorm n g : ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^ (-T.ord (GeneralLinear.determinant g : F)) :=
  T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero

theorem continuous_normalizedAbsUnits :
    letI := T.topology
    Continuous T.normalizedAbsUnits := by
  let := T.topology
  exact T.continuous_normalizedAbsHom.units_map

/-- The normalized determinant is continuous for the actual matrix-unit topology. -/
def determinantNormContinuous (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F) ℝ≥0ˣ := by
  letI := T.topology
  exact
    { toMonoidHom := T.determinantNorm n
      continuous_toFun :=
        T.continuous_normalizedAbsUnits.comp (T.generalLinearDeterminant n).continuous }

/-- The existing continuous positive-character theorem applies to the actual
determinant norm on every compact matrix subgroup. -/
theorem determinantNorm_eq_one_of_mem_compact (r : ℕ) :
    letI := T.topology
    ∀ (J : Subgroup (GeneralLinear r F)),
      IsCompact (J : Set (GeneralLinear r F)) →
      ∀ g ∈ J, T.determinantNorm r g = 1 := by
  let := T.topology
  intro J hJ g hg
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact
    (T.determinantNorm r) (T.determinantNormContinuous r).continuous J hJ hg

end LocalFieldData

end Langlands
