import Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit
/-!
# Fixed-level finiteness of compact-coefficient classes on `G°`

Bernstein--Zelevinsky (1976), Theorem 4.14, page 41, in its compact-open form.
This is a proposition definition, not a proof.
-/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding CompactCoefficientFixedLevelFinitenessTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

/-- For every positive-rank product Levi over an actual nonarchimedean local field, each
compact open subgroup of its determinant-unit subgroup `G°` has a nonzero fixed
vector in only finitely many isomorphism classes of irreducible smooth complex
representations of `G°` with compact smooth-dual coefficients. -/
def CompactCoefficientFixedLevelFinitenessTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ K : OpenSubgroup (determinantUnitSubgroup T B),
      IsCompact (K : Set (determinantUnitSubgroup T B)) →
        (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup).Finite

end Langlands.AllField.CuspidalSupport
