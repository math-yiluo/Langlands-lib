import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CuspidalSupport.DeterminantUnit

/-!
# Fixed-level finiteness of compact-coefficient classes on `G°`

Bernstein--Zelevinsky (1976), Theorem 4.14, page 41, in its compact-open form.
This is a proposition definition, not a proof.
-/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- For every positive-rank product Levi over an actual p-adic field, each
compact open subgroup of its determinant-unit subgroup `G°` has a nonzero fixed
vector in only finitely many isomorphism classes of irreducible smooth complex
representations of `G°` with compact smooth-dual coefficients. -/
def CompactCoefficientFixedLevelFinitenessTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ K : OpenSubgroup (determinantUnitSubgroup T B),
      IsCompact (K : Set (determinantUnitSubgroup T B)) →
        (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup).Finite

end Langlands.CuspidalSupport
