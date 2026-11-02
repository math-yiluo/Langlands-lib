import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleDistinctReindex
import Langlands.AlgebraicGeometry.AffineEtaleUniformPointBound
import Mathlib.AlgebraicGeometry.ResidueField

/-! # A uniform bound on distinct related tuples -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] [IsAffine E.R]

/-- A bound on the number of distinct coordinates of a related tuple, obtained
from the affine étale source map of the relation. -/
noncomputable def tupleLengthBound : ℕ := by
  let := E.etale_s
  exact affineEtalePointBound E.s

variable [IsSeparated E.s]

/-- A field-valued distinct related tuple has at most `tupleLengthBound`
coordinates. The index `n` denotes a tuple with `n + 1` entries. -/
theorem tupleDistinct_fieldPoint_length_le (n : ℕ) (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ E.tupleDistinctScheme n) :
    n + 1 ≤ E.tupleLengthBound := by
  let := E.etale_s
  let a := f ≫ E.tupleDistinctProjection n 0
  let ev : Fin (n + 1) → {g : Spec (.of K) ⟶ E.R // g ≫ E.s = a} :=
    fun i => ⟨f ≫ (E.tupleDistinctOpen n).ι ≫ E.tupleRelation n i 0,
      by simp [a, tupleDistinctProjection]⟩
  have hev : Function.Injective ev := by
    intro i j hij
    apply E.tupleDistinct_coordinates_injective n f
    have h := congrArg (fun g : {g : Spec (.of K) ⟶ E.R // g ≫ E.s = a} =>
      g.val ≫ E.t) hij
    simpa [ev, tupleDistinctProjection, Category.assoc] using h
  obtain ⟨hfin, hbound⟩ := affineEtale_fibrePoints_finite_card_le E.s K a
  let := hfin
  have h := (Nat.card_le_card_of_injective ev hev).trans hbound
  simpa [tupleLengthBound] using h

/-- Distinct-tuple schemes vanish once their number of coordinates exceeds
the uniform bound. Residue-field points detect every possible scheme point. -/
theorem tupleDistinctScheme_isEmpty (n : ℕ) (hn : E.tupleLengthBound ≤ n) :
    IsEmpty (E.tupleDistinctScheme n) where
  false x := by
    have h := E.tupleDistinct_fieldPoint_length_le n
      ((E.tupleDistinctScheme n).residueField x)
      ((E.tupleDistinctScheme n).fromSpecResidueField x)
    omega

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
