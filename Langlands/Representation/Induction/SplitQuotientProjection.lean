import Langlands.Representation.Induction.SplitQuotientProof
import Langlands.Analysis.Local.QuotientMeasure

/-! # Left-coset quotient comparison for a split group projection -/

namespace Langlands.Induction

variable {G L : Type*} [Group G] [Group L] [TopologicalSpace G] [TopologicalSpace L]
  (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
  (H : Subgroup G) (hker : r.ker ≤ H) (hr : Continuous r) (hs : Continuous s)

/-- The existing split quotient maps are inverse homeomorphisms when the
projection kernel is contained in the subgroup of the ambient quotient. -/
def splitQuotientProjectionHomeomorph : LeftQuotient H ≃ₜ LeftQuotient (H.comap s) where
  toFun := splitQuotientRetractMap r s hrs H hker
  invFun := splitQuotientSectionMap s H
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change Quotient.mk _ (s (r g)) = Quotient.mk _ g
      exact Quotient.sound (QuotientGroup.rightRel_apply.mpr
        (hker (splitQuotient_mul_inv_mem_ker r s hrs g)))
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h l =>
      change Quotient.mk _ (r (s l)) = Quotient.mk _ l
      rw [hrs]
  continuous_toFun := continuous_splitQuotientRetractMap r s hrs H hker hr
  continuous_invFun := continuous_splitQuotientSectionMap s H hs

@[simp]
theorem splitQuotientProjectionHomeomorph_mk (g : G) :
    splitQuotientProjectionHomeomorph r s hrs H hker hr hs (Quotient.mk _ g) =
      Quotient.mk _ (r g) := rfl

@[simp]
theorem splitQuotientProjectionHomeomorph_symm_mk (l : L) :
    (splitQuotientProjectionHomeomorph r s hrs H hker hr hs).symm (Quotient.mk _ l) =
      Quotient.mk _ (s l) := rfl

variable [IsTopologicalGroup G] [IsTopologicalGroup L]

/-- Right translations are transported by the projection, also for
nonnormal subgroups. -/
theorem splitQuotientProjectionHomeomorph_rightTranslate (g : G) (q : LeftQuotient H) :
    splitQuotientProjectionHomeomorph r s hrs H hker hr hs
        (QuotientIntegration.rightTranslate H g q) =
      QuotientIntegration.rightTranslate (H.comap s) (r g)
        (splitQuotientProjectionHomeomorph r s hrs H hker hr hs q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [QuotientIntegration.rightTranslate_mk, splitQuotientProjectionHomeomorph_mk,
      map_mul]

end Langlands.Induction
