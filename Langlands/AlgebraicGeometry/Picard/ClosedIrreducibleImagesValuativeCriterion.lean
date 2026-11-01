import Langlands.AlgebraicGeometry.Picard.ClosedIrreducibleImages
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Closed irreducible images and valuative existence -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

/-- For schemes, the closed-irreducible-image condition is exactly specialization lifting. -/
theorem closedIrreducibleImages_iff_specializingMap {X S : Scheme.{u}} (p : X ⟶ S) :
    ClosedIrreducibleImages p ↔ SpecializingMap p := by
  constructor
  · intro hp
    apply (specializingMap_iff_isClosed_image_closure_singleton p.continuous).mpr
    intro x
    exact hp (closure {x}) isClosed_closure isIrreducible_singleton.closure
  · intro hp Z hZ hI
    rw [← hI.closure_genericPoint hZ]
    exact (specializingMap_iff_isClosed_image_closure_singleton p.continuous).mp
      hp hI.genericPoint

/-- Closed irreducible images after every scheme base change, without quasi-compactness. -/
def UniversallyClosedIrreducibleImages {X S : Scheme.{u}} (p : X ⟶ S) : Prop :=
  MorphismProperty.universally
    (fun _ _ q => ClosedIrreducibleImages q : MorphismProperty Scheme.{u}) p

/-- Full valuative existence is equivalent to universally closed irreducible images. -/
theorem valuativeCriterionExistence_iff_universallyClosedIrreducibleImages
    {X S : Scheme.{u}} (p : X ⟶ S) :
    ValuativeCriterion.Existence p ↔ UniversallyClosedIrreducibleImages p := by
  have h :
      (fun _ _ q => ClosedIrreducibleImages q : MorphismProperty Scheme.{u}) =
        topologically @SpecializingMap := by
    ext X S q
    exact closedIrreducibleImages_iff_specializingMap q
  unfold UniversallyClosedIrreducibleImages
  rw [h, ← ValuativeCriterion.Existence.eq]

/-- The existence part of the full valuative criterion supplies the EGA closed-image hypothesis. -/
theorem closedIrreducibleImages_of_valuativeCriterionExistence
    {X S : Scheme.{u}} (p : X ⟶ S) (hp : ValuativeCriterion.Existence p) :
    ClosedIrreducibleImages p :=
  (closedIrreducibleImages_iff_specializingMap p).mpr
    (ValuativeCriterion.Existence.specializingMap p hp)

end Langlands.AlgebraicGeometry
