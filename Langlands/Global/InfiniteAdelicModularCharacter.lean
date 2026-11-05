import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.Analysis.Local.ProductModularCharacter

/-! # Modular character of the actual infinite adelic point group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left]

namespace InfinitePlaceGroupPoints

/-- The actual completion-valued point group retains its continuous group law. -/
instance isTopologicalGroup (w : InfinitePlace F) :
    IsTopologicalGroup (InfinitePlaceGroupPoints F G w) :=
  G.affinePointsIsTopologicalGroup (CommAlgCat.of F w.Completion)

instance t2Space (w : InfinitePlace F) :
    T2Space (InfinitePlaceGroupPoints F G w) :=
  G.affinePointsT2Space (CommAlgCat.of F w.Completion)

/-- Finite-type points over an actual infinite completion are locally compact. -/
instance locallyCompactSpace [LocallyOfFiniteType G.X.hom] (w : InfinitePlace F) :
    LocallyCompactSpace (InfinitePlaceGroupPoints F G w) :=
  G.affinePointsLocallyCompactSpace (CommAlgCat.of F w.Completion)

end InfinitePlaceGroupPoints

namespace InfiniteAdelicGroupPoints

variable [LocallyOfFiniteType G.X.hom]

/-- The intrinsic modular character of actual infinite adelic points is the
product of the intrinsic modular characters at the actual infinite places. -/
theorem modularCharacter_eq_prod (g : InfiniteAdelicGroupPoints F G) :
    Measure.modularCharacter g =
      ∏ w : InfinitePlace F, Measure.modularCharacter (atPlace F G w g) := by
  calc
    Measure.modularCharacter g =
        Measure.modularCharacter (completions F G g) :=
      (Langlands.Aubert.General.modularCharacter_continuousMulEquiv
        (completions F G) g).symm
    _ = ∏ w : InfinitePlace F, Measure.modularCharacter (atPlace F G w g) :=
      Langlands.ProductMeasure.modularCharacter_pi (completions F G g)

/-- The product of actual archimedean modular values as a homomorphism on the
original infinite adelic point group. -/
def localModularProduct : InfiniteAdelicGroupPoints F G →* ℝ≥0 where
  toFun g := ∏ w : InfinitePlace F, Measure.modularCharacter (atPlace F G w g)
  map_one' := by simp
  map_mul' g h := by simp [map_mul, Finset.prod_mul_distrib]

@[simp] theorem localModularProduct_apply (g : InfiniteAdelicGroupPoints F G) :
    localModularProduct F G g = Measure.modularCharacter g :=
  (modularCharacter_eq_prod F G g).symm

/-- The Borel sigma algebra of the existing infinite adelic point topology. -/
instance measurableSpace : MeasurableSpace (InfiniteAdelicGroupPoints F G) :=
  borel (InfiniteAdelicGroupPoints F G)

instance borelSpace : BorelSpace (InfiniteAdelicGroupPoints F G) := ⟨rfl⟩

/-- Positive right translation of fixed infinite-adelic Haar has the product
of the actual archimedean modular values as its scalar. -/
theorem map_mul_right_haar_eq_prod (g : InfiniteAdelicGroupPoints F G) :
    Measure.map (fun x => x * g)
        (Measure.haar : Measure (InfiniteAdelicGroupPoints F G)) =
      (∏ w : InfinitePlace F, Measure.modularCharacter (atPlace F G w g)) •
        (Measure.haar : Measure (InfiniteAdelicGroupPoints F G)) := by
  rw [Langlands.Induction.map_mul_right_haar_eq, modularCharacter_eq_prod F G]

end InfiniteAdelicGroupPoints

end Langlands.Global
