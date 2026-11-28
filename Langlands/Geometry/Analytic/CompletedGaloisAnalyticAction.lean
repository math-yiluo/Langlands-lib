import Langlands.Geometry.Analytic.CompletedGaloisCoefficientAction
import Langlands.Geometry.Analytic.GroundFieldExtensionSemilinearPoints

/-! # The absolute Galois action on the actual completed scalar extension -/

noncomputable section

open CategoryTheory
open Langlands.GaloisRepresentation.HodgeTate
open Langlands.Analytic.CompletedGaloisCoefficientAction
open Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v

namespace Langlands.Analytic.SpaceOverField

open CompleteUltrametricField

variable (p : ℕ) [Fact p.Prime] (F : Type u)
  [NormedField F] [NormedAlgebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [IsUltrametricDist F] [CompleteSpace F]

/-- The isometric ground field arrow into the actual completed algebraic closure. -/
def completedFieldEmbedding : of F ⟶ of (Completed p F) :=
  ⟨algebraMap F (Completed p F), norm_algebraMap_completed p F⟩

private theorem embedding_normedAlgebra :
    (completedFieldEmbedding p F).normedAlgebra = completedNormedAlgebra p F := by
  have hinj : Function.Injective (fun A : NormedAlgebra F (Completed p F) => A.toAlgebra) := by
    intro A B h
    cases A
    cases B
    cases h
    rfl
  exact hinj (Algebra.algebra_ext _ _ fun _ => rfl)

private def coefficientActionOfNormedAlgebra (A : NormedAlgebra F (Completed p F))
    (h : A = completedNormedAlgebra p F) :
    letI := A
    Field.absoluteGaloisGroup F →* isometricAutomorphisms F (Completed p F) :=
  h.symm ▸ galoisCoefficientAction p F

omit [IsUltrametricDist F] [CompleteSpace F] in
private theorem continuous_coefficientActionOfNormedAlgebra (A : NormedAlgebra F (Completed p F))
    (h : A = completedNormedAlgebra p F) (c : Completed p F) :
    Continuous (fun σ : Field.absoluteGaloisGroup F =>
      (coefficientActionOfNormedAlgebra p F A h σ).val c) := by
  subst A
  exact continuous_galoisCoefficientOrbit p F c

private abbrev completedCoefficientAction : Field.absoluteGaloisGroup F →*
    CoefficientAutomorphisms (completedFieldEmbedding p F) :=
  coefficientActionOfNormedAlgebra p F (completedFieldEmbedding p F).normedAlgebra
    (embedding_normedAlgebra p F)

variable (X : (of F).CompatibleAnalyticCategory.{u, v})

/-- The analytic scalar extension formed along the actual completed field embedding. -/
abbrev completedScalarExtension : SpaceOverField.{u, v} :=
  scalarExtendedSpace (completedFieldEmbedding p F) X

/-- The absolute Galois group acts by the actual Cartesian lifts of the inverse
coefficient automorphisms. -/
def completedGaloisAnalyticAction : Field.absoluteGaloisGroup F →*
    Aut (completedScalarExtension p F X) :=
  (coefficientAnalyticAction (completedFieldEmbedding p F) X).comp (completedCoefficientAction p F)

/-- The projection to the original analytic space is invariant under the
absolute Galois action on the scalar extension. -/
theorem completedGaloisAnalyticAction_comp_projection (σ : Field.absoluteGaloisGroup F) :
    (completedGaloisAnalyticAction p F X σ).asIso.hom ≫
        scalarExtensionArrow (withField (of F) X) (completedFieldEmbedding p F) =
      scalarExtensionArrow (withField (of F) X) (completedFieldEmbedding p F) :=
  coefficientLift_comp_projection _ _ (completedCoefficientAction p F σ)

/-- The action of the Krull group on the underlying analytic points is jointly continuous. -/
theorem continuous_completedGaloisPointAction :
    Continuous (fun z : Field.absoluteGaloisGroup F × underlyingSpaceFunctor.obj
        (completedScalarExtension p F X) =>
      underlyingMap ((completedGaloisAnalyticAction p F X z.1).asIso.hom) z.2) :=
  continuous_underlyingCoefficientAction (completedFieldEmbedding p F) X
    (completedCoefficientAction p F) (continuous_coefficientActionOfNormedAlgebra p F
      (completedFieldEmbedding p F).normedAlgebra (embedding_normedAlgebra p F))

end Langlands.Analytic.SpaceOverField
