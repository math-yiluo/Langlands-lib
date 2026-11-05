import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map

/-! # Actual projective arithmetic models and generic fibers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The existing polynomial-Proj projective space as a relative scheme. -/
def projectivePointScheme (R : Type u) [CommRing R] (n : ℕ) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Langlands.AlgebraicGeometry.projectiveSpaceToSpec R n)

instance (R : Type u) [CommRing R] (n : ℕ) :
    IsProper (projectivePointScheme R n).hom :=
  Langlands.AlgebraicGeometry.projectiveSpaceToSpec_isProper R n

/-- Polynomial projective space commutes with the actual spectrum base change. -/
def projectivePointSchemeBaseChangeIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) :
    ringBaseChange R A (projectivePointScheme R n) ≅ projectivePointScheme A n := by
  have h : IsPullback (ProjSpace.map R A n)
      (Langlands.AlgebraicGeometry.projectiveSpaceToSpec A n)
      (Langlands.AlgebraicGeometry.projectiveSpaceToSpec R n) (Spec.algebraMap R A) :=
    ProjSpace.isPullback_map R A n
  exact Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F)) (n : ℕ)

/-- The supplied outside-S integer model is actual projective space over that ring. -/
abbrev curvePlaceProjectiveModel := projectivePointScheme (curvePlaceSIntegers k F S) n

/-- Its generic fiber is identified with actual projective space over F. -/
def curvePlaceProjectiveGenericFiberIso :
    curvePlaceModelGenericFiber k F S (curvePlaceProjectiveModel k F S n) ≅
      projectivePointScheme F n := by
  let : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  exact projectivePointSchemeBaseChangeIso (curvePlaceSIntegers k F S) F n

variable [PerfectField k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FunctionField k F]

/-- The concrete arithmetic projective model specifies the adelic point topology. -/
@[instance_reducible]
def curvePlaceProjectiveAdelePointTopology :
    TopologicalSpace (CurvePlaceAdelePoints k F (projectivePointScheme F n)) :=
  curvePlaceSpreadAdelePointTopology k F S (curvePlaceProjectiveModel k F S n)
    (projectivePointScheme F n) (curvePlaceProjectiveGenericFiberIso k F S n)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K)) (n : ℕ)

/-- The full number-field projective model over the original outside-S integers. -/
abbrev numberFieldProjectiveModel :=
  projectivePointScheme ((S : Set (FinitePlace K)).integer K) n

/-- The specified generic-fiber map comes from the actual projective base change. -/
def numberFieldProjectiveGenericFiberIso :
    numberFieldModelGenericFiber K S (numberFieldProjectiveModel K S n) ≅
      projectivePointScheme K n := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  exact projectivePointSchemeBaseChangeIso ((S : Set (FinitePlace K)).integer K) K n

/-- The concrete model topology includes the arithmetic stages' infinite factors. -/
@[instance_reducible]
def numberFieldProjectiveAdelePointTopology :
    TopologicalSpace (NumberFieldAdelePoints K (projectivePointScheme K n)) :=
  numberFieldSpreadAdelePointTopology K S (numberFieldProjectiveModel K S n)
    (projectivePointScheme K n) (numberFieldProjectiveGenericFiberIso K S n)

end NumberField

end Langlands.Global
