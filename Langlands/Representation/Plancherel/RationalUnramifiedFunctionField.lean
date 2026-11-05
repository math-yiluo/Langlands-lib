import Langlands.Representation.Plancherel.RationalUnramifiedCoordinateAlgebra
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The scalar ring and fraction field of actual unramified families

The published finite Laurent description gives finite generation, Noetherianity
and the domain property for the actual evaluation-generated scalar algebra.
Its fraction field therefore has a faithful scalar embedding.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

include hp hG

/-- The actual regular scalar algebra is finitely generated over `ℂ`. -/
theorem rationalUnramifiedRegularFunctions_finiteType :
    Algebra.FiniteType ℂ
      (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) := by
  have : AddMonoid.FG (Fin (rationalImageRank G) → ℤ) := by infer_instance
  exact (inferInstance : Algebra.FiniteType ℂ
    (AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ))).equiv
      (rationalUnramifiedLaurentAlgebraEquiv G hp hG)

/-- The actual regular scalar algebra is Noetherian. -/
theorem rationalUnramifiedRegularFunctions_isNoetherianRing :
    IsNoetherianRing
      (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) := by
  let := rationalUnramifiedRegularFunctions_finiteType G hp hG
  exact Algebra.FiniteType.isNoetherianRing ℂ _

/-- Finite Laurent coordinates also prove that the actual scalar ring is a
domain; being a subalgebra of all functions alone would not suffice. -/
theorem rationalUnramifiedRegularFunctions_isDomain :
    IsDomain
      (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) := by
  exact (rationalUnramifiedLaurentAlgebraEquiv G hp hG).symm.toMulEquiv.isDomain _

/-- Fractions of the actual regular functions. The displayed reductivity and
continuity data provide the domain instance used by the field structure. -/
def rationalUnramifiedFunctionField
    (hp : Continuous (rationalValuationImageProjection G))
    (hG : GroupScheme.IsConnectedReductive G) :=
  let := rationalUnramifiedRegularFunctions_isDomain G hp hG
  FractionRing (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))

instance rationalUnramifiedFunctionField_field :
    Field (rationalUnramifiedFunctionField G hp hG) := by
  letI := rationalUnramifiedRegularFunctions_isDomain G hp hG
  exact inferInstanceAs (Field (FractionRing
    (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))))

instance rationalUnramifiedFunctionField_algebra :
    Algebra (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
      (rationalUnramifiedFunctionField G hp hG) :=
  inferInstanceAs (Algebra
    (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (FractionRing (unramifiedRegularFunctions
      (fun ψ => (rationalNormCharacters G ψ).toMul))))

instance rationalUnramifiedFunctionField_isFractionRing :
    IsFractionRing
      (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
      (rationalUnramifiedFunctionField G hp hG) :=
  inferInstanceAs (IsFractionRing
    (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (FractionRing (unramifiedRegularFunctions
      (fun ψ => (rationalNormCharacters G ψ).toMul))))

/-- Regular functions embed faithfully into their fraction field. -/
theorem rationalUnramifiedFunctionField_algebraMap_injective :
    Function.Injective
      (algebraMap
        (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG)) := by
  let := rationalUnramifiedRegularFunctions_isDomain G hp hG
  exact IsFractionRing.injective _ _

end Langlands.Plancherel
