import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentGluingStatement
import Langlands.Geometry.Analytic.StrictTestDomain.TrivialScalarRationalLocalizationProof

/-! # The actual binary Laurent amalgam over trivially normed scalars -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Localization at the upper denominator `1` makes the actual upper base
map bijective when all scalar norms are at most one. -/
theorem laurentUpper_baseMap_bijective_of_trivialScalar
    (hK : ∀ c : K, ‖c‖ ≤ 1) (f : P) :
    Function.Bijective (laurentUpper f).baseMap := by
  let : Algebra P (laurentUpper f).algebra :=
    (laurentUpper f).baseMap.toAlgHom.toRingHom.toAlgebra
  let : IsLocalization.Away (1 : P) (laurentUpper f).algebra :=
    trivialScalarRationalLocalization K P hK (laurentUpper f)
  exact (IsLocalization.atUnits P (Submonoid.powers (1 : P))
    (S := (laurentUpper f).algebra)
    (Submonoid.powers_le.mpr (by exact isUnit_one))).bijective

/-- The actual lower-to-overlap restriction is bijective over trivially
normed scalars: both objects localize the base at powers of `f`. -/
theorem laurentLower_interRight_bijective_of_trivialScalar
    (hK : ∀ c : K, ‖c‖ ≤ 1) (f : P) :
    Function.Bijective (interRight (laurentUpper f) (laurentLower f)).restriction := by
  let : Algebra P (laurentLower f).algebra :=
    (laurentLower f).baseMap.toAlgHom.toRingHom.toAlgebra
  let : Algebra P ((laurentUpper f).inter (laurentLower f)).algebra :=
    ((laurentUpper f).inter (laurentLower f)).baseMap.toAlgHom.toRingHom.toAlgebra
  let : IsLocalization.Away f (laurentLower f).algebra :=
    trivialScalarRationalLocalization K P hK (laurentLower f)
  let : IsLocalization.Away f ((laurentUpper f).inter (laurentLower f)).algebra := by
    simpa only [inter, laurentUpper_denominator, laurentLower_denominator, one_mul] using
      trivialScalarRationalLocalization K P hK
        ((laurentUpper f).inter (laurentLower f))
  apply IsLocalization.bijective (Submonoid.powers f)
    (interRight (laurentUpper f) (laurentLower f)).restriction.toAlgHom.toRingHom
  exact congrArg (fun φ => φ.toAlgHom.toRingHom)
    (interRight (laurentUpper f) (laurentLower f)).restriction_comp_baseMap

/-- The unique base element determined by an upper Laurent section over
trivially normed scalars. -/
def trivialScalarLaurentAmalgam
    (hK : ∀ c : K, ‖c‖ ≤ 1) (f : P) (sUpper : (laurentUpper f).algebra) : P :=
  (laurentUpper_baseMap_bijective_of_trivialScalar hK f).surjective sUpper |>.choose

@[simp]
theorem laurentUpper_baseMap_trivialScalarLaurentAmalgam
    (hK : ∀ c : K, ‖c‖ ≤ 1) (f : P) (sUpper : (laurentUpper f).algebra) :
    (laurentUpper f).baseMap (trivialScalarLaurentAmalgam hK f sUpper) = sUpper :=
  (laurentUpper_baseMap_bijective_of_trivialScalar hK f).surjective sUpper |>.choose_spec

/-- Compatibility under the actual restrictions forces the constructed
amalgam to have the specified lower section. -/
theorem laurentLower_baseMap_trivialScalarLaurentAmalgam
    (hK : ∀ c : K, ‖c‖ ≤ 1) (f : P)
    (sUpper : (laurentUpper f).algebra) (sLower : (laurentLower f).algebra)
    (h : (interLeft (laurentUpper f) (laurentLower f)).restriction sUpper =
      (interRight (laurentUpper f) (laurentLower f)).restriction sLower) :
    (laurentLower f).baseMap (trivialScalarLaurentAmalgam hK f sUpper) = sLower := by
  apply (laurentLower_interRight_bijective_of_trivialScalar hK f).injective
  calc
    _ = ((laurentUpper f).inter (laurentLower f)).baseMap
        (trivialScalarLaurentAmalgam hK f sUpper) :=
      congrArg (fun φ : BoundedAlgHom K P _ =>
        φ (trivialScalarLaurentAmalgam hK f sUpper))
        (interRight (laurentUpper f) (laurentLower f)).restriction_comp_baseMap
    _ = (interLeft (laurentUpper f) (laurentLower f)).restriction
        ((laurentUpper f).baseMap (trivialScalarLaurentAmalgam hK f sUpper)) :=
      (congrArg (fun φ : BoundedAlgHom K P _ =>
        φ (trivialScalarLaurentAmalgam hK f sUpper))
        (interLeft (laurentUpper f) (laurentLower f)).restriction_comp_baseMap).symm
    _ = (interRight (laurentUpper f) (laurentLower f)).restriction sLower := by
      rw [laurentUpper_baseMap_trivialScalarLaurentAmalgam, h]

/-- Scalar degree-zero binary Laurent descent over trivially normed
scalars, using the existing quotient carriers and restrictions. -/
theorem binaryLaurentGluing_of_trivialScalar
    (hK : ∀ c : K, ‖c‖ ≤ 1) (f : P)
    (sUpper : (laurentUpper f).algebra) (sLower : (laurentLower f).algebra)
    (h : (interLeft (laurentUpper f) (laurentLower f)).restriction sUpper =
      (interRight (laurentUpper f) (laurentLower f)).restriction sLower) :
    ∃! a : P, (laurentUpper f).baseMap a = sUpper ∧
      (laurentLower f).baseMap a = sLower := by
  refine ⟨trivialScalarLaurentAmalgam hK f sUpper, ⟨?_, ?_⟩, ?_⟩
  · exact laurentUpper_baseMap_trivialScalarLaurentAmalgam hK f sUpper
  · exact laurentLower_baseMap_trivialScalarLaurentAmalgam hK f sUpper sLower h
  · intro b hb
    apply (laurentUpper_baseMap_bijective_of_trivialScalar hK f).injective
    exact hb.1.trans (laurentUpper_baseMap_trivialScalarLaurentAmalgam hK f sUpper).symm

end Langlands.Analytic.StrictTestDomain
