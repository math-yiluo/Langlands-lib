import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.RationalParabolicModulusStatement
import Langlands.Representation.Induction.CompactQuotientDuality
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction

/-!
# Rational natural induction duality from quotient compactness and the modulus

This file reduces `RationalNaturalInductionDualityStatement` to two published
proof targets: compactness of the right-coset space of a dynamic parabolic
(`BruhatTits.DynamicParabolicQuotientCompactStatement`) and unimodularity of the
rational points together with the identification of the modular character of a
standard parabolic (`RationalParabolicModulusStatement`).
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

universe uG uV

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)

/-- For a unimodular group with `P \ G` compact, if the modular character of `P`
is the restricted Haar modulus of conjugation on `U`, then normalized induction
commutes naturally with the smooth contragredient on admissible objects. -/
theorem exists_natural_of_compactSpace (hU : IsClosed (U : Set G))
    (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
    [CompactSpace (Induction.LeftQuotient P)] [LocallyCompactSpace P]
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)) :
    ∃ E : ∀ (A : SmoothRep.{0, uG, uV} ℂ M), A.IsAdmissible →
        (((normalizedInductionFunctor h hU).obj A).contragredient ≅
          (normalizedInductionFunctor h hU).obj A.contragredient),
      ∀ (A B : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) (hB : B.IsAdmissible)
        (f : A ⟶ B),
        SmoothRep.contragredientHom ((normalizedInductionFunctor h hU).map f) ≫ (E A hA).hom =
          (E B hB).hom ≫ (normalizedInductionFunctor h hU).map (SmoothRep.contragredientHom f) := by
  obtain ⟨meas, hpos, hscalar⟩ := Induction.exists_compactQuotient_measure hG P hP
  have hsq : ∀ q : P,
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) *
        HaarModulus.closedHalfCharacter U hU P h.le_normalizer q =
      (((Measure.modularCharacter q : ℝ≥0) : ℝ) : ℂ) := by
    intro q
    rw [closedHalfCharacter_mul_self h hU q, hδ q]
  have hcofM := compactOpenCofinal_of_isClosed (h.isClosed_levi hP hm)
  apply exists_natural_of_isUniformIntegralDuality h hU ⊤ meas
  intro A hA
  obtain ⟨E, hE⟩ := Induction.exists_integralDualEquiv_of_pos P h.projection
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
    (fun q => Measure.modularCharacter q) ⊤ meas hm
    (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)
    hsq hcofM hpos hscalar A.representation A.isSmooth
    (smoothInduced_inducingRepresentation_isAdmissible h hU hm A hA)
  exact exists_functorEquiv_of_twistEquiv h hU ⊤ meas A E hE

end Generic

namespace RationalPointFamily

open _root_.AlgebraicGeometry GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Quotient compactness of dynamic parabolics and the modular-character
statement for standard parabolics imply natural same-parabolic induction
duality on the actual rational-point group. -/
theorem rationalNaturalInductionDuality_of_compact_of_modulus
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hmod : RationalParabolicModulusStatement.{u}) :
    RationalNaturalInductionDualityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi _ _ _ ν hν hStandard I hU hP hproj
  have := hG.isAffineHom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  obtain ⟨hunimod, hδ⟩ := hmod k G hG T i hi ν hν hStandard I hU hP hproj
  have : CompactSpace (Induction.LeftQuotient (parabolic i ν I)) :=
    compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν I
  have : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace
  borelize (RationalPoint k G.X)
  exact exists_natural_of_compactSpace _ hU hP hproj hunimod hδ

end RationalPointFamily

end Langlands.Aubert.General
