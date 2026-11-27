import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Uniform rapid decay of norm-one partial convolutions of cuspidal `L²` classes -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

/-- Uniform rapid decay of norm-one partial convolutions. -/
def NormOnePartialConvolutionRapidDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom H.X.hom] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    (hH : IsConnectedReductive H)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]
    {N : ℕ} (rho : MatrixRepresentation H (Fin N)), 0 < N → IsClosedSubgroup rho →
    ∀ (K : AdelicGroupPoints F H → ℂ), IsAdelicTestFunction F H K →
    ∀ (B : Set (AdelicGroupPoints F H)), IsCompact B → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : normOneSubgroup F H, ∃ q : RationalGroupPoints F H,
        ∀ h ∈ fullAEL2CuspidalSubmodule F H parabolicDynamic hH T i hi I e hc, ∀ b ∈ B,
          ‖∫ n : normOneSubgroup F H,
              starRingEnd ℂ (K ((n : AdelicGroupPoints F H)⁻¹ *
                (rational F H q * (x : AdelicGroupPoints F H) * b))) *
              (h : PositiveRationalQuotient F H T i → ℂ)
                (LeftCosetSpace.mk (positiveRationalSubgroup F H T i) n.val) ∂Measure.haar‖ *
            adelicHeight F H rho (rational F H q * (x : AdelicGroupPoints F H)) ^ m ≤ C * ‖h‖

end Langlands.Global
