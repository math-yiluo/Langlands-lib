import Langlands.Global.AdelicWavePacketAmbientLiftStatement
import Langlands.Global.AdelicPrincipalQuotientProduct

/-! # Square integrability of the ambient spectral profile -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints RestrictionSplitCentre

/-- A smooth compactly supported ambient coefficient gives a continuous profile, square-integrable
on the actual positive split centre with the quotient-product normalization. If the coefficient is
not identically zero, the square integral is strictly positive. -/
def AmbientWavePacketProfileStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {m : ℕ} (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ),
    ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
    Continuous (ambientWavePacketProfile eG b) ∧
    MemLp (fun a : canonicalSubgroup F G => ambientWavePacketProfile eG b a.val) 2
      (positiveCentreHaarMeasure F G hG) ∧
    (b ≠ 0 → 0 < ∫ a : canonicalSubgroup F G, ‖ambientWavePacketProfile eG b a.val‖ ^ 2
      ∂(positiveCentreHaarMeasure F G hG))

end Langlands.Global
