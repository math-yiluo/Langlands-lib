import Langlands.Global.AdelicAmbientWavePacketProfileStatement

/-! # The quotient-product pairing for wave-packet lifts -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints RestrictionSplitCentre

/-- Tensor a function on `[G]` with the ambient profile, using the actual quotient product. -/
def ambientProfileQuotientLift {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) {m : ℕ}
    (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ)
    (f : CanonicalQuotient F G → ℂ) (q : RationalQuotient F G) : ℂ :=
  let z := principalQuotientProductEquiv F G hG q
  ambientWavePacketProfile eG b z.1.val * f z.2

/-- The same nonzero ambient coefficient lifts every relative quotient function. On
representatives this is the pointwise wave-packet lift. It preserves and reflects `L²`,
and scales the pairing by the strictly positive square integral on `A_G`. -/
def WavePacketProductPairingStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {m : ℕ} (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ),
    ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → b ≠ 0 →
    let ν := canonicalMeasure F G
    let fullMeasure := rationalQuotientHaarMeasure F G
    let c := ∫ a : canonicalSubgroup F G, ‖ambientWavePacketProfile eG b a.val‖ ^ 2
      ∂(positiveCentreHaarMeasure F G hG)
    0 < c ∧
    (∀ (f : CanonicalQuotient F G → ℂ) (g : AdelicGroupPoints F G),
      ambientProfileQuotientLift hG eG b f (LeftCosetSpace.mk (rationalSubgroup F G) g) =
        ambientWavePacketProfile eG b g * f (LeftCosetSpace.mk (canonicalRationalSubgroup F G) g)) ∧
    (∀ f : CanonicalQuotient F G → ℂ,
      (MemLp (ambientProfileQuotientLift hG eG b f) 2 fullMeasure ↔ MemLp f 2 ν)) ∧
    (∀ f g : CanonicalQuotient F G → ℂ, MemLp f 2 ν → MemLp g 2 ν →
      (∫ q, ambientProfileQuotientLift hG eG b f q *
        (starRingEnd ℂ) (ambientProfileQuotientLift hG eG b g q) ∂fullMeasure) =
      (c : ℂ) * ∫ q, f q * (starRingEnd ℂ) (g q) ∂ν)

end Langlands.Global
