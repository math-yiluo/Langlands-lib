import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Weyl integration on the regular elliptic set of `GL_n` modulo the center -/

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

/-- The Weyl integration formula on the regular elliptic set of `GL_n(F)` modulo its center `Z`,
in disintegrated form. There is a Borel measure `ν` on `G / Z`, carried by the image `E` of the
regular elliptic set, such that for every Haar measure `μ` on `G / Z` the integral over `E` of a
function `Φ` that is integrable on `E` is the `ν`-integral of its orbital integrals
`x ↦ ∫_{G/Z} Φ(g x g⁻¹) dμ(g)`, which are defined `ν`-almost everywhere and `ν`-integrable. Clozel's measure
`ν = ∑_T |W(G,T)|⁻¹ |D(t)| dt` (elliptic tori `T` up to conjugacy, `dt` the Haar probability
measure of `T / Z`) has this property. -/
def EllipticWeylIntegrationStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    let G := GeneralLinear n F
    let Z := Subgroup.center G
    letI := centralQuotientMeasurableSpace F n
    let E : Set (G ⧸ Z) := QuotientGroup.mk '' {g : G | IsRegularElliptic g}
    ∃ ν : Measure (G ⧸ Z), ν Eᶜ = 0 ∧
      ∀ (μ : Measure (G ⧸ Z)) [μ.IsHaarMeasure] (Φ : G ⧸ Z → ℂ), IntegrableOn Φ E μ →
        (∀ᵐ x ∂ν, Integrable (fun g => Φ (g * x * g⁻¹)) μ) ∧
        Integrable (fun x => (∫ g, Φ (g * x * g⁻¹) ∂μ)) ν ∧
        (∫ q in E, Φ q ∂μ) = ∫ x, (∫ g, Φ (g * x * g⁻¹) ∂μ) ∂ν

end Langlands.BaseChange
