import Langlands.Geometry.FormalGroup.SpecialRationalHeightDivisibility
import Langlands.Geometry.FormalGroup.SplitPrimalFramingRank

/-! # The first split component of the actual primal rigidifier -/

noncomputable section

universe s

namespace Langlands.FormalGroup.Harris

open CategoryTheory TopologicalSpace ValuativeRel LocalDivision ModuleLaw PolarizedFramedAffinePoint

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
attribute [local instance] primalDivisionPadicAlgebra

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Algebra ℤ_[prime] 𝒪[K]]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable {ϖ : 𝒪[K]} {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}

local notation "πW" => algebraMap 𝒪[K] W ϖ
local notation "kW" => ResidueRing W πW
local notation "d" => CentralSimple.reducedDegree K D

private abbrev Reduced (T : Nilp.{0, 0} W πW) := ((Nilp.reductionFunctor W πW).obj T).obj

private abbrev FrameImage (frame : SplitPolarizedFrame prime K D W ϖ)
    (M : ModuleLaw ℤ_[prime] kW (Fin (CentralSimple.reducedDegree K D))) :=
  ModuleLaw.OrderAction.DivisionImage (O := ℤ_[prime]) (B := IntegerRing K D)
    (R := kW) (σ := Fin frame.dimension) (τ := Fin (CentralSimple.reducedDegree K D))
    (M := frame.law) frame.order M

variable {M : ModuleLaw ℤ_[prime] (ResidueRing W (algebraMap 𝒪[K] W ϖ))
  (Fin (CentralSimple.reducedDegree K D))}
variable (A : FrameImage frame M)
variable (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
  (algebraMap 𝒪[K] (ResidueRing W (algebraMap 𝒪[K] W ϖ))))
variable (hg : frame.order.HasGeometricDivisionTangentCharacters.{0, 0, 0, 0, s}
  (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D))
variable (h : HasSplitSpecialTangent ι X)

variable (hpK : (prime : K) ≠ 0)
variable (hFrame : (primalSpecialFrame A hs h.1 hg).HasHeightSquared ϖ)
variable (hTarget : h.primalSpecialAtlas.HasHeightSquared ϖ)

/-- The actual primal rank has the special-atlas division-degree divisibility. -/
theorem primalFramingRank_dvd (x : PrimeSpectrum (Reduced T)) :
    (d : ℤ) ∣ primalFramingRank A hs hg h hpK hFrame hTarget x :=
  SpecialAtlas.dvd_heightFunction
    (X := primalFramingSourceAtlas A hs hg h) (Y := h.primalSpecialAtlas.reduction)
    (primalAtlasFraming A hs hg h hpK)
    (primalFramingSourceAtlas_hasHeightSquared A hs hg h hFrame)
    (h.primalSpecialAtlas.baseChangeAlong_height (Nilp.quotientO 𝒪[K] T) hTarget) x

/-- The first split component is the negative, division-degree-normalized height
of the actual projected primal framing. -/
def primalComponentIndex : LocallyConstant (PrimeSpectrum (Reduced T)) ℤ :=
  (primalComponentOrder A hs hg h hpK hFrame hTarget
    (primalFramingRank_dvd A hs hg h hpK hFrame hTarget)).val

/-- Multiplying the negative index by the division degree recovers the original rank height. -/
theorem primalComponentIndex_rank (x : PrimeSpectrum (Reduced T)) :
    -(primalComponentIndex A hs hg h hpK hFrame hTarget x) * (d : ℤ) =
      primalFramingRank A hs hg h hpK hFrame hTarget x :=
  (primalComponentOrder A hs hg h hpK hFrame hTarget
    (primalFramingRank_dvd A hs hg h hpK hFrame hTarget)).property x

/-- The exact division-degree relation determines the first component uniquely. -/
theorem primalComponentIndex_eq (n : LocallyConstant (PrimeSpectrum (Reduced T)) ℤ)
    (hn : ∀ x, -(n x) * (d : ℤ) = primalFramingRank A hs hg h hpK hFrame hTarget x) :
    primalComponentIndex A hs hg h hpK hFrame hTarget = n :=
  primalComponentOrder_eq A hs hg h hpK hFrame hTarget
    (primalFramingRank_dvd A hs hg h hpK hFrame hTarget) n hn

/-- The first component is zero on the whole base exactly when the primal atlas
rigidifier has the actual chart-height-zero certificate. -/
theorem primalComponentIndex_zero_iff :
    (∀ x, primalComponentIndex A hs hg h hpK hFrame hTarget x = 0) ↔
      (primalAtlasFraming A hs hg h hpK).hom.val.HasConstantChartHeight ϖ (Nat.card 𝓀[K]) 0 :=
  (primalComponentOrder_zero_iff A hs hg h hpK hFrame hTarget
    (primalFramingRank_dvd A hs hg h hpK hFrame hTarget)).trans
      (primalFramingRank_zero_iff A hs hg h hpK hFrame hTarget)

/-- The zero first component produces the actual Drinfeld triple on the affine base. -/
def primalDrinfeldFramedAtlasOfIndexZero (hκ : IsField kW)
    (hz : ∀ x, primalComponentIndex A hs hg h hpK hFrame hTarget x = 0) :
    letI : Field kW := hκ.toField
    DrinfeldFramedAtlas ⟨primalSpecialFrame A hs h.1 hg, hFrame⟩ T :=
  primalDrinfeldFramedAtlas A hs hg h hpK hκ hFrame hTarget
    ((primalComponentIndex_zero_iff A hs hg h hpK hFrame hTarget).mp hz)

end Langlands.FormalGroup.Harris
