import Langlands.Geometry.FormalGroup.AtlasQuasiIsogenyHeight
import Langlands.Geometry.FormalGroup.SplitPrimalFramingHeight

/-! # The actual signed rank and component normalization of the split primal atlas -/

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

omit [Algebra ℤ_[prime] 𝒪[K]] in
private theorem height_reduction (Y : SpecialAtlas K D ι T.obj) (hh : Y.HasHeightSquared ϖ) :
    Y.reduction.HasHeightSquared ϖ :=
  Y.baseChangeAlong_height (Nilp.quotientO 𝒪[K] T) hh

/-- The signed central rank height of the actual primal framing on the reduced base. -/
def primalFramingRank : LocallyConstant (PrimeSpectrum (Reduced T)) ℤ :=
  let z := (primalAtlasFraming A hs hg h hpK).toAtlasQuasiIsogeny
  let hS := (primalFramingSourceAtlas_hasHeightSquared A hs hg h hFrame).2.2
  let hY := (height_reduction h.primalSpecialAtlas hTarget).2.2
  ⟨z.heightFunction hFrame.1 hS hY, z.isLocallyConstant_heightFunction hFrame.1 hS hY⟩

/-- The actual central test section has the measured rank pulled back from the reduced base. -/
theorem primalFramingRank_hasHeightOnChart (B : CommAlgCat.{0} (Reduced T))
    (b : h.primalSpecialAtlas.reduction.atlas.opens) (hb : IsUnit (algebraMap (Reduced T) B b.val)) :
    RationalSection.HasHeightFunction ϖ (Nat.card 𝓀[K])
      (RationalSection.ofGlobal ((primalAtlasFraming A hs hg h hpK).hom.onChart B b hb).val)
      (fun x => primalFramingRank A hs hg h hpK hFrame hTarget (x.val.comap (algebraMap (Reduced T) B))) :=
  (primalAtlasFraming A hs hg h hpK).toAtlasQuasiIsogeny.hasHeightFunction_onChart hFrame.1
    (primalFramingSourceAtlas_hasHeightSquared A hs hg h hFrame).2.2
    (height_reduction h.primalSpecialAtlas hTarget).2.2 B b hb

/-- A zero of the actual base rank on every prime is exactly the chart height-zero relation. -/
theorem primalFramingRank_zero_iff :
    (∀ x, primalFramingRank A hs hg h hpK hFrame hTarget x = 0) ↔
      (primalAtlasFraming A hs hg h hpK).hom.val.HasConstantChartHeight ϖ (Nat.card 𝓀[K]) 0 :=
  ((primalAtlasFraming A hs hg h hpK).toAtlasQuasiIsogeny.hasConstantChartHeight_iff hFrame.1
    (primalFramingSourceAtlas_hasHeightSquared A hs hg h hFrame).2.2
    (height_reduction h.primalSpecialAtlas hTarget).2.2 0).symm

/-- The projected local zero-height certificate gives zero of the computed base rank. -/
theorem primalFramingRank_zero_of_local {e : ℕ} {u : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (u : 𝒪[K]) * ϖ ^ e) (hz : HasPrimalChartHeightZero A h) :
    ∀ x, primalFramingRank A hs hg h hpK hFrame hTarget x = 0 :=
  (primalFramingRank_zero_iff A hs hg h hpK hFrame hTarget).mpr
    (primalAtlasFraming_height_zero A hs hg h hpK hp hFrame hz)

/-- The actual split Drinfeld triple when its computed primal rank vanishes. -/
def primalDrinfeldFramedAtlasOfRankZero (hκ : IsField kW)
    (hz : ∀ x, primalFramingRank A hs hg h hpK hFrame hTarget x = 0) :
    letI : Field kW := hκ.toField
    DrinfeldFramedAtlas ⟨primalSpecialFrame A hs h.1 hg, hFrame⟩ T :=
  primalDrinfeldFramedAtlas A hs hg h hpK hκ hFrame hTarget
    ((primalFramingRank_zero_iff A hs hg h hpK hFrame hTarget).mp hz)

/-- Where the central primal rank is divisible by the division degree, its negative
exact quotient is the first split component coordinate. -/
def primalComponentOrder
    (hdiv : ∀ x, (d : ℤ) ∣ primalFramingRank A hs hg h hpK hFrame hTarget x) :
    {n : LocallyConstant (PrimeSpectrum (Reduced T)) ℤ //
      ∀ x, -(n x) * (d : ℤ) = primalFramingRank A hs hg h hpK hFrame hTarget x} := by
  let k := primalFramingRank A hs hg h hpK hFrame hTarget
  refine ⟨⟨(fun v : ℤ => -(v / (d : ℤ))) ∘ k, k.isLocallyConstant.comp _⟩, fun x => ?_⟩
  change -(-(k x / (d : ℤ))) * (d : ℤ) = k x
  rw [neg_neg, Int.ediv_mul_cancel (hdiv x)]

/-- The exact rank relation uniquely determines the projected component index. -/
theorem primalComponentOrder_eq
    (hdiv : ∀ x, (d : ℤ) ∣ primalFramingRank A hs hg h hpK hFrame hTarget x)
    (n : LocallyConstant (PrimeSpectrum (Reduced T)) ℤ)
    (hn : ∀ x, -(n x) * (d : ℤ) = primalFramingRank A hs hg h hpK hFrame hTarget x) :
    (primalComponentOrder A hs hg h hpK hFrame hTarget hdiv).val = n := by
  ext x
  have hpos : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (CentralSimple.reducedDegree_pos K D).ne'
  have hmul := ((primalComponentOrder A hs hg h hpK hFrame hTarget hdiv).property x).trans (hn x).symm
  exact neg_injective (mul_right_cancel₀ hpos hmul)

/-- The first component vanishes exactly when the actual primal rank vanishes. -/
theorem primalComponentOrder_zero_iff
    (hdiv : ∀ x, (d : ℤ) ∣ primalFramingRank A hs hg h hpK hFrame hTarget x) :
    (∀ x, (primalComponentOrder A hs hg h hpK hFrame hTarget hdiv).val x = 0) ↔
      ∀ x, primalFramingRank A hs hg h hpK hFrame hTarget x = 0 := by
  constructor
  · intro hz x
    have h := (primalComponentOrder A hs hg h hpK hFrame hTarget hdiv).property x
    rw [hz x, neg_zero, zero_mul] at h
    exact h.symm
  · intro hz x
    change -(primalFramingRank A hs hg h hpK hFrame hTarget x / (d : ℤ)) = 0
    rw [hz x, Int.zero_ediv, neg_zero]

end Langlands.FormalGroup.Harris
