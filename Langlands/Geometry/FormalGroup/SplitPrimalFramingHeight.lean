import Langlands.Geometry.FormalGroup.AtlasOrderRationalHeightIso
import Langlands.Geometry.FormalGroup.PrimalAtlasCentralChart
import Langlands.Geometry.FormalGroup.RamifiedPrimalAtlasHeight
import Langlands.Geometry.FormalGroup.SplitPrimalDrinfeldFrame

/-! # Height-zero split primal rigidifiers and their Drinfeld triples -/

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

/-- The genuine chartwise prime-normalized zero-height condition on the projected
polarized rigidifier. The numerator and scalar denominator are measured on the
actual division summands of the two test laws. -/
def HasPrimalChartHeightZero : Prop :=
  let J := reducedPrimalImageCover h
  let A₀ := A.map (frameCoefficientMap prime πW T)
  let I : IdempotentImageCover (source (frame := frame) (T := T)).order.divisionProjector (Fin d) :=
    IdempotentImageCover.ofGlobalImageCover A₀ J.atlas.opens J.atlas.covers
  ∀ (B : CommAlgCat.{0} (Reduced T)) (c : J.atlas.opens)
    (hc : IsUnit (algebraMap (Reduced T) B c.val)),
    RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime
      (I.restrictLocalQuasiIsogenyOnChart J (h := rfl) B c hc X.localFraming X.commutes
        PadicInt.irreducible_p).val (fun _ => 0)

/-- The actual source atlas has the scalar-kernel heights of the base-changed fixed frame. -/
theorem primalFramingSourceAtlas_hasHeightSquared
    (hFrame : (primalSpecialFrame A hs h.1 hg).HasHeightSquared ϖ) :
    (primalFramingSourceAtlas A hs hg h).HasHeightSquared ϖ :=
  SpecialAtlas.ofGlobalCover_height _ (hFrame.map (primalResidueMap T)) _ _

private theorem transportedPrimalChartHeightZero
    (I : IdempotentImageCover (source (frame := frame) (T := T)).order.divisionProjector (Fin d))
    (J : IdempotentImageCover X.reducedTarget.order.divisionProjector (Fin d))
    {hj : I.atlas.opens = J.atlas.opens}
    (hsI : (source (frame := frame) (T := T)).order.HasStructuralDivisionTangent
      (algebraMap 𝒪[K] (IntegerRing K D)) (algebraMap 𝒪[K] (Reduced T)))
    (hsJ : X.reducedTarget.order.HasStructuralDivisionTangent
      (algebraMap 𝒪[K] (IntegerRing K D)) (algebraMap 𝒪[K] (Reduced T)))
    {S Q : SpecialAtlas K D ι (Reduced T)}
    {ha : I.atlas.opens = S.atlas.opens} {hb : J.atlas.opens = Q.atlas.opens}
    (a : BasicAtlas.OrderAction.Iso
      ((I.divisionOrder _).centralAtlasOrder (I.divisionOrder_centralTangent hsI)) S.order ha)
    (b : BasicAtlas.OrderAction.Iso
      ((J.divisionOrder _).centralAtlasOrder (J.divisionOrder_centralTangent hsJ)) Q.order hb)
    (hpK : (prime : K) ≠ 0) {e : ℕ} {u : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (u : 𝒪[K]) * ϖ ^ e) (hS : S.HasHeightSquared ϖ)
    (hz : ∀ (B : CommAlgCat.{0} (Reduced T)) (c : J.atlas.opens)
      (hc : IsUnit (algebraMap (Reduced T) B c.val)),
      RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime
        (I.restrictLocalQuasiIsogenyOnChart J (h := hj) B c hc X.localFraming X.commutes
          PadicInt.irreducible_p).val (fun _ => 0)) :
    let q := I.restrictCentralQuasiIsogeny J (h := hj) (I.divisionOrder_centralTangent hsI)
      (J.divisionOrder_centralTangent hsJ) (X.localFraming.toOrderTensor PadicInt.irreducible_p X.commutes)
      PadicInt.irreducible_p hpK X.localFraming.source_divisible X.localFraming.target_divisible
    (q.isoTransport a b).hom.val.HasConstantChartHeight ϖ (Nat.card 𝓀[K]) 0 := by
  dsimp only
  refine BasicAtlas.OrderAction.QuasiIsogeny.isoTransport_height _ a b
    (I.restrictCentralQuasiIsogeny_height_zero J (h := hj) (H := d ^ 2) hsI hsJ X.localFraming X.commutes
      PadicInt.irreducible_p hpK hp ?_ hz)
  intro B c hc
  let c₀ := BasicAtlas.sourceChart hj c
  let c₁ : S.atlas.opens := ⟨c₀.val, ha ▸ c₀.property⟩
  let f := (a.symm.onChart B c₀ hc).toModuleIso
  exact f.hasPiHeight ϖ (S.chartTest_height hS B c₁ hc).2

/-- A prime-normalized zero-height certificate on the projected local rigidifier
is a uniformizer-normalized zero-height certificate on the actual atlas framing. -/
theorem primalAtlasFraming_height_zero (hpK : (prime : K) ≠ 0) {e : ℕ} {u : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (u : 𝒪[K]) * ϖ ^ e)
    (hFrame : (primalSpecialFrame A hs h.1 hg).HasHeightSquared ϖ)
    (hz : HasPrimalChartHeightZero A h) :
    (primalAtlasFraming A hs hg h hpK).hom.val.HasConstantChartHeight ϖ (Nat.card 𝓀[K]) 0 := by
  unfold primalAtlasFraming
  dsimp only
  have hsI := hs.map (frameCoefficientMap prime πW T)
  have hcoeff : (frameCoefficientMap prime πW T).toRingHom.comp (algebraMap 𝒪[K] kW) =
      algebraMap 𝒪[K] (Reduced T) := RingHom.ext (primalResidueMap T).commutes
  rw [hcoeff] at hsI
  exact transportedPrimalChartHeightZero _ _ hsI (reducedTarget_structuralTangent h) _ _ hpK hp
    (primalFramingSourceAtlas_hasHeightSquared A hs hg h hFrame) hz

/-- Form the actual height-zero Drinfeld triple from a split polarized point,
its square-height frame, and the local projected height condition. -/
def primalDrinfeldFramedAtlasOfLocalHeight (hpK : (prime : K) ≠ 0) (hκ : IsField kW)
    (hFrame : (primalSpecialFrame A hs h.1 hg).HasHeightSquared ϖ) {e f : ℕ} (he : 0 < e)
    {u : 𝒪[K]ˣ} (hp : (prime : 𝒪[K]) = (u : 𝒪[K]) * ϖ ^ e)
    (hq : Nat.card 𝓀[K] = prime ^ f) (hz : HasPrimalChartHeightZero A h) :
    letI : Field kW := hκ.toField
    DrinfeldFramedAtlas ⟨primalSpecialFrame A hs h.1 hg, hFrame⟩ T :=
  primalDrinfeldFramedAtlas A hs hg h hpK hκ hFrame
    (h.primalHeightSquaredAtlas A hs hFrame.2 hFrame.1 he hp hq).property
    (primalAtlasFraming_height_zero A hs hg h hpK hp hFrame hz)

end Langlands.FormalGroup.Harris
