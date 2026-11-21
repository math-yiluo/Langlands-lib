import Langlands.Geometry.FormalGroup.SplitPrimalComponentIndex
import Langlands.Geometry.FormalGroup.TransportedPrimalChartHeight

/-! # The prime-normalized height of the actual projected split rigidifier -/

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

/-- The signed height in the prime normalization, evaluated on the primes of a chart test. -/
def primalPrimeChartRank (f : ℕ) (B : CommAlgCat.{0} (Reduced T)) :
    (⊤ : Opens (PrimeSpectrum B)) → ℤ :=
  fun x => -(primalComponentIndex A hs hg h hpK hFrame hTarget
    (x.val.comap (algebraMap (Reduced T) B))) * (d : ℤ) * (f : ℤ)

/-- The actual projected local rigidifier has prime-normalized height equal to
minus the first split index times the division degree and the residue degree. -/
theorem primalPrimeChartRank_hasHeight {e f : ℕ} {u : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (u : 𝒪[K]) * ϖ ^ e) (hf : 0 < f) (hq : Nat.card 𝓀[K] = prime ^ f)
    (B : CommAlgCat.{0} (Reduced T)) (c : h.primalSpecialAtlas.reduction.atlas.opens)
    (hc : IsUnit (algebraMap (Reduced T) B c.val)) :
    let J := reducedPrimalImageCover h
    let I : IdempotentImageCover (source (frame := frame) (T := T)).order.divisionProjector (Fin d) :=
      IdempotentImageCover.ofGlobalImageCover (A.map (frameCoefficientMap prime πW T))
        J.atlas.opens J.atlas.covers
    let c₀ : J.atlas.opens := ⟨c.val, (reducedPrimalImageCover_opens h).symm ▸ c.property⟩
    RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime
      (I.restrictLocalQuasiIsogenyOnChart J (h := rfl) B c₀ hc X.localFraming X.commutes
        PadicInt.irreducible_p).val (primalPrimeChartRank A hs hg h hpK hFrame hTarget f B) := by
  dsimp only
  let J := reducedPrimalImageCover h
  let I : IdempotentImageCover (source (frame := frame) (T := T)).order.divisionProjector (Fin d) :=
    IdempotentImageCover.ofGlobalImageCover (A.map (frameCoefficientMap prime πW T))
      J.atlas.opens J.atlas.covers
  let c₀ : J.atlas.opens := ⟨c.val, (reducedPrimalImageCover_opens h).symm ▸ c.property⟩
  let hS := primalFramingSourceAtlas_hasHeightSquared A hs hg h hFrame
  let hQ := h.primalSpecialAtlas.baseChangeAlong_height (Nilp.quotientO 𝒪[K] T) hTarget
  let z := primalAtlasFraming A hs hg h hpK
  have P : {k : (⊤ : Opens (PrimeSpectrum B)) → ℤ //
      RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime
        (I.restrictLocalQuasiIsogenyOnChart J (h := rfl) B c₀ hc X.localFraming X.commutes
          PadicInt.irreducible_p).val k ∧
      (∀ x, (f : ℤ) ∣ k x) ∧
      RationalSection.HasHeightFunction ϖ (Nat.card 𝓀[K])
        (RationalSection.ofGlobal (z.hom.onChart B c hc).val) (fun x => k x / (f : ℤ))} := by
    dsimp only [z]
    unfold primalAtlasFraming
    dsimp only
    have hsI := hs.map (frameCoefficientMap prime πW T)
    have hcoeff : (frameCoefficientMap prime πW T).toRingHom.comp (algebraMap 𝒪[K] kW) =
        algebraMap 𝒪[K] (Reduced T) := RingHom.ext (primalResidueMap T).commutes
    rw [hcoeff] at hsI
    have hpO : Nat.card (IsLocalRing.ResidueField ℤ_[prime]) = prime :=
      (Nat.card_congr PadicInt.residueField.toEquiv).trans (Nat.card_zmod prime)
    exact IdempotentImageCover.restrictCentralQuasiIsogeny_chartRank_transport I J (h := rfl)
      hsI (reducedTarget_structuralTangent h) _ _ B c hc X.localFraming X.commutes
      PadicInt.irreducible_p hpK hpO (Fact.out : prime.Prime).one_lt hf hFrame.1 hp hq hS.2.2 hQ.2.2
  have hEq := z.toAtlasQuasiIsogeny.heightOnChart_eq hFrame.1 hS.2.2 hQ.2.2 B c hc P.property.2.2
  have he : P.val = primalPrimeChartRank A hs hg h hpK hFrame hTarget f B := by
    funext x
    have hr : P.val x / (f : ℤ) = primalFramingRank A hs hg h hpK hFrame hTarget
        (x.val.comap (algebraMap (Reduced T) B)) :=
      (congrFun hEq x).symm.trans
        (z.toAtlasQuasiIsogeny.heightOnChart_eq_heightFunction hFrame.1 hS.2.2 hQ.2.2 B c hc x)
    change P.val x = -(primalComponentIndex A hs hg h hpK hFrame hTarget
        (x.val.comap (algebraMap (Reduced T) B))) * (d : ℤ) * (f : ℤ)
    calc
      P.val x = (P.val x / (f : ℤ)) * (f : ℤ) := (Int.ediv_mul_cancel (P.property.2.1 x)).symm
      _ = _ := congrArg (fun a : ℤ => a * (f : ℤ))
        (hr.trans (primalComponentIndex_rank A hs hg h hpK hFrame hTarget
          (x.val.comap (algebraMap (Reduced T) B))).symm)
  exact he ▸ P.property.1

/-- Vanishing of the actual first split coordinate is equivalent to vanishing of
its local prime height on every projected chart. -/
theorem primalComponentIndex_zero_iff_primeHeightZero {e f : ℕ} {u : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (u : 𝒪[K]) * ϖ ^ e) (hf : 0 < f) (hq : Nat.card 𝓀[K] = prime ^ f) :
    (∀ x, primalComponentIndex A hs hg h hpK hFrame hTarget x = 0) ↔
      HasPrimalChartHeightZero A h := by
  constructor
  · intro hz B c hc
    let c' : h.primalSpecialAtlas.reduction.atlas.opens := ⟨c.val, reducedPrimalImageCover_opens h ▸ c.property⟩
    have hr := primalPrimeChartRank_hasHeight A hs hg h hpK hFrame hTarget hp hf hq B c' hc
    have he : primalPrimeChartRank A hs hg h hpK hFrame hTarget f B = fun _ => 0 := by
      funext x
      simp only [primalPrimeChartRank, hz, neg_zero, zero_mul]
    exact he ▸ hr
  · intro hz
    exact (primalComponentIndex_zero_iff A hs hg h hpK hFrame hTarget).mpr
      (primalAtlasFraming_height_zero A hs hg h hpK hp hFrame hz)

end Langlands.FormalGroup.Harris
