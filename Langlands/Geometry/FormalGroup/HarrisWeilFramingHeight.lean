import Langlands.Geometry.FormalGroup.HarrisSplitSpecialWeil
import Langlands.Geometry.FormalGroup.PolarizedFramedHeight
import Langlands.Geometry.FormalGroup.RationalSectionInverseHeight
import Langlands.Geometry.FormalGroup.RelativeFrobeniusIsogenyStatement

/-! # The rank change of the full polarized rigidifier under inverse Frobenius -/

noncomputable section

universe u

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw
open PolarizedFramedAffinePoint

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable [Algebra ℤ_[prime] 𝒪[K]]
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable [IsScalarTower ℤ_[prime] 𝒪[K] W] {ϖ : 𝒪[K]}
variable (frame : SplitPolarizedFrame prime K D W ϖ) (σ : W ≃ₐ[𝒪[K]] W)

local instance harrisWeilFramingHeightPadicIntegerRingAlgebra : Algebra ℤ_[prime] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[prime] 𝒪[K])

variable [ExpChar (ResidueRing W (algebraMap 𝒪[K] W ϖ)) prime] (m : ℕ)
variable (hσ :
  (Nilp.twistResidueEquiv (σ.restrictScalars ℤ_[prime]) (σ.commutes ϖ)).toRingHom =
    iterateFrobenius (ResidueRing W (algebraMap 𝒪[K] W ϖ)) prime m)
variable (hF : (frame.order.frobeniusHom prime m
    (Nilp.twistResidueEquiv (σ.restrictScalars ℤ_[prime]) (σ.commutes ϖ)).toAlgHom hσ).val.IsIsogeny)
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}

local notation "πW" => algebraMap 𝒪[K] W ϖ
local notation "σₚ" => AlgEquiv.restrictScalars ℤ_[prime] σ
local notation "hπ" => AlgEquiv.commutes σ ϖ
local notation "σ₀" => AlgEquiv.toAlgHom (Nilp.twistResidueEquiv σₚ hπ)
local notation "Frob" => frame.frobeniusRationalSimilitude m σ₀ hσ hF
local notation "twistSquare" => CoefficientChange.twist σₚ hπ frame T

/-- The raw height of the full polarized rigidifier decreases by the relative
Frobenius exponent times the dimension of the full frame. -/
theorem splitSpecialWeilFrobeniusPoint_hasFramingHeight
    (X : PolarizedFramedAffinePoint prime πW frame T) {H : ℕ} (hH : 0 < H)
    (hFrame : frame.law.HasPiHeight (prime : ℤ_[prime]) prime H)
    (hRank : RelativeFrobeniusIsogenyStatement frame.law prime m)
    {h : reducedTop T → ℤ} (hh : X.HasFramingHeight h) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).HasFramingHeight
      (fun x => h (coefficientOpenPoint (twistSquare).reduced ⊤ x) -
        (m * frame.dimension : ℕ)) := by
  let r := frameCoefficientMap prime πW T
  let f := (frame.order.frobeniusHom prime m σ₀ hσ).val
  let e := (Frob).sectionIso.baseChange r
  have he : e.hom = RationalSection.ofHom (f.map r) ⊤ := by
    change RationalSection.baseChange r ⊤ (Frob).sectionIso.hom = _
    rw [frame.frobeniusRationalSimilitude_hom, RationalSection.baseChange_ofHom]
    rfl
  have hf : (f.map r).HasHeight prime (m * frame.dimension) := by
    have h := (frame.order.frobeniusHom_height_of_statement prime m hRank σ₀ hσ).map r
    simpa only [Nat.card_fin] using h
  have hp : algebraMap ℤ_[prime] ℚ_[prime] (prime : ℤ_[prime]) ≠ 0 := by
    rw [map_natCast]
    exact Nat.cast_ne_zero.mpr (Fact.out : prime.Prime).ne_zero
  have hHeight := e.hasHeightFunction_transportIso_baseChange_comp_inv_ofHom
    (f.map r) he hf hp (Fact.out : prime.Prime).two_le hH
    (hFrame.map r) ((hFrame.map σ₀).map r) hh (twistSquare).reduced
    (twistSquare).sourceIso.orderIso.toModuleIso
    ((twistSquare).targetIso (X.changeFrame Frob)).orderIso.toModuleIso
  unfold HasFramingHeight
  rw [splitSpecialWeilFrobeniusPoint_rho]
  exact hHeight

end Langlands.FormalGroup.Harris
