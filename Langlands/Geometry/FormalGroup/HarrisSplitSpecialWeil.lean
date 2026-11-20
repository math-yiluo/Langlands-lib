import Langlands.Geometry.FormalGroup.HarrisSplitSpecialTwist
import Langlands.Geometry.FormalGroup.PolarizedFramedAction
import Langlands.Geometry.FormalGroup.PolarizedFrobenius

/-! # Frobenius descent on the affine split-special functor -/

noncomputable section

universe u s

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
variable [wTower : IsScalarTower ℤ_[prime] 𝒪[K] W] {ϖ : 𝒪[K]}
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable (frame : SplitPolarizedFrame prime K D W ϖ) (σ : W ≃ₐ[𝒪[K]] W)

local instance splitSpecialWeilPadicIntegerRingAlgebra : Algebra ℤ_[prime] (IntegerRing K D) :=
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
local notation "Tσ" => Nilp.twistObj σₚ hπ T
local notation "twistSquare" => CoefficientChange.twist σₚ hπ frame T

/-- Harris's inverse-Frobenius rigidifier gives a natural isomorphism to the
structurally twisted affine split-special functor. -/
def splitSpecialWeilFrobeniusNatIso :
    splitSpecialAffineFunctor ι frame ≅ Nilp.twistFunctor σₚ hπ ⋙ splitSpecialAffineFunctor ι frame :=
  (splitSpecialChangeFrameNatIso ι Frob).trans (splitSpecialTwistFrameNatIso ι frame σ)

/-- First precompose the rigidifier by inverse relative Frobenius, then read
the result over the test with its Frobenius-twisted structural map. -/
def splitSpecialWeilFrobeniusPoint (X : PolarizedFramedAffinePoint prime πW frame T) :
    PolarizedFramedAffinePoint prime πW frame Tσ :=
  (X.changeFrame Frob).mapCoefficients twistSquare

@[simp]
theorem splitSpecialWeilFrobeniusNatIso_hom_app_val
    (q : (splitSpecialAffineFunctor ι frame).obj T) :
    ((splitSpecialWeilFrobeniusNatIso ι frame σ m hσ hF).hom.app T q).val =
      (q.val.changeFrame Frob).mapCoefficients twistSquare := rfl

/-- On the class of a representative the natural isomorphism sends it to the
class of the explicit Frobenius-twisted triple. -/
theorem splitSpecialWeilFrobeniusNatIso_hom_app_mk
    (X : PolarizedFramedAffinePoint prime πW frame T) (hX : HasSplitSpecialTangent ι X) :
    ((splitSpecialWeilFrobeniusNatIso ι frame σ m hσ hF).hom.app T
      ⟨Quotient.mk _ X, hX⟩).val =
        Quotient.mk _ (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X) := rfl

@[simp]
theorem splitSpecialWeilFrobeniusPoint_target (X : PolarizedFramedAffinePoint prime πW frame T) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).target = X.target.map (twistSquare).scalar :=
  rfl

/-- The rigidifier on the twisted test, including its canonical source and target
identifications across the reduction square. -/
theorem splitSpecialWeilFrobeniusPoint_rho (X : PolarizedFramedAffinePoint prime πW frame T) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).rho =
      RationalSection.transportIso (twistSquare).sourceIso.orderIso.toModuleIso
        ((twistSquare).targetIso (X.changeFrame Frob)).orderIso.toModuleIso ⊤
        (RationalSection.baseChange (twistSquare).reduced ⊤
          (RationalSection.comp X.rho
            ((Frob).sectionIso.baseChange (frameCoefficientMap prime πW T)).inv)) := rfl

/-- Under inverse precomposition, a given rational multiplier is multiplied by `p^(-m)`. -/
theorem splitSpecialWeilFrobeniusPoint_hasMultiplier
    (X : PolarizedFramedAffinePoint prime πW frame T) (c : ℚ_[prime]ˣ)
    (hc : RationalSection.HasPadicTorsionSimilitude prime
      (frame.map (frameCoefficientMap prime πW T)).polarization
      X.reducedTarget.polarization X.rho c) :
    RationalSection.HasPadicTorsionSimilitude prime
      (frame.map (frameCoefficientMap prime πW Tσ)).polarization
      (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).reducedTarget.polarization
      (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).rho
      ((PolarizedOrderModule.frobeniusMultiplier prime m)⁻¹ * c) := by
  let r := frameCoefficientMap prime πW T
  have h := hc.comp ((frame.frobeniusRationalSimilitude_hasMultipliers m σ₀ hσ hF).2.baseChange r)
  let b := (twistSquare).targetIso (X.changeFrame Frob)
  exact (h.baseChange (twistSquare).reduced).transportIso (twistSquare).sourceIso.orderIso.toModuleIso
    b.orderIso.toModuleIso (twistSquare).sourceIso.preserves b.preserves

end Langlands.FormalGroup.Harris
