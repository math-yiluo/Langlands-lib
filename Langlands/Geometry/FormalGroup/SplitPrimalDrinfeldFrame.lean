import Langlands.Geometry.FormalGroup.DrinfeldFramedAtlas
import Langlands.Geometry.FormalGroup.SplitPrimalAtlasFraming

/-! # The height-zero Drinfeld triple of a split primal rigidifier -/

noncomputable section

universe s

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
attribute [local instance] primalDivisionPadicAlgebra

set_option maxHeartbeats 1800000
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

local notation "kW" => ResidueRing W (algebraMap 𝒪[K] W ϖ)
local notation "d" => CentralSimple.reducedDegree K D

/-- With the actual square-height laws and the actual zero-height condition, the
split primal construction gives a height-zero Drinfeld framed triple. -/
def primalDrinfeldFramedAtlas {M : ModuleLaw ℤ_[prime] kW (Fin d)}
    (A : ModuleLaw.OrderAction.DivisionImage (O := ℤ_[prime]) (B := IntegerRing K D)
      (R := kW) (σ := Fin frame.dimension) (τ := Fin d) (M := frame.law) frame.order M)
    (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] kW))
    (hg : frame.order.HasGeometricDivisionTangentCharacters.{0, 0, 0, 0, s}
      (subfieldIntegerInclusion K D ι).toRingHom d)
    (h : HasSplitSpecialTangent ι X) (hpK : (prime : K) ≠ 0) (hκ : IsField kW)
    (hFrame : (primalSpecialFrame A hs h.1 hg).HasHeightSquared ϖ)
    (hTarget : h.primalSpecialAtlas.HasHeightSquared ϖ)
    (hzero : (primalAtlasFraming A hs hg h hpK).hom.val.HasConstantChartHeight ϖ (Nat.card 𝓀[K]) 0) :
    letI : Field kW := hκ.toField
    DrinfeldFramedAtlas ⟨primalSpecialFrame A hs h.1 hg, hFrame⟩ T :=
  letI : Field kW := hκ.toField
  { residueMap := primalResidueMap T
    target := ⟨h.primalSpecialAtlas, hTarget⟩
    rho := primalAtlasFraming A hs hg h hpK
    height_zero := hzero }

end Langlands.FormalGroup.Harris
