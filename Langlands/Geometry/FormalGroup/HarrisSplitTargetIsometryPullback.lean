import Langlands.Geometry.FormalGroup.HarrisSplitPDivisibleClasses
import Langlands.Geometry.FormalGroup.PDivisibleSplitIsometryBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleSplitPolarizedIso

/-! # Pullback of the actual split target isometry on affine tests -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v s

open CategoryTheory ValuativeRel

namespace Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

open LocalDivision CentralDivision ModuleLaw GroupScheme.Cartier PDivisibleGroup
open SpecialModule.HeightSquaredModule

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {embedding : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) («ι» := embedding)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T U : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}

local notation "Point" => SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he

/-- Compare the split tower of the coefficient-extended target with the split of the
pulled-back primal tower. -/
def targetPrimalComparison (X : Point T) (f : T ⟶ U) (hExact : FiniteCartierDualExactnessStatement.{v}) :
    let φ := Nilp.scalarMap 𝒪[K] f
    letI : Algebra T.obj U.obj := φ.toRingHom.toAlgebra
    (X.baseChange f).targetTower hExact ≅
      ((baseChangeFunctor T.obj U.obj p).obj (X.target.pDivisibleGroup hp he)).splitWithDual hExact := by
  let φ := Nilp.scalarMap 𝒪[K] f
  letI : Algebra T.obj U.obj := φ.toRingHom.toAlgebra
  have j := splitPolarizedIso hExact (X.target.pDivisibleBaseChangeIso hp he φ)
  dsimp only [targetTower, baseChange, splitPDivisibleGroup]
  exact j

/-- The target comparison respects the full split order. -/
theorem targetPrimalComparison_order (X : Point T) (f : T ⟶ U)
    (hExact : FiniteCartierDualExactnessStatement.{v})
    (a : (IntegerRing K D)ᵐᵒᵖ × IntegerRing K D) :
    let φ := Nilp.scalarMap 𝒪[K] f
    letI : Algebra T.obj U.obj := φ.toRingHom.toAlgebra
    (X.baseChange f).orderAction hExact a ≫ (X.targetPrimalComparison f hExact).hom =
      (X.targetPrimalComparison f hExact).hom ≫
        splitOrderAction ((baseChangeEnd (S := U.obj) (X.target.pDivisibleGroup hp he)).comp
          (X.target.pDivisibleAction hp he)) hExact a := by
  let φ := Nilp.scalarMap 𝒪[K] f
  let algebra : Algebra T.obj U.obj := φ.toRingHom.toAlgebra
  let G := (X.target.mapSameUniverse φ).pDivisibleGroup hp he
  let H := (@baseChangeFunctor T.obj U.obj _ _ algebra p _).obj (X.target.pDivisibleGroup hp he)
  let uG : IntegerRing K D →+* End G := (X.target.mapSameUniverse φ).pDivisibleAction hp he
  let uH : IntegerRing K D →+* End H :=
    (@baseChangeEnd T.obj U.obj _ _ algebra p _ (X.target.pDivisibleGroup hp he)).comp
      (X.target.pDivisibleAction hp he)
  let j : G ≅ H := X.target.pDivisibleBaseChangeIso hp he φ
  have hOrder (d : IntegerRing K D) : uG d ≫ j.hom = j.hom ≫ uH d :=
    X.target.pDivisibleBaseChangeIso_order hp he φ d
  have h := splitPolarizedIso_order hExact (a := uG) (b := uH) j hOrder a
  dsimp only [orderAction, targetPrimalComparison, targetTower, baseChange,
    splitPDivisibleAction, splitPDivisibleGroup]
  exact h

/-- Pull back the actual target isomorphism and compare with the coefficient-extended targets. -/
def baseChangeTargetIso {X Y : Point T} (hExact : FiniteCartierDualExactnessStatement.{v})
    (i : PolarizedFramedTower.Iso (X.framedTower hExact) (Y.framedTower hExact)) (f : T ⟶ U) :
    (X.baseChange f).targetTower hExact ≅ (Y.baseChange f).targetTower hExact := by
  let φ := Nilp.scalarMap 𝒪[K] f
  letI : Algebra T.obj U.obj := φ.toRingHom.toAlgebra
  let G := X.target.pDivisibleGroup hp he
  let H := Y.target.pDivisibleGroup hp he
  let e : G.splitWithDual hExact ≅ H.splitWithDual hExact := i.targetIso
  let k := baseChangeSplitTowerIso (S := U.obj) hExact e
  let jX := X.targetPrimalComparison f hExact
  let jY := Y.targetPrimalComparison f hExact
  exact jX.trans (k.trans jY.symm)

end Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint
