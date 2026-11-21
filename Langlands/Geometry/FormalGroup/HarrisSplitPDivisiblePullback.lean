import Langlands.Geometry.FormalGroup.FormalPDivisibleBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleOrderBaseChange
import Langlands.Geometry.FormalGroup.ModuleReduction

/-! # Pullback of the split polarized affine point -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v s

open CategoryTheory ValuativeRel

namespace Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

open LocalDivision CentralDivision ModuleLaw PDivisibleGroup
open SpecialModule.HeightSquaredModule

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T U : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}

local notation "T₀" => specialFibre (π := π) T
local notation "U₀" => specialFibre (π := π) U

/-- Pull back the actual affine split point across the quotient square of tests. -/
def baseChange (X : SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T) (f : T ⟶ U) :
    SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he U := by
  let φ := Nilp.scalarMap 𝒪[K] f
  let ψ := Nilp.reducedScalarMap 𝒪[K] f
  letI : Algebra T.obj U.obj := φ.toRingHom.toAlgebra
  letI : Algebra T₀ U₀ := ψ.toRingHom.toAlgebra
  letI : Algebra T.obj U₀ := ((Nilp.quotientO 𝒪[K] U).comp φ).toRingHom.toAlgebra
  letI : IsScalarTower T.obj U.obj U₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower T.obj T₀ U₀ := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (fun g : T.obj →ₐ[𝒪[K]] U₀ => g x) (Nilp.quotientO_natural 𝒪[K] f)
  letI : IsScalarTower (ResidueRing W (algebraMap 𝒪[K] W π)) T₀ U₀ :=
    IsScalarTower.of_algebraMap_eq fun x => (Nilp.residueReductionMap f.hom.hom).commutes x |>.symm
  let a := Φ.pDivisibleAction hp he
  let b := pDivisibleAction (R := T.obj) X.target hp he
  let Y := X.target.mapSameUniverse φ
  let c := pDivisibleAction (R := U.obj) Y hp he
  let d := (baseChangeEnd (S := U.obj) (X.target.pDivisibleGroup hp he)).comp b
  let source := baseChangeCompOrderIso (S := T₀) (T := U₀) a
  let compare := OrderQuasiIsogeny.ofIso (a := c) (b := d)
    (X.target.pDivisibleBaseChangeIso hp he φ) (X.target.pDivisibleBaseChangeIso_order hp he φ)
  let target := (compare.baseChange (S := U₀)).trans
    ((baseChangeCompOrderIso (S := U.obj) (T := U₀) b).symm.trans
      (baseChangeCompOrderIso (S := T₀) (T := U₀) b))
  exact {
    target := Y
    primalRigidifier := source.trans ((X.primalRigidifier.baseChange (S := U₀)).trans target.symm)
    multiplier := X.multiplier }

@[simp] theorem baseChange_multiplier (X : SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T)
    (f : T ⟶ U) : (X.baseChange f).multiplier = X.multiplier := rfl

end Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint
