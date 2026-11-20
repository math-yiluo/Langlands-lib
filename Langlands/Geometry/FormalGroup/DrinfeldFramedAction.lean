import Langlands.Geometry.FormalGroup.DrinfeldDivisionTargetHeight
import Langlands.Geometry.FormalGroup.DrinfeldFrobeniusHeight
import Langlands.Geometry.FormalGroup.DrinfeldMatrixFrameHeight

/-! # The height-zero Drinfeld transformation of framed representatives -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open ValuativeRel CentralSimple ModuleLaw

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {π : 𝒪[K]} {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable (X : DrinfeldFramedAtlas Φ A) (g : GL (Fin (reducedDegree K D)) K × Dˣ)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (f * j))
variable (c : Φ.val.MatrixCoordinates)

include hRank

set_option maxHeartbeats 1000000 in
/-- The signed kernel-rank heights of the four maps cancel on the original cover. -/
theorem actionFramingOnCover_hasConstantChartHeight :
    (X.actionFramingOnCover g p hcard hFrob c).hom.val.HasConstantChartHeight
      π (Nat.card 𝓀[K]) 0 := by
  have hπ : algebraMap 𝒪[K] K π ≠ 0 :=
    (IsFractionRing.injective 𝒪[K] K).ne (Φ.property.1.ne_zero) |>.trans_eq (map_zero _)
  have hq : 2 ≤ Nat.card 𝓀[K] := LocalField.residueCardinality_gt_one K
  have hsource := SpecialAtlas.quotientFrame_height Φ.val Φ.property (X.actionResidueMap g) X.target.val
  have hfrob := DrinfeldResidue.signedFrameFrobenius_hasConstantChartHeight
    Φ p hcard hFrob hRank hπ (DrinfeldAction.exponent K D g) (b := X.residueMap)
    rfl X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers
  have hmatrix := X.inverseMatrixSource_hasConstantChartHeight c g.1
  have htwist := X.reducedTargetDivision_hasConstantChartHeight g.2
  have hcomp := htwist.comp hq hsource.2.2 X.reducedTarget_height.2.2
    (X.height_zero.comp hq hsource.2.2 X.source_height.2.2
      (hmatrix.comp hq hsource.2.2 X.source_height.2.2 hfrob))
  have hindex :
      DrinfeldAction.exponent K D g * (reducedDegree K D : ℤ) +
        (-(reducedDegree K D : ℤ) * (Plancherel.fieldOrderUnits K g.1.det).toAdd) + 0 +
        (-(reducedDegree K D : ℤ) * (DrinfeldAction.divisionUnitOrder K D g.2).toAdd) = 0 := by
    rw [DrinfeldAction.exponent_eq]
    ring
  rw [hindex] at hcomp
  exact hcomp

/-- The literal transformed framing satisfies the defining height-zero condition. -/
theorem actionFraming_hasConstantChartHeight :
    (X.actionFraming g p hcard hFrob c).hom.val.HasConstantChartHeight
      π (Nat.card 𝓀[K]) 0 :=
  (X.actionFraming_hasConstantChartHeight_iff g p hcard hFrob c 0).mpr
    (X.actionFramingOnCover_hasConstantChartHeight g p hcard hFrob hRank c)

/-- Drinfeld's formula sends an actual height-zero framed representative to another. -/
def act : DrinfeldFramedAtlas Φ A where
  residueMap := X.actionResidueMap g
  target := X.actionTarget g
  rho := X.actionFraming g p hcard hFrob c
  height_zero := X.actionFraming_hasConstantChartHeight g p hcard hFrob hRank c

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
