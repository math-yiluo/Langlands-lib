import Langlands.Geometry.FormalGroup.DrinfeldDivisionFrameHeight
import Langlands.Geometry.FormalGroup.DrinfeldFramedActionFormula
import Langlands.Geometry.FormalGroup.RationalHeightInverse

/-! # Signed kernel-rank height of the division twist on the reduced target -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open ValuativeRel CentralSimple ModuleLaw BasicAtlas.RationalHom

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable (X : DrinfeldFramedAtlas Φ A)

set_option maxHeartbeats 1000000 in
/-- The original rational framing transports the division-algebra action to the reduced target. -/
theorem frameDivision_conjugation (d : D) :
    comp X.rho.hom.val (comp (atlasRationalAction K D X.source.order d) X.rho.inv.val) =
      atlasRationalAction K D X.target.val.reduction.order d := by
  let e := X.rho.toAtlasQuasiIsogeny
  let a := atlasRationalAction K D X.source.order d
  let b := atlasRationalAction K D X.target.val.reduction.order d
  change comp e.hom (comp a e.inv) = b
  calc
    _ = comp (comp e.hom a) e.inv := (comp_assoc _ _ _).symm
    _ = comp (comp b e.hom) e.inv :=
      congrArg (fun z => comp z e.inv) (atlasRationalAction_commutes K D X.rho.hom d)
    _ = comp b (comp e.hom e.inv) := comp_assoc _ _ _
    _ = b := (congrArg (comp b) e.hom_inv).trans (comp_id b)

set_option maxHeartbeats 1000000 in
/-- The actual reduced-target twist has the inverse division-unit height on every original test. -/
theorem reducedTargetDivision_hasConstantChartHeight (g : Dˣ) :
    (X.target.val.reduction.twistDivisionUnitQuasiIsogeny g).hom.val.HasConstantChartHeight
      π (Nat.card 𝓀[K]) (-(reducedDegree K D : ℤ) * (DrinfeldAction.divisionUnitOrder K D g).toAdd) := by
  have hπ : algebraMap 𝒪[K] K π ≠ 0 := fun h =>
    Φ.property.1.ne_zero ((IsFractionRing.injective 𝒪[K] K) (h.trans (map_zero _).symm))
  have hq : 2 ≤ Nat.card 𝓀[K] := LocalField.residueCardinality_gt_one K
  have hH := pow_pos (reducedDegree_pos K D) 2
  let e := X.rho.toAtlasQuasiIsogeny
  have hinv : e.inv.HasConstantChartHeight π (Nat.card 𝓀[K]) 0 := by
    simpa only [neg_zero] using e.inv_hasConstantChartHeight hπ hq hH
      X.source_height.2.2 X.reducedTarget_height.2.2 X.height_zero
  change X.rho.inv.val.HasConstantChartHeight π (Nat.card 𝓀[K]) 0 at hinv
  have hframe : (atlasRationalAction K D X.source.order ((g⁻¹ : Dˣ) : D)).HasConstantChartHeight
      π (Nat.card 𝓀[K]) (-(reducedDegree K D : ℤ) * (DrinfeldAction.divisionUnitOrder K D g).toAdd) :=
    DrinfeldAction.frameDivision_hasConstantChartHeight Φ X.residueMap
      X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers g
  have hcomp := X.height_zero.comp hq X.reducedTarget_height.2.2 X.source_height.2.2
    (hframe.comp hq X.reducedTarget_height.2.2 X.source_height.2.2 hinv)
  change HasConstantChartHeight
    (atlasRationalAction K D X.target.val.reduction.order ((g⁻¹ : Dˣ) : D))
    π (Nat.card 𝓀[K]) _
  have hconj := X.frameDivision_conjugation ((g⁻¹ : Dˣ) : D)
  rw [← hconj]
  simpa only [zero_add, add_zero] using hcomp

/-- The original twist together with its signed height on the original reduced cover. -/
def reducedTargetDivisionWithHeight (g : Dˣ) :
    {e : BasicAtlas.OrderAction.QuasiIsogeny K X.target.val.reduction.order
        (X.target.val.reduction.twistDivisionUnit g).order rfl //
      e.hom.val.HasConstantChartHeight π (Nat.card 𝓀[K])
        (-(reducedDegree K D : ℤ) * (DrinfeldAction.divisionUnitOrder K D g).toAdd)} :=
  ⟨X.target.val.reduction.twistDivisionUnitQuasiIsogeny g,
    X.reducedTargetDivision_hasConstantChartHeight g⟩

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
