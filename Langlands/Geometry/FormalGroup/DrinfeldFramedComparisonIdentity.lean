import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonInverse
import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonIdentity

/-! # Actual identity comparisons of framed formal atlases -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Reflexive equality of residue maps gives the actual rational identity frame map. -/
theorem globalFrameQuasiIso_refl (X : DrinfeldFramedAtlas Φ A) :
    ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
        (globalFrameIso (X := X) (Y := X) rfl) =
      ModuleLaw.OrderAction.QuasiIsogeny.refl X.globalFrame.order := rfl

/-- The same reflexive frame comparison is identity on every actual coefficient test. -/
theorem globalFrameQuasiIso_map_refl (X : DrinfeldFramedAtlas Φ A)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj) :
    ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
        ((globalFrameIso (X := X) (Y := X) rfl).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) =
      ModuleLaw.OrderAction.QuasiIsogeny.refl
        (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) := by
  rw [← ModuleLaw.OrderAction.QuasiIsogeny.map_ofIso,
    globalFrameQuasiIso_refl, ModuleLaw.OrderAction.QuasiIsogeny.map_refl]

/-- A diagonal target comparison is the rational identity on each defined finer chart. -/
theorem reducedComparisonOnChart_diagonal (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    reducedComparisonOnChart
        (BasicAtlas.OrderAction.Comparison.diagonal X.target.val.reduction.order q) B b hb =
      ModuleLaw.OrderAction.QuasiIsogeny.refl
        ((q.orderChart X.target.val.reduction.order b).map
          (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb)) := by
  exact (congrArg (fun f => f.onChart B b hb)
    (BasicAtlas.OrderAction.QuasiIsogeny.ofIso_refl
      (F := K) (q.orderAction X.target.val.reduction.order))).trans
        (BasicAtlas.OrderAction.QuasiIsogeny.onChart_refl
          (F := K) (q.orderAction X.target.val.reduction.order) B b hb)

/-- The normalized actual framing commutes with identity on any actual refinement. -/
theorem ReducedFramingSquare.diagonal (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas) :
    ReducedFramingSquare (X := X) (Y := X) rfl
      (BasicAtlas.OrderAction.Comparison.diagonal X.target.val.reduction.order q) := by
  intro B b hb
  have hc := reducedComparisonOnChart_diagonal X q B b hb
  have hf := globalFrameQuasiIso_map_refl X B
  exact ((congrArg (fun k => (X.refinedChartFraming q B b hb).trans k) hc).trans
    (ModuleLaw.OrderAction.QuasiIsogeny.trans_refl _)).trans
      (((congrArg (fun k => k.trans (X.refinedChartFraming q B b hb)) hf).trans
        (ModuleLaw.OrderAction.QuasiIsogeny.refl_trans _)).symm)

/-- Any actual diagonal reduced target comparison supplies the identity framing square. -/
theorem ReducedFramingSquare.of_isDiagonal (X : DrinfeldFramedAtlas Φ A)
    (c : SpecialAtlas.Comparison X.target.val.reduction X.target.val.reduction)
    (h : c.IsDiagonal) : ReducedFramingSquare (X := X) (Y := X) rfl c := by
  obtain ⟨q, rfl⟩ := h
  exact ReducedFramingSquare.diagonal X q

/-- The specified reflexive target comparison has the actual framing square after reduction. -/
theorem FramingSquare.refl (X : DrinfeldFramedAtlas Φ A) :
    FramingSquare (X := X) (Y := X) rfl
      (BasicAtlas.OrderAction.Comparison.refl X.target.val.order) :=
  ReducedFramingSquare.of_isDiagonal X _
    (SpecialAtlas.isDiagonal_reductionComparison _
      (BasicAtlas.OrderAction.Comparison.isDiagonal_refl X.target.val.order))

namespace Comparison

/-- Identity comparison of an actual framed representative with itself. -/
def refl (X : DrinfeldFramedAtlas Φ A) : Comparison X X where
  targetComparison := BasicAtlas.OrderAction.Comparison.refl X.target.val.order
  residue_eq := rfl
  square := FramingSquare.refl X

/-- The specified identity comparison fixes every complete target family. -/
theorem refl_targetPointFunctorIso_hom_app (X : DrinfeldFramedAtlas Φ A)
    (B : CommAlgCat.{u} A.obj) (x : X.target.val.Point B) :
    ((refl X).targetPointFunctorIso.hom.app B) x = x :=
  BasicAtlas.OrderAction.Comparison.onPoints_refl X.target.val.order B x

end Comparison

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
