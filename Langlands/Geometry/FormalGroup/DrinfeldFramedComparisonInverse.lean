import Langlands.Geometry.FormalGroup.DrinfeldFramedComparison
import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonInverse
import Langlands.Geometry.FormalGroup.AtlasOrderQuasiIsogenyCalculus

/-! # Actual inverses of framed formal comparisons -/

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
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Reversing equality of residue maps inverts the actual identity frame map. -/
theorem globalFrameQuasiIso_symm (e : X.residueMap = Y.residueMap) :
    ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K) (globalFrameIso e.symm) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (globalFrameIso e)).symm := by
  cases X
  cases Y
  cases e
  rfl

/-- The same identity-frame inverse equation holds after actual test extension. -/
theorem globalFrameQuasiIso_map_symm (e : X.residueMap = Y.residueMap)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj) :
    ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := K)
        ((globalFrameIso e.symm).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))).symm := by
  have h := congrArg
    (ModuleLaw.OrderAction.QuasiIsogeny.map (IsScalarTower.toAlgHom 𝒪[K]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
    (globalFrameQuasiIso_symm e)
  simpa only [ModuleLaw.OrderAction.QuasiIsogeny.map_ofIso,
    ModuleLaw.OrderAction.QuasiIsogeny.map_symm] using h

/-- The reversed actual comparison has precisely the inverse rational chart map. -/
theorem reducedComparisonOnChart_symm
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : c.right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    reducedComparisonOnChart c.symm B
        (BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb =
      (reducedComparisonOnChart c B b hb).symm := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  rfl

/-- Reverse the actual rational square on the same two reduced refinements. -/
theorem ReducedFramingSquare.symm (e : X.residueMap = Y.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (h : ReducedFramingSquare e c) : ReducedFramingSquare e.symm c.symm := by
  intro B a ha
  let b := BasicAtlas.sourceChart (X := c.right.atlas) (Y := c.left.atlas) c.sameCover.symm a
  have hs := h B b ha
  have hr := ModuleLaw.OrderAction.QuasiIsogeny.square_reverse
    (X.refinedChartFraming c.left B a ha)
    (reducedComparisonOnChart c B b ha)
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
      ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B)))
    (Y.refinedChartFraming c.right B b ha) hs
  have hc := reducedComparisonOnChart_symm c B b ha
  have hf := globalFrameQuasiIso_map_symm e B
  exact (congrArg (fun k => (Y.refinedChartFraming c.right B b ha).trans k) hc).trans
    (hr.trans (congrArg (fun k => k.trans (X.refinedChartFraming c.left B a ha)) hf.symm))

/-- Quotient reduction and inversion retain the reverse framing square. -/
theorem FramingSquare.symm (e : X.residueMap = Y.residueMap)
    (g : SpecialAtlas.Comparison X.target.val Y.target.val)
    (h : FramingSquare e g) : FramingSquare e.symm g.symm := by
  unfold FramingSquare at *
  rw [SpecialAtlas.reductionComparison_symm]
  exact ReducedFramingSquare.symm e _ h

namespace Comparison

/-- Reverse the specified target comparison and its actual rational framing square. -/
def symm (f : Comparison X Y) : Comparison Y X where
  targetComparison := f.targetComparison.symm
  residue_eq := f.residue_eq.symm
  square := FramingSquare.symm f.residue_eq f.targetComparison f.square

@[simp]
theorem symm_symm (f : Comparison X Y) : f.symm.symm = f := by
  cases f
  rfl

/-- The same specified inverse target comparison acts inversely on complete families. -/
theorem symm_targetPointFunctorIso_hom_app (f : Comparison X Y)
    (B : CommAlgCat.{u} A.obj) (y : Y.target.val.Point B) :
    (f.symm.targetPointFunctorIso.hom.app B) y =
      (f.targetComparison.onPoints B).symm y := rfl

end Comparison

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
