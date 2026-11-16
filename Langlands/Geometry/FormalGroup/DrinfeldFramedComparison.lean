import Langlands.Geometry.FormalGroup.DrinfeldFramedAtlas
import Langlands.Geometry.FormalGroup.AtlasRationalHeightRefinement
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Actual framing squares on reduced principal refinements -/

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

/-- The actual global frame extended along the stored residue map. -/
def globalFrame (X : DrinfeldFramedAtlas Φ A) :
    SpecialModule K D ι
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj :=
  Φ.val.mapSameUniverse X.residueMap

private def frameExtensionIso
    (ψ ψ' : κ →ₐ[𝒪[K]]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (e : ψ = ψ') :
    ModuleLaw.OrderAction.Iso (Φ.val.mapSameUniverse ψ).order
      (Φ.val.mapSameUniverse ψ').order := by
  subst ψ'
  exact {
    hom := ModuleLaw.OrderAction.Hom.id _
    inv := ModuleLaw.OrderAction.Hom.id _
    inv_hom := Subtype.ext (ModuleLaw.Hom.comp_id _)
    hom_inv := Subtype.ext (ModuleLaw.Hom.comp_id _) }

/-- Equality of residue maps gives only the identity coordinate comparison of
their extended frames. No frame automorphism is chosen. -/
def globalFrameIso {X Y : DrinfeldFramedAtlas Φ A}
    (e : X.residueMap = Y.residueMap) :
    ModuleLaw.OrderAction.Iso X.globalFrame.order Y.globalFrame.order :=
  frameExtensionIso X.residueMap Y.residueMap e

/-- The given full-order quasi-isogeny, expressed from the global extended
frame to any actual refined reduced-target test chart. -/
def refinedChartFraming (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny K
      (X.globalFrame.order.map (IsScalarTower.toAlgHom 𝒪[K]
        ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))
      ((q.orderChart X.target.val.reduction.order b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb)) :=
  (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    (BasicAtlas.globalOrderChartIso X.globalFrame.order (q.source b).val B
      (q.source_unit B b hb))).symm.trans
    (X.rho.onChart B (q.source b) (q.source_unit B b hb)) |>.trans
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        (q.orderChartIso X.target.val.reduction.order B b hb)).symm

/-- The normalized framing uses the transported actual tensor, with its
existing local kernel-rank height zero. -/
theorem refinedChartFraming_height_zero (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : q.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    RationalSection.HasHeightFunction π (Nat.card 𝓀[K])
      (RationalSection.ofGlobal (X.refinedChartFraming q B b hb).hom.val) (fun _ => 0) := by
  let a := (BasicAtlas.globalOrderChartIso X.globalFrame.order (q.source b).val B
    (q.source_unit B b hb)).toModuleIso
  let t := (q.orderChartIso X.target.val.reduction.order B b hb).toModuleIso.symm
  have hz := (X.height_zero B (q.source b) (q.source_unit B b hb)).ofGlobal_isoTransport a t
  have he := ModuleLaw.RationalHom.isoTransport_eq_comp a t
    (X.rho.hom.onChart B (q.source b) (q.source_unit B b hb)).val
  exact (congrArg
    (fun z => RationalSection.HasHeightFunction π (Nat.card 𝓀[K])
      (RationalSection.ofGlobal z) (fun _ => 0)) he).mp hz

/-- The actual comparison map on the two selected finer test charts. -/
def reducedComparisonOnChart {X Y : DrinfeldFramedAtlas Φ A}
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : c.right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny K
      ((c.left.orderChart X.target.val.reduction.order
        (BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b)).map
          (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb))
      ((c.right.orderChart Y.target.val.reduction.order b).map
        (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb)) :=
  (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) c.coordinateIso).onChart B b hb

/-- The rational square for a specified comparison of the reduced targets. -/
def ReducedFramingSquare {X Y : DrinfeldFramedAtlas Φ A}
    (e : X.residueMap = Y.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction) : Prop :=
  ∀ (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : c.right.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)),
    (X.refinedChartFraming c.left B (BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb).trans
        (reducedComparisonOnChart c B b hb) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B))).trans
        (Y.refinedChartFraming c.right B b hb)

/-- The actual rational square uses the specified target comparison after
quotient reduction, and the identity comparison forced by residue-map equality. -/
def FramingSquare {X Y : DrinfeldFramedAtlas Φ A}
    (e : X.residueMap = Y.residueMap)
    (g : SpecialAtlas.Comparison X.target.val Y.target.val) : Prop :=
  ReducedFramingSquare e (SpecialAtlas.reductionComparison g)

/-- A framed comparison retains its actual target formal isomorphism after
principal refinements, equal residue maps, and the rational framing square. -/
structure Comparison (X Y : DrinfeldFramedAtlas Φ A) where
  targetComparison : SpecialAtlas.Comparison X.target.val Y.target.val
  residue_eq : X.residueMap = Y.residueMap
  square : FramingSquare residue_eq targetComparison

namespace Comparison

variable {X Y : DrinfeldFramedAtlas Φ A}

/-- The same actual target comparison gives the division-order-module functor isomorphism. -/
def targetPointFunctorIso (f : Comparison X Y) :
    X.target.val.pointFunctor ≅ Y.target.val.pointFunctor :=
  f.targetComparison.pointFunctorIso

/-- Quotient reduction keeps the specified target comparison, including its refinements. -/
def reducedTargetComparison (f : Comparison X Y) :
    SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction :=
  SpecialAtlas.reductionComparison f.targetComparison

/-- The actual reduced comparison gives the corresponding natural full-order isomorphism. -/
def reducedTargetPointFunctorIso (f : Comparison X Y) :
    X.target.val.reduction.pointFunctor ≅ Y.target.val.reduction.pointFunctor :=
  f.reducedTargetComparison.pointFunctorIso

end Comparison

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
