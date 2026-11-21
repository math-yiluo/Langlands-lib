import Langlands.Geometry.FormalGroup.AffineOrderTensor
import Langlands.Geometry.FormalGroup.PrimalAtlasQuasiIsogeny
import Langlands.Geometry.FormalGroup.SplitPrimalReducedAtlas

/-! # The split primal rigidifier on the actual reduced special atlas -/

noncomputable section

universe s

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw PolarizedFramedAffinePoint

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
variable {ϖ : 𝒪[K]}

local notation "πW" => algebraMap 𝒪[K] W ϖ
local notation "kW" => ResidueRing W πW
local notation "d" => CentralSimple.reducedDegree K D

private abbrev Reduced (T : Nilp.{0, 0} W πW) := ((Nilp.reductionFunctor W πW).obj T).obj

private abbrev FrameImage (frame : SplitPolarizedFrame prime K D W ϖ)
    (M : ModuleLaw ℤ_[prime] kW (Fin (CentralSimple.reducedDegree K D))) :=
  ModuleLaw.OrderAction.DivisionImage (O := ℤ_[prime]) (B := IntegerRing K D)
    (R := kW) (σ := Fin frame.dimension) (τ := Fin (CentralSimple.reducedDegree K D))
    (M := frame.law) frame.order M

variable {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}
variable {M : ModuleLaw ℤ_[prime] (ResidueRing W (algebraMap 𝒪[K] W ϖ))
  (Fin (CentralSimple.reducedDegree K D))}
variable (A : FrameImage frame M)
variable (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
  (algebraMap 𝒪[K] (ResidueRing W (algebraMap 𝒪[K] W ϖ))))
variable (hg : frame.order.HasGeometricDivisionTangentCharacters.{0, 0, 0, 0, s}
  (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D))

private abbrev reducedFrameImage (T : Nilp.{0, 0} W πW) :
    ModuleLaw.OrderAction.DivisionImage (O := ℤ_[prime]) (B := IntegerRing K D)
      (R := Reduced T) (σ := Fin frame.dimension) (τ := Fin d)
      (M := (source (frame := frame) (T := T)).law)
      (source (frame := frame) (T := T)).order (M.map (frameCoefficientMap prime πW T)) :=
  A.map (frameCoefficientMap prime πW T)

include hs in
private theorem reducedFrame_structuralTangent (T : Nilp.{0, 0} W πW) :
    (source (frame := frame) (T := T)).order.HasStructuralDivisionTangent
      (algebraMap 𝒪[K] (IntegerRing K D)) (algebraMap 𝒪[K] (Reduced T)) := by
  have h := hs.map (frameCoefficientMap prime πW T)
  have hmap : (frameCoefficientMap prime πW T).toRingHom.comp (algebraMap 𝒪[K] kW) =
      algebraMap 𝒪[K] (Reduced T) := RingHom.ext (primalResidueMap T).commutes
  rw [hmap] at h
  exact h

private def reducedPrimalSourceCover (h : HasSplitSpecialTangent ι X) :
    IdempotentImageCover (source (frame := frame) (T := T)).order.divisionProjector (Fin d) :=
  IdempotentImageCover.ofGlobalImageCover (reducedFrameImage A T)
    (reducedPrimalImageCover h).atlas.opens (reducedPrimalImageCover h).atlas.covers

/-- The actual central residue frame, extended to the reduced target's principal cover. -/
def primalFramingSourceAtlas (h : HasSplitSpecialTangent ι X) : SpecialAtlas K D ι (Reduced T) :=
  SpecialAtlas.ofGlobalCover ((primalSpecialFrame A hs h.1 hg).mapSameUniverse (primalResidueMap T))
    h.primalSpecialAtlas.reduction.atlas.opens h.primalSpecialAtlas.reduction.atlas.covers

private theorem reducedFrameOrder_coordinates (T : Nilp.{0, 0} W πW) (a : IntegerRing K D) :
    (((reducedFrameImage A T).centralOrder (reducedFrame_structuralTangent hs T)).action a).toHom.toCoordinateMap =
      ((((ModuleLaw.OrderAction.DivisionImage.centralOrder (E := frame.order) A hs).map
        (primalResidueMap T)).action a).toHom.toCoordinateMap) := by
  let φ := (primalResidueMap T).toRingHom
  change (A.projection.toHom.toCoordinateMap.map φ).comp
      (((frame.order.action (0, a)).toHom.toCoordinateMap.map φ).comp
        (A.inclusion.toHom.toCoordinateMap.map φ)) =
    (A.projection.toHom.toCoordinateMap.comp
      ((frame.order.action (0, a)).toHom.toCoordinateMap.comp A.inclusion.toHom.toCoordinateMap)).map φ
  rw [CoordinateMap.map_comp, CoordinateMap.map_comp]

private def reducedPrimalSourceOrder (h : HasSplitSpecialTangent ι X) :=
  let I := reducedPrimalSourceCover A h
  (I.divisionOrder (source (frame := frame) (T := T)).order).centralAtlasOrder
    (I.divisionOrder_centralTangent (E := (source (frame := frame) (T := T)).order)
      (reducedFrame_structuralTangent hs T))

private def reducedPrimalSourceIso (h : HasSplitSpecialTangent ι X) :
    BasicAtlas.OrderAction.Iso (reducedPrimalSourceOrder A hs h) (primalFramingSourceAtlas A hs hg h).order
      (reducedPrimalImageCover_opens h) := by
  let t := reducedFrame_structuralTangent hs T
  let J := reducedPrimalImageCover h
  let q := IdempotentImageCover.globalImageCentralIso (reducedFrameImage A T) t J.atlas.opens J.atlas.covers
  let E := BasicAtlas.ofGlobalCoverOrderAction ((reducedFrameImage A T).centralOrder t) J.atlas.opens J.atlas.covers
  let G := (primalFramingSourceAtlas A hs hg h).order
  let e := reducedPrimalImageCover_opens h
  let r : BasicAtlas.OrderAction.Iso E G e := by
    refine BasicAtlas.OrderAction.Iso.ofIdenticalChartCoordinates E G e ?_ ?_ ?_
    · intro B b hb
      rfl
    · intro B b hb a
      let α := algebraMap (Reduced T) (Localization.Away b.val)
      let β := (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val B hb).toRingHom
      have h := reducedFrameOrder_coordinates A hs T a
      exact congrArg (fun f : CoordinateMap (Reduced T) (Fin d) (Fin d) => (f.map α).map β) h
    · intro B b c hb hc
      rfl
  exact q.trans r

/-- The actual split rigidifying tensor, projected to the primal division images and
transported to the central residue frame and the reduced special target atlas. -/
def primalAtlasFraming (h : HasSplitSpecialTangent ι X) (hpK : (prime : K) ≠ 0) :
    BasicAtlas.OrderAction.QuasiIsogeny K
      (primalFramingSourceAtlas A hs hg h).order h.primalSpecialAtlas.reduction.order rfl := by
  let I := reducedPrimalSourceCover A h
  let J := reducedPrimalImageCover h
  let a := reducedPrimalSourceIso A hs hg h
  let b := reducedPrimalImageIso h
  let z := X.localFraming.toOrderTensor PadicInt.irreducible_p X.commutes
  let q := I.restrictCentralQuasiIsogeny J (h := rfl)
    (I.divisionOrder_centralTangent (E := (source (frame := frame) (T := T)).order)
      (reducedFrame_structuralTangent hs T))
    (J.divisionOrder_centralTangent (reducedTarget_structuralTangent h))
    z PadicInt.irreducible_p hpK X.localFraming.source_divisible X.localFraming.target_divisible
  exact ((BasicAtlas.OrderAction.QuasiIsogeny.ofIso a.symm).trans q).trans
    (BasicAtlas.OrderAction.QuasiIsogeny.ofIso b)

end Langlands.FormalGroup.Harris
