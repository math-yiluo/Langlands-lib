import Langlands.Geometry.FormalGroup.IdempotentImageAtlasAlong
import Langlands.Geometry.FormalGroup.SpecialAtlasReduction
import Langlands.Geometry.FormalGroup.SplitSpecialPrimalAtlas

/-! # The reduced split primal atlas and its special frame -/

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
variable {ϖ : 𝒪[K]} {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}

local notation "πW" => algebraMap 𝒪[K] W ϖ
local notation "kW" => ResidueRing W πW
local notation "d" => CentralSimple.reducedDegree K D

private abbrev Reduced (T : Nilp.{0, 0} W πW) := ((Nilp.reductionFunctor W πW).obj T).obj

/-- The actual residue coefficient map, now with its central scalar action. -/
def primalResidueMap (T : Nilp.{0, 0} W πW) : kW →ₐ[𝒪[K]] Reduced T where
  __ := algebraMap kW (Nilp.Reduction πW T.obj)
  commutes' _ := rfl

private abbrev reductionTest (T : Nilp.{0, 0} W πW) :=
  BasicAtlas.coefficientTest (Nilp.quotientO 𝒪[K] T)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra ℤ_[prime] 𝒪[K]] in
private theorem reducedPadicAlgebra_eq (T : Nilp.{0, 0} W πW) :
    coefficientAlgebra (O := ℤ_[prime]) (reductionTest T) =
      (inferInstance : Algebra ℤ_[prime] (Reduced T)) := by
  apply Algebra.algebra_ext
  intro a
  exact (Nilp.quotientO ℤ_[prime] T).commutes a

/-- Reduce the actual primal image retractions along the quotient map. -/
def reducedPrimalImageCover (h : HasSplitSpecialTangent ι X) :
    IdempotentImageCover X.reducedTarget.order.divisionProjector (Fin d) :=
  (primalImageCover X.target.order h.2.2).baseChangeWithAlgebra (reductionTest T) _
    (reducedPadicAlgebra_eq T)

/-- The structural central tangent condition survives the reduction of the target. -/
theorem reducedTarget_structuralTangent (h : HasSplitSpecialTangent ι X) :
    X.reducedTarget.order.HasStructuralDivisionTangent
      (algebraMap 𝒪[K] (IntegerRing K D)) (algebraMap 𝒪[K] (Reduced T)) := by
  have ht := h.2.1.map (Nilp.quotientO ℤ_[prime] T)
  have hmap : (Nilp.quotientO ℤ_[prime] T).toRingHom.comp (algebraMap 𝒪[K] T.obj) =
      algebraMap 𝒪[K] (Reduced T) := RingHom.ext (Nilp.quotientO 𝒪[K] T).commutes
  rw [hmap] at ht
  exact ht

/-- The reduced image cover uses the same generators as reduction of the central atlas. -/
theorem reducedPrimalImageCover_opens (h : HasSplitSpecialTangent ι X) :
    (reducedPrimalImageCover h).atlas.opens = h.primalSpecialAtlas.reduction.atlas.opens :=
  (primalImageCover X.target.order h.2.2).baseChangeWithAlgebra_opens (reductionTest T) _
    (reducedPadicAlgebra_eq T)

/-- The actual central order action on the reduced primal image. -/
def reducedPrimalImageOrder (h : HasSplitSpecialTangent ι X) :=
  ((reducedPrimalImageCover h).divisionOrder X.reducedTarget.order).centralAtlasOrder
    ((reducedPrimalImageCover h).divisionOrder_centralTangent (reducedTarget_structuralTangent h))

/-- The central atlas of the reduced image compares integrally with the reduction of the
actual special primal atlas. -/
def reducedPrimalImageIso (h : HasSplitSpecialTangent ι X) :
    BasicAtlas.OrderAction.Iso (reducedPrimalImageOrder h) h.primalSpecialAtlas.reduction.order
      (reducedPrimalImageCover_opens h) :=
  (primalImageCover X.target.order h.2.2).baseChangeWithAlgebraCentralIso (reductionTest T)
    ((primalImageCover X.target.order h.2.2).divisionOrder_centralTangent h.2.1)
    _ _ (reducedPadicAlgebra_eq T) (BasicAtlas.coefficientAlgebraAlong_eq (Nilp.quotientO 𝒪[K] T)) _

/-- The chosen global image of the split polarized frame is a special central formal module. -/
def primalSpecialFrame {M : ModuleLaw ℤ_[prime] kW (Fin (CentralSimple.reducedDegree K D))}
    (A : ModuleLaw.OrderAction.DivisionImage (O := ℤ_[prime]) (B := IntegerRing K D)
      (R := kW) (σ := Fin frame.dimension) (τ := Fin (CentralSimple.reducedDegree K D))
      (M := frame.law) frame.order M)
    (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] kW))
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hg : frame.order.HasGeometricDivisionTangentCharacters.{0, 0, 0, 0, s}
      (subfieldIntegerInclusion K D ι).toRingHom d) : SpecialModule K D ι kW where
  formalModule := ModuleLaw.OrderAction.DivisionImage.centralModule (E := frame.order) A hs
  order := ModuleLaw.OrderAction.DivisionImage.centralOrder (E := frame.order) A hs
  unramified := hL
  tangent := by
    exact ModuleLaw.OrderAction.DivisionImage.centralOrder_hasGeometricTangentCharacters
      (E := frame.order) A hs hg

end Langlands.FormalGroup.Harris
