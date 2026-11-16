import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.SpecialAtlasReduction

/-! # Actual height-zero framed triples over the principal quotient -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace SpecialAtlas

/-- Extend the supplied actual frame along the residue map, and restrict it to
exactly the cover of the actual reduced target. -/
def quotientFrame (Φ : SpecialModule K D ι κ)
    (ψ : κ →ₐ[𝒪[K]]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (Y : SpecialAtlas K D ι A.obj) :
    SpecialAtlas K D ι
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj :=
  ofGlobalCover (Φ.mapSameUniverse ψ) Y.reduction.atlas.opens
    Y.reduction.atlas.covers

@[simp]
theorem quotientFrame_opens (Φ : SpecialModule K D ι κ)
    (ψ : κ →ₐ[𝒪[K]]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (Y : SpecialAtlas K D ι A.obj) :
    (quotientFrame Φ ψ Y).atlas.opens = Y.reduction.atlas.opens := rfl

/-- The extended and restricted frame retains its supplied actual height d². -/
theorem quotientFrame_height (Φ : SpecialModule K D ι κ)
    (hΦ : Φ.HasHeightSquared π)
    (ψ : κ →ₐ[𝒪[K]]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (Y : SpecialAtlas K D ι A.obj) :
    (quotientFrame Φ ψ Y).HasHeightSquared π :=
  ofGlobalCover_height _ (hΦ.map ψ) _ _

end SpecialAtlas

/-- Actual representatives of the height-zero framed triples, relative to a
supplied height-certified frame over a supplied residue field. -/
structure DrinfeldFramedAtlas
    (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
      (R := κ) π) (A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)) where
  residueMap : κ →ₐ[𝒪[K]]
    ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj
  target : SpecialAtlas.HeightSquaredAtlas (K := K) (D := D) (ι := ι)
    (R := A.obj) π
  rho : BasicAtlas.OrderAction.QuasiIsogeny K
    (SpecialAtlas.quotientFrame Φ.val residueMap target.val).order
    target.val.reduction.order rfl
  height_zero : rho.hom.val.HasConstantChartHeight π (Nat.card 𝓀[K]) 0

namespace DrinfeldFramedAtlas

variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}
variable (X : DrinfeldFramedAtlas Φ A)

/-- The source is the actual extended fixed frame on the target's reduced cover. -/
def source :
    SpecialAtlas K D ι
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj :=
  SpecialAtlas.quotientFrame Φ.val X.residueMap X.target.val

@[simp]
theorem source_opens :
    X.source.atlas.opens = X.target.val.reduction.atlas.opens := rfl

/-- Actual scalar-kernel height certificates on the source. -/
theorem source_height : X.source.HasHeightSquared π :=
  SpecialAtlas.quotientFrame_height Φ.val Φ.property X.residueMap X.target.val

/-- Actual scalar-kernel height certificates on the reduced target. -/
theorem reducedTarget_height : X.target.val.reduction.HasHeightSquared π :=
  X.target.val.reduction_height X.target.property

/-- Every chart of the framing is an actual local quasi-isogeny whose section
is the section of the given rational full-order formal map. -/
def localFraming (hπ : algebraMap 𝒪[K] K π ≠ 0)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    LocalQuasiIsogeny K π
      (X.source.chartTestModule B b hb).formalModule
      (X.target.val.reduction.chartTestModule B b hb).formalModule ⊤ :=
  X.height_zero.localQuasiIsogeny hπ B b hb
    ((X.source.chartTest_height X.source_height B b hb).2.piDivisible)
    ((X.target.val.reduction.chartTest_height X.reducedTarget_height B b hb).2.piDivisible)

@[simp]
theorem localFraming_val (hπ : algebraMap 𝒪[K] K π ≠ 0)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    (X.localFraming hπ B b hb).val =
      RationalSection.ofGlobal (X.rho.hom.onChart B b hb).val := rfl

/-- The same actual framing has the local kernel-rank height function zero. -/
theorem localFraming_height_zero (hπ : algebraMap 𝒪[K] K π ≠ 0)
    (B : CommAlgCat.{u}
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    RationalSection.HasHeightFunction π (Nat.card 𝓀[K])
      (X.localFraming hπ B b hb).val (fun _ => 0) :=
  X.height_zero B b hb

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
