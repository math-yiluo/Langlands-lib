import Langlands.Geometry.FormalGroup.DrinfeldFramedAtlas
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderBaseChangeAlong
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderMorphism
import Langlands.Geometry.FormalGroup.AtlasRationalHeightBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderRationalHeightIso
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChangeAlong
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Actual framed formal atlases over a varying Nilp base -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}

/-- Equal supplied covers retain the actual restricted global formal order action. -/
def globalCoverOrderIsoOfCoverEq (E : ModuleLaw.OrderAction D M)
    (a b : Set R) (ha : Ideal.span a = ⊤) (hb : Ideal.span b = ⊤) (e : a = b) :
    OrderAction.Iso (ofGlobalCoverOrderAction E a ha) (ofGlobalCoverOrderAction E b hb) e := by
  cases e
  exact OrderAction.Iso.refl _

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace SpecialAtlas

set_option backward.isDefEq.respectTransparency false in
/-- The extended original frame compares by actual full-order maps with the frame on the new quotient cover. -/
def quotientFrameBaseChangeIso (Φ : SpecialModule K D ι κ)
    (ψ : κ →ₐ[𝒪[K]]
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (Y : SpecialAtlas K D ι A.obj) (f : A ⟶ B) :
    BasicAtlas.OrderAction.Iso
      ((quotientFrame Φ ψ Y).order.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f))
      (quotientFrame Φ ((Nilp.reducedScalarMap 𝒪[K] f).comp ψ)
        (Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f))).order
      (Y.atlas.reductionBaseChangeOpens_eq f).symm := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let t := φ '' Y.reduction.atlas.opens
  have ht : Ideal.span t = ⊤ :=
    Y.reduction.atlas.baseOpens_covers (BasicAtlas.coefficientTest φ)
  let c₁ := BasicAtlas.globalCoverBaseAlongIso (Φ.mapSameUniverse ψ).order
    Y.reduction.atlas.opens Y.reduction.atlas.covers φ
  let c₂ := BasicAtlas.ofGlobalOrderIso (Φ.order.mapCompIso ψ φ) t ht
  let c₃ := BasicAtlas.globalCoverOrderIsoOfCoverEq (Φ.order.map (φ.comp ψ)) t
    (Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction.atlas.opens ht
    (Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction.atlas.covers
    (Y.atlas.reductionBaseChangeOpens_eq f).symm
  exact c₁.trans (c₂.trans c₃)

end SpecialAtlas

namespace DrinfeldFramedAtlas

variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}

/-- Extend the specified actual framed representative along a Nilp morphism,
retaining its actual target, fixed-frame source and local height zero. -/
def baseChange (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) : DrinfeldFramedAtlas Φ B where
  residueMap := (Nilp.reducedScalarMap 𝒪[K] f).comp X.residueMap
  target := X.target.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)
  rho := (X.rho.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)).isoTransport
    (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f)
    (X.target.val.reductionBaseChangeIso f).symm
  height_zero := by
    apply BasicAtlas.OrderAction.QuasiIsogeny.isoTransport_height
    have hz := X.height_zero.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f)
    exact (congrArg
      (fun z => z.HasConstantChartHeight π (Nat.card 𝓀[K]) 0)
      (BasicAtlas.OrderAction.RationalHom.baseChangeAlong_val
        (Nilp.reducedScalarMap 𝒪[K] f) X.rho.hom)).mpr hz

@[simp]
theorem baseChange_residueMap (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (X.baseChange f).residueMap = (Nilp.reducedScalarMap 𝒪[K] f).comp X.residueMap := rfl

@[simp]
theorem baseChange_target (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (X.baseChange f).target = X.target.baseChangeAlong (Nilp.scalarMap 𝒪[K] f) := rfl

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
