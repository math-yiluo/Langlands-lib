import Langlands.Geometry.FormalGroup.DrinfeldFramedResidueCoherence
import Langlands.Geometry.FormalGroup.AtlasOrderRationalIdentity

/-! # Whole actual framing tensors under identity Nilp-base extension -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {E'' : OrderAction D Z} {E''' : OrderAction D W}
variable {h : X.opens = Y.opens} {k : Z.opens = Y.opens} {l : Y.opens = W.opens}

/-- Cancel an actual target correction in the whole global rational tensor composition. -/
theorem trans_symm_trans (a : QuasiIsogeny F E E' h) (b : QuasiIsogeny F E'' E' k)
    (c : QuasiIsogeny F E' E''' l) :
    (a.trans b.symm).trans (b.trans c) = a.trans c := by
  simp only [trans_assoc]
  rw [← trans_assoc b.symm b c, symm_trans_self, refl_trans]

/-- Four actual global rational atlas maps, their actual cover equalities and complete tensor square. -/
structure CommutingSquare (E : OrderAction D X) (E' : OrderAction D Y)
    (E'' : OrderAction D Z) (E''' : OrderAction D W) where
  topCover : X.opens = Y.opens
  rightCover : Y.opens = Z.opens
  leftCover : X.opens = W.opens
  bottomCover : W.opens = Z.opens
  top : QuasiIsogeny F E E' topCover
  right : QuasiIsogeny F E' E'' rightCover
  left : QuasiIsogeny F E E''' leftCover
  bottom : QuasiIsogeny F E''' E'' bottomCover
  commutes : top.trans right = left.trans bottom

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual source atlas comparison under identity Nilp-base extension. -/
def baseChangeIdentitySourceIso (X : DrinfeldFramedAtlas Φ A) :=
  (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val (𝟙 A)).symm.trans
    (X.source.order.identityAlongIso (Nilp.reducedScalarMap_id 𝒪[K] A))

/-- Reduce the actual target identity-base isomorphism. -/
def baseChangeIdentityReducedTargetIso (X : DrinfeldFramedAtlas Φ A) :=
  X.target.val.baseIdIso.reduction

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Identity base extension preserves the actual global framing tensor through the specified integral maps. -/
theorem baseChangeIdentity_rho (X : DrinfeldFramedAtlas Φ A) :
    (X.baseChange (𝟙 A)).rho.trans
        (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) X.baseChangeIdentityReducedTargetIso) =
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) X.baseChangeIdentitySourceIso).trans X.rho := by
  let hm := Nilp.reducedScalarMap_id 𝒪[K] A
  let sa := SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val (𝟙 A)
  let tq := X.target.val.reductionBaseChangeIso (𝟙 A)
  let si := X.source.order.identityAlongIso hm
  let ti := X.target.val.reduction.order.identityAlongIso hm
  let a := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) sa
  let t := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) tq
  let ss := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) si
  let tt := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) ti
  let q := X.rho.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] (𝟙 A))
  have hn := X.rho.identityAlong_natural hm
  have hti : tq.trans ti = X.baseChangeIdentityReducedTargetIso :=
    (BasicAtlas.OrderAction.Iso.trans_assoc tq
      X.target.val.order.reductionIdentityScalarIso
      X.target.val.reduction.order.baseIdIso).symm.trans
        X.target.val.order.reductionBaseChange_identity_unit
  have ht : BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
      X.baseChangeIdentityReducedTargetIso = t.trans tt :=
    (congrArg (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)) hti.symm).trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans tq ti)
  have hs : BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) X.baseChangeIdentitySourceIso =
      a.symm.trans ss := by
    exact (BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans sa.symm si).trans
      (congrArg (fun z => z.trans ss) (BasicAtlas.OrderAction.QuasiIsogeny.ofIso_symm sa))
  have hl : (X.baseChange (𝟙 A)).rho.trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) X.baseChangeIdentityReducedTargetIso) =
        ((a.symm.trans q).trans t.symm).trans (t.trans tt) := by
    change (((a.symm.trans q).trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) tq.symm))).trans _ = _
    exact congrArg₂ BasicAtlas.OrderAction.QuasiIsogeny.trans
      (congrArg (fun z => (a.symm.trans q).trans z)
        (BasicAtlas.OrderAction.QuasiIsogeny.ofIso_symm tq)) ht
  exact hl.trans ((BasicAtlas.OrderAction.QuasiIsogeny.trans_symm_trans (a.symm.trans q) t tt).trans
    ((BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc a.symm q tt).trans
      ((congrArg (fun z => a.symm.trans z) hn).trans
        ((BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc a.symm ss X.rho).symm.trans
          (congrArg (fun z => z.trans X.rho) hs.symm)))))

/-- The identity Nilp-base framing square on the four actual whole global tensor maps. -/
def baseChangeIdentityRhoSquare (X : DrinfeldFramedAtlas Φ A) :
    BasicAtlas.OrderAction.QuasiIsogeny.CommutingSquare (F := K)
      (X.baseChange (𝟙 A)).source.order (X.baseChange (𝟙 A)).target.val.reduction.order
      X.target.val.reduction.order X.source.order where
  topCover := rfl
  rightCover := BasicAtlas.reductionOpens_eq X.target.val.atlas.baseIdOpens_eq
  leftCover := BasicAtlas.reductionOpens_eq X.target.val.atlas.baseIdOpens_eq
  bottomCover := rfl
  top := (X.baseChange (𝟙 A)).rho
  right := BasicAtlas.OrderAction.QuasiIsogeny.ofIso X.baseChangeIdentityReducedTargetIso
  left := BasicAtlas.OrderAction.QuasiIsogeny.ofIso X.baseChangeIdentitySourceIso
  bottom := X.rho
  commutes := X.baseChangeIdentity_rho

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
