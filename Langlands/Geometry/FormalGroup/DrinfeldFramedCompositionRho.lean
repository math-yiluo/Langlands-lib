import Langlands.Geometry.FormalGroup.DrinfeldFramedIdentityComparison
import Langlands.Geometry.FormalGroup.AtlasOrderReductionComposition

/-! # Whole actual framing tensors under composite Nilp-base extension -/

noncomputable section

universe u v w z s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra O R] [Algebra O S] [Algebra O T]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Actual coefficient-composition map corrected to a supplied equal composite coefficient map. -/
def compositionAlongIso (E : OrderAction D X) (f : R →ₐ[O] S) (g : S →ₐ[O] T)
    {m : R →ₐ[O] T} (hm : m = g.comp f) :=
  (E.baseAlongCompIso f g).trans (E.baseAlongEqIso hm.symm)

namespace QuasiIsogeny

/-- A forced equality of coefficient maps is natural on the whole actual global rational tensor. -/
theorem baseAlongEq_natural (a : QuasiIsogeny F E E' h) {f g : R →ₐ[O] S} (e : f = g) :
    (a.baseChangeAlong f).trans (h := baseAlongOpens_eq X Y f h)
        (ofIso (E'.baseAlongEqIso e)) =
      (ofIso (E.baseAlongEqIso e)).trans (a.baseChangeAlong g) := by
  cases e
  change (a.baseChangeAlong f).trans (ofIso (Iso.refl _)) =
    (ofIso (Iso.refl _)).trans (a.baseChangeAlong f)
  rw [ofIso_refl, ofIso_refl]
  exact (trans_refl _).trans (refl_trans _).symm

/-- Corrected supplied coefficient composition is natural on the whole global framing-type tensor. -/
theorem compositionAlong_natural (a : QuasiIsogeny F E E' h)
    (f : R →ₐ[O] S) (g : S →ₐ[O] T) {m : R →ₐ[O] T} (hm : m = g.comp f) :
    ((a.baseChangeAlong f).baseChangeAlong g).trans
        (h := baseAlongCompMapOpens_eq X Y f g h) (ofIso (E'.compositionAlongIso f g hm)) =
      (ofIso (E.compositionAlongIso f g hm)).trans (a.baseChangeAlong m) := by
  let q := (a.baseChangeAlong f).baseChangeAlong g
  let c₁ := E.baseAlongCompQuasiIsogeny (F := F) f g
  let c₂ := E'.baseAlongCompQuasiIsogeny (F := F) f g
  let e₁ := ofIso (F := F) (E.baseAlongEqIso hm.symm)
  let e₂ := ofIso (F := F) (E'.baseAlongEqIso hm.symm)
  have hc : q.trans c₂ = c₁.trans (a.baseChangeAlong (g.comp f)) := a.baseAlongComp_natural f g
  have he : (a.baseChangeAlong (g.comp f)).trans e₂ = e₁.trans (a.baseChangeAlong m) :=
    a.baseAlongEq_natural hm.symm
  have hn : q.trans (c₂.trans e₂) = (c₁.trans e₁).trans (a.baseChangeAlong m) := by
    exact (trans_assoc q c₂ e₂).symm.trans
      ((congrArg (fun j => j.trans e₂) hc).trans
        ((trans_assoc c₁ _ e₂).trans
          ((congrArg (fun j => c₁.trans j) he).trans (trans_assoc c₁ e₁ _).symm)))
  have hl : ofIso (F := F) (E'.compositionAlongIso f g hm) = c₂.trans e₂ :=
    ofIso_trans _ _
  have hr : ofIso (F := F) (E.compositionAlongIso f g hm) = c₁.trans e₁ :=
    ofIso_trans _ _
  exact (congrArg (fun j => q.trans j) hl).trans
    (hn.trans (congrArg (fun j => j.trans (a.baseChangeAlong m)) hr.symm))

/-- Cancel a specified inverse at the end of a left-associated whole tensor path. -/
@[simp]
theorem trans_inverse_tail (a : QuasiIsogeny F E E' h) (b : QuasiIsogeny F E' E'' k) :
    (a.trans b).trans b.symm = a := by
  rw [trans_assoc, self_trans_symm, trans_refl]

/-- Cancel a specified forward map after its inverse at the end of a whole tensor path. -/
@[simp]
theorem trans_forward_tail (a : QuasiIsogeny F E E' h) {l : Z.opens = Y.opens}
    (b : QuasiIsogeny F E'' E' l) :
    (a.trans b.symm).trans b = a := by
  rw [trans_assoc, symm_trans_self, trans_refl]

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B C : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual base-extended framing is the specified whole tensor inverse-correction composite. -/
theorem baseChange_rho_formula (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (X.baseChange f).rho =
      (((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
        (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f)).symm).trans
          (X.rho.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f))).trans
            (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (X.target.val.reductionBaseChangeIso f)).symm := by
  exact congrArg (fun j =>
    ((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
      (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f)).symm.trans
        (X.rho.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f))).trans j)
    (BasicAtlas.OrderAction.QuasiIsogeny.ofIso_symm (X.target.val.reductionBaseChangeIso f))

/-- The actual source map between successive and composite Nilp-base extensions. -/
def baseChangeCompositionSourceIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    BasicAtlas.OrderAction.Iso ((X.baseChange f).baseChange g).source.order
      (X.baseChange (f ≫ g)).source.order
      (BasicAtlas.reductionOpens_eq
        (X.target.val.atlas.baseAlongCompOpens_eq (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g))) :=
  (SpecialAtlas.quotientFrameBaseChangeIso Φ.val (X.baseChange f).residueMap
    (X.baseChange f).target.val g).symm.trans
      (((SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f).baseChangeAlong
        (Nilp.reducedScalarMap 𝒪[K] g)).symm.trans
          ((X.source.order.compositionAlongIso (Nilp.reducedScalarMap 𝒪[K] f)
            (Nilp.reducedScalarMap 𝒪[K] g) (Nilp.reducedScalarMap_comp 𝒪[K] f g)).trans
              (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val (f ≫ g))))

/-- Reduce the actual specified target coefficient-composition isomorphism. -/
def baseChangeCompositionReducedTargetIso (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    ((X.baseChange f).baseChange g).target.val.reduction.Iso
      (X.baseChange (f ≫ g)).target.val.reduction
      (BasicAtlas.reductionOpens_eq
        (X.target.val.atlas.baseAlongCompOpens_eq (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g))) :=
  (X.target.val.baseAlongCompIso (Nilp.scalarMap 𝒪[K] f) (Nilp.scalarMap 𝒪[K] g)).reduction

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Successive Nilp-base extension satisfies the whole actual framing tensor square. -/
theorem baseChangeComposition_rho (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) (g : B ⟶ C) :
    ((X.baseChange f).baseChange g).rho.trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.baseChangeCompositionReducedTargetIso f g)) =
        (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.baseChangeCompositionSourceIso f g)).trans
          (X.baseChange (f ≫ g)).rho := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let ψ := Nilp.reducedScalarMap 𝒪[K] g
  let χ := Nilp.reducedScalarMap 𝒪[K] (f ≫ g)
  let hm := Nilp.reducedScalarMap_comp 𝒪[K] f g
  let afi := (SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f).baseChangeAlong ψ
  let agi := SpecialAtlas.quotientFrameBaseChangeIso Φ.val (X.baseChange f).residueMap
    (X.baseChange f).target.val g
  let aci := SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val (f ≫ g)
  let tfi := (X.target.val.reductionBaseChangeIso f).baseChangeAlong ψ
  let tgi := (X.baseChange f).target.val.reductionBaseChangeIso g
  let tci := X.target.val.reductionBaseChangeIso (f ≫ g)
  let csi := X.source.order.compositionAlongIso φ ψ hm
  let cti := X.target.val.reduction.order.compositionAlongIso φ ψ hm
  let af := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) afi
  let ag := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) agi
  let ac := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) aci
  let tf := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) tfi
  let tg := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) tgi
  let tc := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) tci
  let cs := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) csi
  let ct := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) cti
  let t := BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.baseChangeCompositionReducedTargetIso f g)
  let q := (X.rho.baseChangeAlong φ).baseChangeAlong ψ
  let qc := X.rho.baseChangeAlong χ
  have hff := congrArg (fun j => j.baseChangeAlong ψ) (X.baseChange_rho_formula f)
  simp only [BasicAtlas.OrderAction.QuasiIsogeny.baseChangeAlong_trans,
    BasicAtlas.OrderAction.QuasiIsogeny.baseChangeAlong_symm,
    BasicAtlas.OrderAction.QuasiIsogeny.baseChangeAlong_ofIso] at hff
  have hf : ((X.baseChange f).rho.baseChangeAlong ψ) = (af.symm.trans q).trans tf.symm := hff
  have hfg : ((X.baseChange f).baseChange g).rho =
      ((((ag.symm.trans af.symm).trans q).trans tf.symm).trans tg.symm) := by
    have hh := (X.baseChange f).baseChange_rho_formula g
    change ((X.baseChange f).baseChange g).rho =
      (ag.symm.trans ((X.baseChange f).rho.baseChangeAlong ψ)).trans tg.symm at hh
    exact hh.trans ((congrArg (fun j => (ag.symm.trans j).trans tg.symm) hf).trans
      (by simp only [← BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc]))
  have hc : (X.baseChange (f ≫ g)).rho = (ac.symm.trans qc).trans tc.symm :=
    X.baseChange_rho_formula (f ≫ g)
  have hs : BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.baseChangeCompositionSourceIso f g) =
      ((ag.symm.trans af.symm).trans cs).trans ac := by
    change BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
      (agi.symm.trans (afi.symm.trans (csi.trans aci))) = _
    simp only [BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans,
      BasicAtlas.OrderAction.QuasiIsogeny.ofIso_symm, ← BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc]
    rfl
  have ht := congrArg (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K))
    (X.target.val.order.reductionBaseChange_comp f g)
  simp only [BasicAtlas.OrderAction.QuasiIsogeny.ofIso_trans] at ht
  have htarget : (tg.trans tf).trans ct = t.trans tc := ht
  have hn : q.trans ct = cs.trans qc := X.rho.compositionAlong_natural φ ψ hm
  apply BasicAtlas.OrderAction.QuasiIsogeny.trans_right_cancel _ _ tc
  rw [hfg, hs, hc, BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc _ t tc, htarget.symm]
  simp only [← BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc,
    BasicAtlas.OrderAction.QuasiIsogeny.trans_forward_tail,
    BasicAtlas.OrderAction.QuasiIsogeny.trans_inverse_tail]
  exact (BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc (ag.symm.trans af.symm) q ct).trans
    ((congrArg (fun j => (ag.symm.trans af.symm).trans j) hn).trans
      (BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc (ag.symm.trans af.symm) cs qc).symm)

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
