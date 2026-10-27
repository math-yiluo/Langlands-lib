import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Induction.HeterogeneousPairs
import Langlands.Representation.Tensor.GLRefinement

/-! Factor identifications for the literal three-block regrouping consumer. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.FiniteTensor

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The published rank-transport linear map as an actual representation equivalence. -/
def rankCastRepresentationEquiv {r s : ℕ} (h : r = s) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear s F.Carrier),
      Representation.Equiv
        (A.representation.comp (reindex (R := F.Carrier) (finCongr h)).toMonoidHom)
        (h.symm ▸ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)).representation := by
  letI := T.topology
  intro A
  refine Representation.Equiv.mk (rankCastLinearEquiv F T h A) ?_
  intro g
  ext v
  exact rankCastLinearEquiv_action F T h A g v

end Langlands.FiniteTensor

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

set_option maxHeartbeats 800000 in
/-- A one-block product of the canonically transported factor evaluates to that factor. -/
def singleBlockTransportedProductEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier),
      Representation.Equiv
        (T.normalizedProductInduced B (fun i =>
          (B.singleBlock_size hB i |>.symm ▸ A :
            SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)).representation))
        A.representation := by
  letI := T.topology
  intro A
  let i := B.singleBlockIndex hB
  let h := B.singleBlock_size hB i
  let e := GeneralLinear.reindex (R := F.Carrier) (finCongr h)
  let δ := T.singleBlockNormalizedProductEquiv B hB
    (fun j => ((B.singleBlock_size hB j).symm ▸ A :
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size j) F.Carrier)).representation)
    (fun j => SmoothRep.isSmooth _) i
  let ε := (FiniteTensor.rankCastRepresentationEquiv F T h A).symm.precomp
    e.symm.toMonoidHom
  let E := δ.trans ε
  refine Representation.Equiv.mk E.toLinearEquiv ?_
  intro g
  have hE := E.isIntertwining' g
  simpa only [e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using hE

end Langlands.PadicField.TopologicalData

namespace Langlands.Parabolic

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] {C A B : ℕ}

/-- Three bundled smooth factors in their literal ordered rank family. -/
def threeBlockSmoothFamily
    (σ0 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear C F))
    (σ1 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear A F))
    (σ2 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear B F)) :
    ∀ i : Fin 3, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (![C,A,B] i) F) :=
  Fin.cases σ0 (Fin.cases σ1 (Fin.cases σ2 finZeroElim))

@[simp] theorem threeBlockSmoothFamily_zero
    (σ0 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear C F))
    (σ1 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear A F))
    (σ2 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear B F)) :
    threeBlockSmoothFamily σ0 σ1 σ2 0 = σ0 := rfl

@[simp] theorem threeBlockSmoothFamily_one
    (σ0 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear C F))
    (σ1 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear A F))
    (σ2 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear B F)) :
    threeBlockSmoothFamily σ0 σ1 σ2 1 = σ1 := rfl

@[simp] theorem threeBlockSmoothFamily_two
    (σ0 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear C F))
    (σ1 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear A F))
    (σ2 : SmoothRep.{0,uF,uV} ℂ (GeneralLinear B F)) :
    threeBlockSmoothFamily σ0 σ1 σ2 2 = σ2 := rfl

end Langlands.Parabolic
