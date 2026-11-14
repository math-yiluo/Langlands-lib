import Langlands.Representation.Parabolic.RegroupingFactorEquivalences
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.Induction.SingleBlockSupplement
import Langlands.AllField.Representation.Shahidi.Induction
import Langlands.AllField.Representation.Tensor.GLRefinement
/-! Factor identifications for the literal three-block regrouping consumer. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.FiniteTensor
open Langlands.FiniteTensor hiding glRefinementEquiv glRefinementLinearEquiv glRefinementLinearEquiv_tprod rankCastLinearEquiv rankCastLinearEquiv_action rankCastRepresentationEquiv
open Langlands.AllField.FiniteTensor

open Langlands.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The published rank-transport linear map as an actual representation equivalence. -/
def rankCastRepresentationEquiv {r s : ℕ} (h : r = s) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear s F),
      Representation.Equiv
        (A.representation.comp (reindex (R := F) (finCongr h)).toMonoidHom)
        (h.symm ▸ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F)).representation := by
  letI := T.topology
  intro A
  refine Representation.Equiv.mk (rankCastLinearEquiv F T h A) ?_
  intro g
  ext v
  exact rankCastLinearEquiv_action F T h A g v

end Langlands.AllField.FiniteTensor

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

set_option maxHeartbeats 800000 in
/-- A one-block product of the canonically transported factor evaluates to that factor. -/
def singleBlockTransportedProductEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F),
      Representation.Equiv
        (T.normalizedProductInduced B (fun i =>
          (B.singleBlock_size hB i |>.symm ▸ A :
            SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F)).representation))
        A.representation := by
  letI := T.topology
  intro A
  let i := B.singleBlockIndex hB
  let h := B.singleBlock_size hB i
  let e := GeneralLinear.reindex (R := F) (finCongr h)
  let δ := T.singleBlockNormalizedProductEquiv B hB
    (fun j => ((B.singleBlock_size hB j).symm ▸ A :
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size j) F)).representation)
    (fun j => SmoothRep.isSmooth _) i
  let ε := (Langlands.AllField.FiniteTensor.rankCastRepresentationEquiv F T h A).symm.precomp
    e.symm.toMonoidHom
  let E := δ.trans ε
  refine Representation.Equiv.mk E.toLinearEquiv ?_
  intro g
  have hE := E.isIntertwining' g
  simpa only [e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using hE

end Langlands.LocalFieldData

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic
open Langlands.AllField.Parabolic

universe uF uV


end Langlands.AllField.Parabolic
