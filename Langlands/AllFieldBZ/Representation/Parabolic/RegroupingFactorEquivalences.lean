import Langlands.AllFieldBZ.Group.GL.UnramifiedCharacter
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredientStatement
import Langlands.AllFieldBZ.Representation.Induction.BlockEquivalence
import Langlands.AllFieldBZ.Representation.Induction.SingleBlock
import Langlands.AllFieldBZ.Representation.Shahidi.TwoBlocks
import Langlands.AllFieldBZ.Representation.Tensor.GLRefinement
import Langlands.Representation.Parabolic.RegroupingFactorEquivalences

/-!
# All-field port of `Langlands.Representation.Parabolic.RegroupingFactorEquivalences`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RegroupingFactorEquivalences` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.FiniteTensor
open Langlands.FiniteTensor hiding glRefinementEquiv glRefinementEquiv_symm_tprod glRefinementEquiv_toLinearEquiv glRefinementEquiv_tprod glRefinementLinearEquiv glRefinementLinearEquiv_tprod rankCastLinearEquiv rankCastLinearEquiv_action rankCastRepresentationEquiv
open Langlands.GeneralLinear
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

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

end Langlands.AllFieldBZ.FiniteTensor
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV

variable {F : LocalFieldPackage.{uF}}
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

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic
universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] {C A B : ℕ}

end Langlands.AllFieldBZ.Parabolic
