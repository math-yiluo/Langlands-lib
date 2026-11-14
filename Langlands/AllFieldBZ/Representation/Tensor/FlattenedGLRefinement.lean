import Langlands.AllFieldBZ.Representation.Geometric.FlattenedLevi
import Langlands.AllFieldBZ.Representation.Tensor.GLRefinement
import Langlands.Representation.Tensor.FlattenedGLRefinement

/-!
# All-field port of `Langlands.Representation.Tensor.FlattenedGLRefinement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Tensor.FlattenedGLRefinement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.FiniteTensor
open Langlands.FiniteTensor hiding flattenedTensorRegroupEquiv glRefinementEquiv glRefinementEquiv_symm_tprod glRefinementEquiv_toLinearEquiv glRefinementEquiv_tprod glRefinementLinearEquiv glRefinementLinearEquiv_tprod rankCastLinearEquiv rankCastLinearEquiv_action
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uR uF uV

/-- Cancel one group pullback while retaining a prescribed composite homomorphism. -/
private def _root_.Langlands.FiniteTensor.cancelGroupPullback
    {G H K : Type*} [Group G] [Group H] [Group K]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W}
    (e : G ≃* K) (f : H ≃* K)
    (E : Representation.Equiv (ρ.comp e.symm.toMonoidHom)
      (σ.comp f.symm.toMonoidHom))
    (φ : G →* H) (hφ : ∀ g, f.symm (e g) = φ g) :
    Representation.Equiv ρ (σ.comp φ) :=
  Representation.Equiv.mk E.toLinearEquiv fun g => by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hφ] using E.isIntertwining' (e g)

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)

/-- The published rank-aware comparison, now over the flattened group itself. -/
def flattenedTensorRegroupEquiv
    (A : letI := T.topology
      ∀ k : Fin (B.flatten Q).length,
        SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((B.flatten Q).size k) F.Carrier)) :=
  letI := T.topology
  cancelGroupPullback
    ((B.flatten Q).leviRefinementEquiv B Q (B.flattenBlockEquiv Q)
      (fun a => (B.flatten_size_flattenBlockEquiv Q a).symm) F.Carrier)
    (refinedLeviEquiv F.Carrier B Q)
    (FiniteTensor.glRefinementEquiv F T (B.flatten Q) B Q
      (B.flattenBlockEquiv Q)
      (fun a => (B.flatten_size_flattenBlockEquiv Q a).symm) A)
    (flattenedLeviProductEquiv F.Carrier B Q).toMonoidHom
    (flattenedGroupComposite_apply F.Carrier B Q)

end Langlands.AllFieldBZ.FiniteTensor
