import Langlands.Representation.Tensor.GLRefinement
import Langlands.Representation.Geometric.FlattenedLevi

/-! Flattened GL tensor regrouping over the actual flattened product Levi. -/

noncomputable section
set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.FiniteTensor

open GeneralLinear Geometric

universe uR uF uV

/-- Cancel one group pullback while retaining a prescribed composite homomorphism. -/
private def cancelGroupPullback
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

theorem nestedLeviEquiv_flatten (R : Type uR) [CommRing R]
    {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B) :
    (B.flatten Q).nestedLeviEquiv B Q (B.flattenBlockEquiv Q)
        (fun a => (B.flatten_size_flattenBlockEquiv Q a).symm) R =
      flattenedLeviProductEquiv R B Q := by
  apply MulEquiv.ext
  intro m
  funext i j
  rw [BlockShape.nestedLeviEquiv_apply, flattenedLeviProductEquiv_apply]

theorem leviRefinementEquiv_flatten (R : Type uR) [CommRing R]
    {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B) :
    (B.flatten Q).leviRefinementEquiv B Q (B.flattenBlockEquiv Q)
        (fun a => (B.flatten_size_flattenBlockEquiv Q a).symm) R =
      flattenedLeviEquiv R B Q := by
  rw [BlockShape.leviRefinementEquiv, nestedLeviEquiv_flatten]
  rfl

theorem flattenedGroupComposite_apply (R : Type uR) [CommRing R]
    {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)
    (g : (B.flatten Q).Levi R) :
    (refinedLeviEquiv R B Q).symm
        ((B.flatten Q).leviRefinementEquiv B Q (B.flattenBlockEquiv Q)
          (fun a => (B.flatten_size_flattenBlockEquiv Q a).symm) R g) =
      flattenedLeviProductEquiv R B Q g := by
  rw [leviRefinementEquiv_flatten]
  exact (refinedLeviEquiv R B Q).symm_apply_apply _

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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

end Langlands.FiniteTensor
