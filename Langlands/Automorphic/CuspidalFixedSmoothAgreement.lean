import Langlands.Automorphic.OperatorFixedJointVectorRecovery
import Langlands.Representation.Archimedean.SmoothAction

/-! # Continuous agreement on the original fixed smooth image -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

open scoped Manifold ContDiff

namespace Langlands.Archimedean.SmoothInvariantSubspace

universe uG uV uA uGarch uE

variable {G : Type uG} [Group G] {V : Type uV}
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {Garch : Type uGarch} [Group Garch] [TopologicalSpace Garch] [ChartedSpace A Garch]
  [LieGroup 𝓘(ℝ, A) ∞ Garch]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : G →* (E →L[ℂ] E)) (J : Subgroup G) (π : Garch →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation "VJ" => ambientFixedSmoothSubspace σ J π I

/-- Fixed derivative smooth vectors whose smooth representatives are in the
image of the supplied map. -/
def fixedSmoothImageOf (j : V → smoothVectors I π) : Set VJ :=
  {w | DerivativeSmoothVectors.toSmooth I π w.val ∈ Set.range j}

/-- Continuous functions on the fixed smooth space agree when they agree
on a dense image of original vectors. -/
theorem eqOn_fixedSmoothImageOf (j : V → smoothVectors I π)
    (hd : Dense (fixedSmoothImageOf σ J π j))
    {f g : DerivativeSmoothVectors I π → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ v, f ((DerivativeSmoothVectors.toSmooth I π).symm (j v)) =
      g ((DerivativeSmoothVectors.toSmooth I π).symm (j v))) (w : VJ) : f w.val = g w.val := by
  have hfg : Set.EqOn (fun x : VJ => f x.val) (fun x => g x.val)
      (fixedSmoothImageOf σ J π j) := by
    rintro x ⟨v, hv⟩
    have he := congrArg (⇑(DerivativeSmoothVectors.toSmooth I π).symm) hv
    change f x.val = g x.val
    rw [LinearEquiv.symm_apply_apply] at he
    rw [← he]
    exact h v
  exact hfg.closure (hf.comp continuous_subtype_val) (hg.comp continuous_subtype_val) (hd w)

/-- A covariance identity for a fixed archimedean element extends from
the dense image to every fixed genuine smooth vector. -/
theorem covarianceOn_fixedSmoothImageOf (j : V → smoothVectors I π)
    (hd : Dense (fixedSmoothImageOf σ J π j))
    (L : smoothVectors I π →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L)
    (a : Garch) (c : ℂ) (h : ∀ v, L (smoothRepresentation I π a (j v)) = c * L (j v))
    (w : smoothVectors I π) (hw : w.val ∈ fixedSubspace σ J) :
    L (smoothRepresentation I π a w) = c * L w := by
  let f := fun x : DerivativeSmoothVectors I π => L (DerivativeSmoothVectors.toSmooth I π x)
  have hf : Continuous f := continuous_of_isContinuousOnSmoothVectors I π L hL
  let x := (DerivativeSmoothVectors.toSmooth I π).symm w
  have hx : x ∈ VJ := (mem_ambientSmoothSubspace π (fixedSubspace σ J) I x).mpr
    (by simpa only [x, LinearEquiv.apply_symm_apply] using hw)
  have he := eqOn_fixedSmoothImageOf σ J π j hd
    (f := f ∘ SmoothAction.derivativeAction I π a) (g := fun x => c * f x)
    (hf.comp (SmoothAction.derivativeAction I π a).continuous) (continuous_const.mul hf)
    (by
      intro v
      simpa only [Function.comp_apply, f, SmoothAction.toSmooth_derivativeAction,
        LinearEquiv.apply_symm_apply] using h v) ⟨x, hx⟩
  simpa only [Function.comp_apply, f, SmoothAction.toSmooth_derivativeAction,
    x, LinearEquiv.apply_symm_apply] using he

end Langlands.Archimedean.SmoothInvariantSubspace

namespace Langlands.Automorphic.OperatorUnitaryFormCore

open Langlands.Archimedean Langlands.Archimedean.SmoothInvariantSubspace

universe uG uK uV uX uA uGarch

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} {ρ : Representation ℂ G V} {κ : Representation ℂ K V}
  {D : X → Module.End ℂ V}
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {Garch : Type uGarch} [Group Garch] [TopologicalSpace Garch] [ChartedSpace A Garch]
  [LieGroup 𝓘(ℝ, A) ∞ Garch] (b : OperatorUnitaryFormCore ρ κ D)
  (σ : G →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion)) (J : OpenSubgroup G)
  (π : Garch →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion))

local notation "I" => 𝓘(ℝ, A)

/-- Density formulated by canonical Hilbert preimages implies density
formulated by a supplied smooth representative of each canonical preimage. -/
theorem dense_fixedSmoothImageOf (hd : Dense (fixedSmoothImage (A := A) b σ J π))
    (j : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
    (hj : ∀ w : V, (j w).val = b.toHilbert w) :
    Dense (fixedSmoothImageOf σ J.toSubgroup π
      (fun v : Langlands.fixedVectors ρ J.toSubgroup => j v.val)) := by
  refine hd.mono ?_
  rintro w ⟨v, hv⟩
  exact ⟨v, Subtype.ext ((hj v.val).trans hv)⟩

end Langlands.Automorphic.OperatorUnitaryFormCore
