import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Induction.SplitQuotientStatement

/-! Smooth induction in stages, with its coefficient naturality. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable (H P : Subgroup G) (hHP : H ≤ P)
variable (σ : Representation R H V)

local notation "HP" => H.subgroupOf P
local notation "φ" => (MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP))
local notation "σP" => σ.comp φ
local notation "ρP" => smoothInduced HP σP

omit [IsTopologicalGroup G] in
private theorem smooth_ext (f g : SmoothFunctions H σ)
    (he : ∀ x, eval H σ f x = eval H σ g x) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact funext he

private def smoothStageInner (f : SmoothFunctions H σ) (x : G) :
    SmoothFunctions HP σP := by
  let K := f.property.choose
  have hK := f.property.choose_spec
  refine smoothFunctionOf HP σP (fun p => eval H σ f ((p : G) * x))
    (fun h p => ?_) (conjOpenSubgroup P K x) (fun k p => ?_)
  · change eval H σ f (((h : P) : G) * (p : G) * x) =
      σ (φ h) (eval H σ f ((p : G) * x))
    have hh : ((φ h : H) : G) = ((h : P) : G) := rfl
    simpa only [mul_assoc, hh] using
      eval_covariant H σ f (φ h) ((p : G) * x)
  · have hk : x⁻¹ * ((k : P) : G) * x ∈ K := mem_conjOpenSubgroup.mp k.property
    have he := congrArg (fun F : EquivariantFunctions H σ => F.val ((p : G) * x))
      (hK ⟨_, hk⟩)
    change eval H σ f (((p : G) * x) * (x⁻¹ * ((k : P) : G) * x)) =
      eval H σ f ((p : G) * x) at he
    change eval H σ f ((((p : P) : G) * ((k : P) : G)) * x) =
      eval H σ f ((p : G) * x)
    simpa only [eval, mul_assoc, mul_inv_cancel_left] using he

@[simp] private theorem smoothStageInner_eval (f : SmoothFunctions H σ) (x : G) (p : P) :
    eval HP σP (smoothStageInner H P hHP σ f x) p =
      eval H σ f ((p : G) * x) := rfl

private def smoothStageExpand (f : SmoothFunctions H σ) :
    SmoothFunctions P ρP := by
  let K := f.property.choose
  have hK := f.property.choose_spec
  refine smoothFunctionOf P ρP (smoothStageInner H P hHP σ f)
    (fun p x => ?_) K (fun k x => ?_)
  · apply smooth_ext
    intro q
    change eval HP σP (smoothStageInner H P hHP σ f ((p : G) * x)) q =
      eval HP σP (smoothStageInner H P hHP σ f x) (q * p)
    simp only [smoothStageInner_eval, Subgroup.coe_mul, mul_assoc]
  · apply smooth_ext
    intro p
    simp only [smoothStageInner_eval]
    have he := congrArg (fun F : EquivariantFunctions H σ => F.val ((p : G) * x)) (hK k)
    change eval H σ f (((p : G) * x) * (k : G)) =
      eval H σ f ((p : G) * x) at he
    simpa only [mul_assoc] using he

@[simp] private theorem smoothStageExpand_eval (f : SmoothFunctions H σ) (x : G) :
    eval P ρP (smoothStageExpand H P hHP σ f) x =
      smoothStageInner H P hHP σ f x := rfl

private def smoothStageFlatten (F : SmoothFunctions P ρP) : SmoothFunctions H σ := by
  let K := F.property.choose
  have hK := F.property.choose_spec
  refine smoothFunctionOf H σ
    (fun x => eval HP σP (eval P ρP F x) 1) (fun h x => ?_)
    K (fun k x => ?_)
  · let p : P := ⟨h, hHP h.property⟩
    rw [show (h : G) = (p : G) from rfl, eval_covariant]
    change eval HP σP (eval P ρP F x) (1 * p) =
      σ h (eval HP σP (eval P ρP F x) 1)
    simpa [MonoidHom.comp_apply, Subgroup.subgroupOfEquivOfLe, p] using
      eval_covariant HP σP (eval P ρP F x) ⟨p, h.property⟩ 1
  · exact congrArg (fun F' : EquivariantFunctions P ρP =>
      eval HP σP (F'.val x) 1) (hK k)

@[simp] private theorem smoothStageFlatten_eval (F : SmoothFunctions P ρP) (x : G) :
    eval H σ (smoothStageFlatten H P hHP σ F) x =
      eval HP σP (eval P ρP F x) 1 := rfl

/-- Evaluation at the inner identity gives smooth induction in stages.
No closedness or local compactness hypothesis is needed. -/
def smoothStagesEquiv : Representation.Equiv (smoothInduced P ρP) (smoothInduced H σ) where
  toFun := smoothStageFlatten H P hHP σ
  invFun := smoothStageExpand H P hHP σ
  map_add' F F' := by
    apply smooth_ext
    intro x
    rfl
  map_smul' a F := by
    apply smooth_ext
    intro x
    rfl
  left_inv F := by
    apply smooth_ext
    intro x
    change smoothStageInner H P hHP σ (smoothStageFlatten H P hHP σ F) x =
      eval P ρP F x
    apply smooth_ext
    intro p
    simp only [smoothStageInner_eval, smoothStageFlatten_eval, eval_covariant]
    change eval HP σP (eval P ρP F x) (1 * p) =
      eval HP σP (eval P ρP F x) p
    rw [one_mul]
  right_inv f := by
    apply smooth_ext
    intro x
    change eval HP σP (smoothStageInner H P hHP σ f x) 1 = eval H σ f x
    simp only [smoothStageInner_eval, Subgroup.coe_one, one_mul]
  isIntertwining' g := by
    apply LinearMap.ext
    intro F
    apply smooth_ext
    intro x
    rfl

@[simp] theorem smoothStagesEquiv_eval (F : SmoothFunctions P ρP) (x : G) :
    eval H σ (smoothStagesEquiv H P hHP σ F) x =
      eval HP σP (eval P ρP F x) 1 := rfl

@[simp] theorem smoothStagesEquiv_symm_eval (f : SmoothFunctions H σ) (x : G) (p : P) :
    eval HP σP (eval P ρP ((smoothStagesEquiv H P hHP σ).symm f) x) p =
      eval H σ f ((p : G) * x) := rfl

variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The stages equivalence commutes with coefficient intertwiners, also between
independently sized coefficient modules. -/
theorem smoothStagesEquiv_natural {τ : Representation R H W} (T : σ.IntertwiningMap τ)
    (F : SmoothFunctions P ρP) :
    smoothStagesEquiv H P hHP τ
      (smoothInducedMap P (smoothInducedMap HP (restrictAlongMap φ T)) F) =
    smoothInducedMap H T (smoothStagesEquiv H P hHP σ F) := by
  apply smooth_ext
  intro x
  rfl

end Langlands.Induction
