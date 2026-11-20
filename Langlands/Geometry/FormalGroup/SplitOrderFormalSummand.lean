import Langlands.Geometry.FormalGroup.FormalIdempotentImage
import Langlands.Geometry.FormalGroup.SplitOrderTangent

/-! # The formal division summand of a split order action -/

noncomputable section

universe u v w q

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {B : Type v} [Ring B] [Algebra O B]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {K : Type q} [CommRing K]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable (E : OrderAction (Bᵐᵒᵖ × B) M)

/-- The formal endomorphism induced by the central idempotent of the division factor. -/
def divisionProjector : ModuleLaw.Hom M M := E.action (0, 1)

@[simp]
theorem divisionProjector_comp_action (b : B) :
    E.divisionProjector.comp (E.action (0, b)) = E.action (0, b) := by
  change E.action (0, 1) * E.action (0, b) = E.action (0, b)
  rw [← map_mul]
  exact congrArg E.action (Prod.ext (zero_mul 0) (one_mul b))

@[simp]
theorem action_comp_divisionProjector (b : B) :
    (E.action (0, b)).comp E.divisionProjector = E.action (0, b) := by
  change E.action (0, b) * E.action (0, 1) = E.action (0, b)
  rw [← map_mul]
  exact congrArg E.action (Prod.ext (zero_mul 0) (mul_one b))

theorem divisionProjector_comp :
    E.divisionProjector.comp E.divisionProjector = E.divisionProjector :=
  E.divisionProjector_comp_action 1

/-- A finite-coordinate presentation of the image of the actual division projector. -/
abbrev DivisionImage (N : ModuleLaw O R τ) :=
  ModuleLaw.Hom.IdempotentImage E.divisionProjector N

namespace DivisionImage

variable {E}

private theorem restrictHom_scalar (A : E.DivisionImage N) (a : O) :
    A.restrictHom A (E.action (0, algebraMap O B a)) = N.scalarHom a := by
  have h : (0, algebraMap O B a) =
      ((0, 1) : Bᵐᵒᵖ × B) * algebraMap O (Bᵐᵒᵖ × B) a :=
    Prod.ext (zero_mul _).symm (one_mul _).symm
  have hs : E.action (algebraMap O (Bᵐᵒᵖ × B) a) = M.scalarHom a := by
    apply ModuleLaw.Hom.ext
    rw [E.extends_scalars, scalarHom, ModuleLaw.Hom.smul_toHom]
    exact (CommLaw.Hom.comp_id _).symm
  rw [h, map_mul, hs]
  change A.projection.comp
    ((E.divisionProjector.comp (a • ModuleLaw.Hom.id M)).comp A.inclusion) = _
  rw [ModuleLaw.Hom.comp_smul, ModuleLaw.Hom.comp_id, ModuleLaw.Hom.smul_comp,
    ModuleLaw.Hom.comp_smul, A.projector_inclusion, A.projection_inclusion, scalarHom]

/-- The division order acts on its image by restricting the endomorphisms `(0,b)`. -/
def order (A : E.DivisionImage N) : OrderAction B N where
  action := {
    toFun b := A.restrictHom A (E.action (0, b))
    map_zero' := by
      change A.restrictHom A (E.action (0 : Bᵐᵒᵖ × B)) = 0
      rw [map_zero]
      simp [ModuleLaw.Hom.IdempotentImage.restrictHom]
    map_one' := by
      change A.projection.comp (E.divisionProjector.comp A.inclusion) = ModuleLaw.Hom.id N
      rw [A.projector_inclusion, A.projection_inclusion]
    map_add' b c := by
      change A.restrictHom A (E.action (0, b + c)) =
        A.restrictHom A (E.action (0, b)) + A.restrictHom A (E.action (0, c))
      rw [show (0, b + c) = ((0, b) : Bᵐᵒᵖ × B) + (0, c) from Prod.ext (zero_add 0).symm rfl,
        map_add]
      simp only [ModuleLaw.Hom.IdempotentImage.restrictHom,
        ModuleLaw.Hom.add_comp, ModuleLaw.Hom.comp_add]
    map_mul' b c := by
      change A.restrictHom A (E.action (0, b * c)) =
        (A.restrictHom A (E.action (0, b))).comp (A.restrictHom A (E.action (0, c)))
      rw [show (0, b * c) = ((0, b) : Bᵐᵒᵖ × B) * (0, c) from Prod.ext (zero_mul 0).symm rfl,
        map_mul]
      exact A.restrictHom_comp A A _ _ (by simp)
  }
  extends_scalars a := by
    change (A.restrictHom A (E.action (0, algebraMap O B a))).toHom = N.action a
    rw [A.restrictHom_scalar, scalarHom, ModuleLaw.Hom.smul_toHom]
    exact CommLaw.Hom.comp_id _

/-- The derivative of the inclusion identifies the image tangent with the
division tangent cut out on the ambient formal module. -/
def tangentEquiv (A : E.DivisionImage N) (φ : R →+* K) :
    (τ → K) ≃ₗ[K] E.divisionTangent φ where
  toFun x := ⟨A.inclusion.fiberTangent φ x, (E.mem_divisionTangent_iff φ _).2 (by
    change E.divisionProjector.fiberTangent φ (A.inclusion.fiberTangent φ x) =
      A.inclusion.fiberTangent φ x
    have h := congrArg (fun f : ModuleLaw.Hom N M => f.fiberTangent φ x) A.projector_inclusion
    simpa only [ModuleLaw.Hom.fiberTangent_comp, LinearMap.comp_apply] using h)⟩
  invFun x := A.projection.fiberTangent φ x
  left_inv x := by
    have h := congrArg (fun f : ModuleLaw.Hom N N => f.fiberTangent φ x) A.projection_inclusion
    simpa only [ModuleLaw.Hom.fiberTangent_comp, ModuleLaw.Hom.fiberTangent_id,
      LinearMap.comp_apply, LinearMap.id_apply] using h
  right_inv x := by
    apply Subtype.ext
    have h := congrArg (fun f : ModuleLaw.Hom M M => f.fiberTangent φ (x : σ → K))
      A.inclusion_projection
    simp only [ModuleLaw.Hom.fiberTangent_comp, LinearMap.comp_apply] at h
    have hx := E.divisionTangentProjector_apply φ x
    change E.divisionProjector.fiberTangent φ x = (x : σ → K) at hx
    exact h.trans hx
  map_add' x y := Subtype.ext ((A.inclusion.fiberTangent φ).map_add x y)
  map_smul' a x := Subtype.ext ((A.inclusion.fiberTangent φ).map_smul a x)

theorem tangentEquiv_commutes (A : E.DivisionImage N) (φ : R →+* K) (b : B) (x : τ → K) :
    A.tangentEquiv φ (A.order.fiberTangent φ b x) =
      E.divisionTangentAction φ b (A.tangentEquiv φ x) := by
  apply Subtype.ext
  change A.inclusion.fiberTangent φ ((A.restrictHom A (E.action (0, b))).fiberTangent φ x) =
    (E.action (0, b)).fiberTangent φ (A.inclusion.fiberTangent φ x)
  have h := A.inclusion_restrictHom A (E.action (0, b)) (by simp)
  have hx := congrArg (fun f : ModuleLaw.Hom N M => f.fiberTangent φ x) h
  simpa only [ModuleLaw.Hom.fiberTangent_comp, LinearMap.comp_apply] using hx

end DivisionImage

end Langlands.FormalGroup.ModuleLaw.OrderAction
