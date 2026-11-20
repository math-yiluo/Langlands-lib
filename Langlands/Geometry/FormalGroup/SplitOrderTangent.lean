import Langlands.Geometry.FormalGroup.TangentCharacters
import Mathlib.Algebra.Algebra.Opposite

/-! # The division-order tangent summand of a split formal module -/

noncomputable section

universe u v w z q

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {B : Type v} [Ring B] [Algebra O B]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable {L : Type q} [CommRing L]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable (E : OrderAction (Bᵐᵒᵖ × B) M) {E' : OrderAction (Bᵐᵒᵖ × B) N}

/-- The actual tangent idempotent projecting onto the division-order factor. -/
def divisionTangentProjector (φ : R →+* L) : Module.End L (σ → L) :=
  E.fiberTangent φ (0, 1)

/-- The tangent summand cut out by the actual second central idempotent. -/
def divisionTangent (φ : R →+* L) : Submodule L (σ → L) :=
  LinearMap.range (E.divisionTangentProjector φ)

private theorem divisionTangentProjector_act (φ : R →+* L) (b : B) (x : σ → L) :
    E.divisionTangentProjector φ (E.fiberTangent φ (0, b) x) = E.fiberTangent φ (0, b) x := by
  change (E.fiberTangent φ (0, 1) * E.fiberTangent φ (0, b)) x = _
  rw [← _root_.map_mul]
  simp

/-- Differentiating the order idempotent gives an idempotent tangent map. -/
theorem divisionTangentProjector_comp (φ : R →+* L) :
    (E.divisionTangentProjector φ).comp (E.divisionTangentProjector φ) =
      E.divisionTangentProjector φ :=
  LinearMap.ext (E.divisionTangentProjector_act φ 1)

/-- The projector acts as the identity on its own actual image. -/
theorem divisionTangentProjector_apply (φ : R →+* L) (x : E.divisionTangent φ) :
    E.divisionTangentProjector φ x = (x : σ → L) := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact E.divisionTangentProjector_act φ 1 y

/-- The division tangent vectors are precisely the fixed vectors of the projector. -/
theorem mem_divisionTangent_iff (φ : R →+* L) (x : σ → L) :
    x ∈ E.divisionTangent φ ↔ E.divisionTangentProjector φ x = x :=
  ⟨fun h => E.divisionTangentProjector_apply φ ⟨x, h⟩, fun h => ⟨x, h⟩⟩

set_option maxHeartbeats 800000 in
/-- Restrict the actual tangent action to the image of the division-order projector. -/
def divisionTangentAction (φ : R →+* L) : B →+* Module.End L (E.divisionTangent φ) where
  toFun b := LinearMap.codRestrict _ ((E.fiberTangent φ (0, b)).comp (Submodule.subtype _))
    (fun x => ⟨E.fiberTangent φ (0, b) x, E.divisionTangentProjector_act φ b x⟩)
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change E.fiberTangent φ (0 : Bᵐᵒᵖ × B) x = 0
    rw [_root_.map_zero, LinearMap.zero_apply]
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact E.divisionTangentProjector_apply φ x
  map_add' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change E.fiberTangent φ (0, b + c) x =
      E.fiberTangent φ (0, b) x + E.fiberTangent φ (0, c) x
    have h : ((0, b) : Bᵐᵒᵖ × B) + (0, c) = (0, b + c) := Prod.ext (zero_add 0) rfl
    exact LinearMap.congr_fun ((congrArg (E.fiberTangent φ) h.symm).trans
      (_root_.map_add (E.fiberTangent φ) _ _)) x
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change E.fiberTangent φ (0, b * c) x =
      (E.fiberTangent φ (0, b) * E.fiberTangent φ (0, c)) x
    have h : ((0, b) : Bᵐᵒᵖ × B) * (0, c) = (0, b * c) := Prod.ext (zero_mul 0) rfl
    exact LinearMap.congr_fun ((congrArg (E.fiberTangent φ) h.symm).trans
      (_root_.map_mul (E.fiberTangent φ) _ _)) x

@[simp]
theorem divisionTangentAction_val (φ : R →+* L) (b : B) (x : E.divisionTangent φ) :
    (E.divisionTangentAction φ b x : σ → L) = E.fiberTangent φ (0, b) x := rfl

namespace Hom

variable {E}

/-- Derivatives of order-linear maps restrict to maps between the actual summands. -/
def divisionTangentMap (f : Hom E E') (φ : R →+* L) :
    E.divisionTangent φ →ₗ[L] E'.divisionTangent φ :=
  LinearMap.codRestrict _ ((f.val.fiberTangent φ).comp (Submodule.subtype _)) (fun x => by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨f.val.fiberTangent φ y, ?_⟩
    change E'.fiberTangent φ (0, 1) (f.val.fiberTangent φ y) = f.val.fiberTangent φ x
    exact (LinearMap.congr_fun (f.fiberTangent_commutes φ (0, 1)) y).symm.trans
      (congrArg (f.val.fiberTangent φ) hy))

@[simp]
theorem divisionTangentMap_val (f : Hom E E') (φ : R →+* L) (x : E.divisionTangent φ) :
    (f.divisionTangentMap φ x : τ → L) = f.val.fiberTangent φ x := rfl

/-- The restricted tangent map intertwines the division-order actions. -/
theorem divisionTangentMap_commutes (f : Hom E E') (φ : R →+* L) (b : B)
    (x : E.divisionTangent φ) :
    f.divisionTangentMap φ (E.divisionTangentAction φ b x) =
      E'.divisionTangentAction φ b (f.divisionTangentMap φ x) :=
  Subtype.ext (LinearMap.congr_fun (f.fiberTangent_commutes φ (0, b)) (x : σ → L))

end Hom

namespace Iso

variable {E}

/-- An actual order isomorphism induces an invertible derivative on the summands. -/
def divisionTangentEquiv (e : Iso E E') (φ : R →+* L) :
    E.divisionTangent φ ≃ₗ[L] E'.divisionTangent φ :=
  { e.hom.divisionTangentMap φ with
    invFun := e.inv.divisionTangentMap φ
    left_inv := fun x => Subtype.ext ((e.toModuleIso.fiberTangent φ).left_inv (x : σ → L))
    right_inv := fun x => Subtype.ext ((e.toModuleIso.fiberTangent φ).right_inv (x : τ → L)) }

/-- The comparison induced by an order isomorphism is division-order linear. -/
theorem divisionTangentEquiv_commutes (e : Iso E E') (φ : R →+* L) (b : B)
    (x : E.divisionTangent φ) :
    e.divisionTangentEquiv φ (E.divisionTangentAction φ b x) =
      E'.divisionTangentAction φ b (e.divisionTangentEquiv φ x) :=
  e.hom.divisionTangentMap_commutes φ b x

end Iso

/-- Taking the division summand at a point after pullback uses the composite point. -/
theorem divisionTangent_map (θ : R →ₐ[O] S) (φ : S →+* L) :
    (E.map θ).divisionTangent φ = E.divisionTangent (φ.comp θ.toRingHom) := by
  unfold divisionTangent divisionTangentProjector
  rw [fiberTangent_map]

/-- Coefficient comparison is the identity on the actual summand vectors. -/
def divisionTangentBaseChangeEquiv (θ : R →ₐ[O] S) (φ : S →+* L) :
    (E.map θ).divisionTangent φ ≃ₗ[L] E.divisionTangent (φ.comp θ.toRingHom) :=
  LinearEquiv.ofEq _ _ (E.divisionTangent_map θ φ)

/-- The coefficient comparison intertwines the induced division-order actions. -/
theorem divisionTangentBaseChangeEquiv_commutes (θ : R →ₐ[O] S) (φ : S →+* L)
    (b : B) (x : (E.map θ).divisionTangent φ) :
    E.divisionTangentBaseChangeEquiv θ φ ((E.map θ).divisionTangentAction φ b x) =
      E.divisionTangentAction (φ.comp θ.toRingHom) b (E.divisionTangentBaseChangeEquiv θ φ x) := by
  apply Subtype.ext
  change (E.map θ).fiberTangent φ (0, b) x = E.fiberTangent (φ.comp θ.toRingHom) (0, b) x
  rw [fiberTangent_map]

end Langlands.FormalGroup.ModuleLaw.OrderAction
