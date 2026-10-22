import Langlands.Group.GL.Blocks
import Langlands.Representation.Jacquet.Coinvariants

namespace Langlands.Parabolic

universe uF uR uV uW uX

variable {F : Type uF} [CommRing F] {R : Type uR} [CommRing R]
    {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Type uV} {W : Type uW} {X : Type uX}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup X] [Module R X]

/-- Inflate an actual product-Levi action along the block projection. -/
abbrev inflate (σ : Representation R (B.Levi F) V) :
    Representation R (B.parabolic F) V :=
  σ.comp (B.leviProjection F)

/-- Inflation leaves the underlying linear intertwiner unchanged. -/
def inflateMap {σ : Representation R (B.Levi F) V}
    {τ : Representation R (B.Levi F) W} (f : σ.IntertwiningMap τ) :
    (inflate B σ).IntertwiningMap (inflate B τ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (B.leviProjection F g)

@[simp] theorem inflateMap_apply {σ : Representation R (B.Levi F) V}
    {τ : Representation R (B.Levi F) W} (f : σ.IntertwiningMap τ) (v : V) :
    inflateMap B f v = f v := rfl

@[simp] theorem inflate_radical (σ : Representation R (B.Levi F) V)
    (u : B.unipotentRadical F) (v : V) :
    inflate B σ u.val v = v := by
  change σ (B.leviProjection F u.val) v = v
  rw [show B.leviProjection F u.val = 1 from u.property]
  simp

/-- The actual radical quotient of a representation of the parabolic. -/
abbrev LeviCoinvariants (ρ : Representation R (B.parabolic F) V) :=
  Representation.Coinvariants (ρ.comp (B.unipotentRadical F).subtype)

/-- The product Levi acts on the radical quotient through its actual section.
This is the unnormalized action. -/
noncomputable def leviCoinvariants (ρ : Representation R (B.parabolic F) V) :
    Representation R (B.Levi F) (LeviCoinvariants B ρ) :=
  (Representation.toCoinvariants ρ (B.unipotentRadical F)).comp
    (B.leviInParabolic F)

@[simp] theorem leviCoinvariants_mk (ρ : Representation R (B.parabolic F) V)
    (m : B.Levi F) (v : V) :
    leviCoinvariants B ρ m (Jacquet.mk ρ (B.unipotentRadical F) v) =
      Jacquet.mk ρ (B.unipotentRadical F) (ρ (B.leviInParabolic F m) v) := rfl

/-- An actual parabolic intertwiner descends to a Levi intertwiner. -/
noncomputable def leviCoinvariantsMap
    {ρ : Representation R (B.parabolic F) V}
    {σ : Representation R (B.parabolic F) W} (f : ρ.IntertwiningMap σ) :
    (leviCoinvariants B ρ).IntertwiningMap (leviCoinvariants B σ) where
  toLinearMap := Representation.Coinvariants.map _ _
    (Jacquet.restrictMap f (B.unipotentRadical F))
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change Jacquet.mk σ _ (f (ρ (B.leviInParabolic F m) v)) =
      Jacquet.mk σ _ (σ (B.leviInParabolic F m) (f v))
    exact congrArg (Jacquet.mk σ _)
      (Representation.IntertwiningMap.isIntertwining ρ σ f _ v)

@[simp] theorem leviCoinvariantsMap_mk
    {ρ : Representation R (B.parabolic F) V}
    {σ : Representation R (B.parabolic F) W} (f : ρ.IntertwiningMap σ) (v : V) :
    leviCoinvariantsMap B f (Jacquet.mk ρ (B.unipotentRadical F) v) =
      Jacquet.mk σ (B.unipotentRadical F) (f v) := rfl

@[simp] theorem leviCoinvariantsMap_id (ρ : Representation R (B.parabolic F) V) :
    leviCoinvariantsMap B (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (leviCoinvariants B ρ) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

@[simp] theorem leviCoinvariantsMap_comp
    {ρ : Representation R (B.parabolic F) V}
    {σ : Representation R (B.parabolic F) W}
    {τ : Representation R (B.parabolic F) X}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    leviCoinvariantsMap B (g.comp f) =
      (leviCoinvariantsMap B g).comp (leviCoinvariantsMap B f) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

/-- A parabolic element and its Levi component act identically after quotienting. -/
theorem mk_action_eq_levi (ρ : Representation R (B.parabolic F) V)
    (g : B.parabolic F) (v : V) :
    Jacquet.mk ρ (B.unipotentRadical F) (ρ g v) =
      Jacquet.mk ρ (B.unipotentRadical F)
        (ρ (B.leviInParabolic F (B.leviProjection F g)) v) := by
  have h := Jacquet.mk_apply_subgroup ρ (B.unipotentRadical F)
    (B.unipotentPart F g) (ρ (B.leviInParabolic F (B.leviProjection F g)) v)
  change Jacquet.mk ρ _ (ρ (g * (B.leviInParabolic F (B.leviProjection F g))⁻¹)
    (ρ (B.leviInParabolic F (B.leviProjection F g)) v)) = _ at h
  rw [← Module.End.mul_apply, ← ρ.map_mul, inv_mul_cancel_right] at h
  exact h

/-- The quotient projection, equivariant for the entire parabolic after inflation. -/
noncomputable def leviCoinvariantsMk (ρ : Representation R (B.parabolic F) V) :
    ρ.IntertwiningMap (inflate B (leviCoinvariants B ρ)) where
  toLinearMap := Jacquet.mk ρ (B.unipotentRadical F)
  isIntertwining' g := by
    ext v
    exact mk_action_eq_levi B ρ g v

/-- A map into an inflated representation factors through the actual quotient. -/
noncomputable def coinvariantsDesc
    {ρ : Representation R (B.parabolic F) V}
    {σ : Representation R (B.Levi F) W}
    (f : ρ.IntertwiningMap (inflate B σ)) :
    (leviCoinvariants B ρ).IntertwiningMap σ where
  toLinearMap := Jacquet.lift ρ (B.unipotentRadical F) f.toLinearMap (by
    intro u
    ext v
    change f (ρ u.val v) = f v
    rw [Representation.IntertwiningMap.isIntertwining ρ (inflate B σ) f]
    exact inflate_radical B σ u (f v))
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change f (ρ (B.leviInParabolic F m) v) = σ m (f v)
    rw [Representation.IntertwiningMap.isIntertwining ρ (inflate B σ) f]
    change σ (B.leviProjection F (B.leviInParabolic F m)) (f v) = _
    rw [GeneralLinear.BlockShape.leviProjection_section]

@[simp] theorem coinvariantsDesc_mk
    {ρ : Representation R (B.parabolic F) V}
    {σ : Representation R (B.Levi F) W}
    (f : ρ.IntertwiningMap (inflate B σ)) (v : V) :
    coinvariantsDesc B f (Jacquet.mk ρ (B.unipotentRadical F) v) = f v := rfl

/-- The algebraic coinvariant-inflation adjunction on actual intertwiner modules. -/
noncomputable def coinvariantsHomEquiv
    (ρ : Representation R (B.parabolic F) V) (σ : Representation R (B.Levi F) W) :
    ((leviCoinvariants B ρ).IntertwiningMap σ) ≃ₗ[R]
      ρ.IntertwiningMap (inflate B σ) where
  toFun f := (inflateMap B f).comp (leviCoinvariantsMk B ρ)
  invFun f := coinvariantsDesc B f
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply Representation.Coinvariants.hom_ext
    rfl
  right_inv f := by
    ext v
    rfl
  map_add' f g := by
    ext v
    rfl
  map_smul' r f := by
    ext v
    rfl

@[simp] theorem coinvariantsHomEquiv_apply
    (ρ : Representation R (B.parabolic F) V) (σ : Representation R (B.Levi F) W)
    (f : (leviCoinvariants B ρ).IntertwiningMap σ) (v : V) :
    coinvariantsHomEquiv B ρ σ f v =
      f (Jacquet.mk ρ (B.unipotentRadical F) v) := rfl

@[simp] theorem coinvariantsHomEquiv_symm_mk
    (ρ : Representation R (B.parabolic F) V) (σ : Representation R (B.Levi F) W)
    (f : ρ.IntertwiningMap (inflate B σ)) (v : V) :
    (coinvariantsHomEquiv B ρ σ).symm f
      (Jacquet.mk ρ (B.unipotentRadical F) v) = f v := rfl

end Langlands.Parabolic
