import Langlands.Shimura.Unitary.InvolutionBaseChangeTower
import Mathlib.Algebra.Group.Prod

noncomputable section

namespace Langlands.Shimura.AlgebraInvolution

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (σ : AlgebraInvolution R A)

@[simp] theorem units_scalarUnits (c : Rˣ) :
    σ.units (scalarUnits (A := A) c) = scalarUnits c :=
  Units.ext (σ.apply_algebraMap c)

/-- Exchange the two factors while applying the same algebra involution. -/
def exchange : AlgebraInvolution R (A × A) where
  linear :=
    { toFun := fun p => (σ p.2, σ p.1)
      map_add' := by intros; exact Prod.ext (σ.apply_add _ _) (σ.apply_add _ _)
      map_smul' := by intros; exact Prod.ext (σ.apply_smul _ _) (σ.apply_smul _ _) }
  map_one := Prod.ext σ.apply_one σ.apply_one
  map_mul p q := Prod.ext (σ.apply_mul _ _) (σ.apply_mul _ _)
  involutive p := Prod.ext (σ.apply_apply _) (σ.apply_apply _)

@[simp] theorem exchange_apply (p : A × A) : σ.exchange p = (σ p.2, σ p.1) := rfl

@[simp] theorem exchange_units (p : (A × A)ˣ) :
    MulEquiv.prodUnits (σ.exchange.units p) =
      (σ.units (MulEquiv.prodUnits p).2, σ.units (MulEquiv.prodUnits p).1) :=
  Prod.ext (Units.ext rfl) (Units.ext rfl)

/-- Build the two algebra-unit components from a free first unit and scalar multiplier. -/
def exchangeLift : Aˣ × Rˣ →* (A × A)ˣ :=
  MulEquiv.prodUnits.symm.toMonoidHom.comp
    ((MonoidHom.fst Aˣ Rˣ).prod σ.similitudeCompanion)

@[simp] theorem exchangeLift_components (p : Aˣ × Rˣ) :
    MulEquiv.prodUnits (σ.exchangeLift p) = (p.1, σ.similitudeCompanion p) :=
  MulEquiv.apply_symm_apply _ _

/-- The constructed pair satisfies the actual exchange-similitude equation. -/
theorem exchangeLift_mem (p : Aˣ × Rˣ) :
    (σ.exchangeLift p, p.2) ∈ σ.exchange.similitudes := by
  rw [mem_similitudes_iff_units]
  apply MulEquiv.prodUnits.injective
  rw [_root_.map_mul, exchange_units, exchangeLift_components]
  change
    (p.1 * σ.units (scalarUnits p.2 * σ.inverseUnits p.1),
      (scalarUnits p.2 * σ.inverseUnits p.1) * σ.units p.1) =
    (scalarUnits p.2, scalarUnits p.2)
  simp [inverseUnits, mul_assoc]

/-- Similitudes for an exchange involution are a free algebra unit and a scalar unit. -/
def exchangeSimilitudesEquiv : σ.exchange.similitudes ≃* Aˣ × Rˣ where
  toFun g := ((MulEquiv.prodUnits g.val.1).1, g.val.2)
  invFun p := ⟨(σ.exchangeLift p, p.2), σ.exchangeLift_mem p⟩
  left_inv g := by
    have hg := (σ.exchange.mem_similitudes_iff_units g.val).mp g.property
    have hsecond := congrArg (fun u : (A × A)ˣ => (MulEquiv.prodUnits u).2) hg
    change (MulEquiv.prodUnits g.val.1).2 * σ.units (MulEquiv.prodUnits g.val.1).1 =
      scalarUnits g.val.2 at hsecond
    apply Subtype.ext
    apply Prod.ext
    · apply MulEquiv.prodUnits.injective
      rw [exchangeLift_components]
      apply Prod.ext
      · rfl
      · change scalarUnits g.val.2 * (σ.units (MulEquiv.prodUnits g.val.1).1)⁻¹ = _
        exact (eq_mul_inv_iff_mul_eq.mpr hsecond).symm
    · rfl
  right_inv p := by
    change ((MulEquiv.prodUnits (σ.exchangeLift p)).1, p.2) = p
    rw [exchangeLift_components]
  map_mul' g h := by
    change ((MulEquiv.prodUnits (g.val.1 * h.val.1)).1, g.val.2 * h.val.2) = _
    rw [_root_.map_mul]
    rfl

@[simp] theorem exchangeSimilitudesEquiv_fst (g : σ.exchange.similitudes) :
    (σ.exchangeSimilitudesEquiv g).1 = (MulEquiv.prodUnits g.val.1).1 := rfl

@[simp] theorem exchangeSimilitudesEquiv_snd (g : σ.exchange.similitudes) :
    (σ.exchangeSimilitudesEquiv g).2 = σ.exchange.multiplier g := rfl

@[simp] theorem exchangeSimilitudesEquiv_symm_components (p : Aˣ × Rˣ) :
    MulEquiv.prodUnits ((σ.exchangeSimilitudesEquiv.symm p).val.1) =
      (p.1, scalarUnits p.2 * σ.inverseUnits p.1) :=
  σ.exchangeLift_components p

end Langlands.Shimura.AlgebraInvolution
