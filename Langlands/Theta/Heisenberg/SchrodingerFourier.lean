import Langlands.Theta.Heisenberg.SchrodingerInduced
import Langlands.Theta.Heisenberg.InvariantForm
import Langlands.HarmonicAnalysis.Bicharacter.DualMeasure

/-!
# The Fourier transform between the two Schrödinger models of a polarization

GKT §1.2.5 (**Proposition 1.24**, p. 33; **Theorem 1.25** and **Remark 1.26**, p. 34). For a perfect
pairing `β : X →ₗ[F] Y →ₗ[F] F` of finite-dimensional spaces over a nonarchimedean local field, the
space `X × Y` with `polarizedForm β` has two Schrödinger models: `schrodingerSB` on `S(X)` (induced
from the Lagrangian `0 × Y`, the book's `C_c^∞(Y)`) and `schrodingerSBDual` on `S(Y)` (induced from
`X × 0`, the book's `C_c^∞(X)`), the second being the Schrödinger model of the swapped polarization
`Y × X` with the pairing `-β.flip`, read through `swapHeisenbergEquiv`.

* `schrodingerFourier μ`: `φ ↦ (y ↦ ∫ ψ(β(x, y)) φ(x) dμ(x))`, the book's `F_{Y,X}`
  (`⟨y_B, x_B⟩ = β(y_B, x_B)`);
* `schrodingerFourier_schrodinger`: it intertwines the two models (Theorem 1.25);
* `schrodingerFourierEquiv`: with its inverse `f ↦ (x ↦ ∫ ψ(-β(x, y)) f(y) dμ'(y))` for the dual
  measure `μ'` (Remark 1.26: `F_{X,Y} = F_{Y,X}⁻¹`, no sign), an isomorphism of representations;
* `lintegral_enorm_schrodingerFourier_sq`: unitary from `μ` to the dual measure (Theorem 1.25).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.HeisenbergGroup

open Langlands.HarmonicAnalysis

universe u v w

section Swap

variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

variable (β : X →ₗ[R] Y →ₗ[R] R)

/-- `polarizedForm (-β.flip) ((y, x), (y', x')) = polarizedForm β ((x, y), (x', y'))`. -/
theorem polarizedForm_neg_flip_swap (w w' : X × Y) :
    polarizedForm (-β.flip) w.swap w'.swap = polarizedForm β w w' := by
  simp only [polarizedForm_apply, Prod.fst_swap, Prod.snd_swap, LinearMap.neg_apply,
    LinearMap.flip_apply]
  ring

variable [Invertible (2 : R)]

/-- **The swap of the polarization** as an isomorphism of Heisenberg groups
`H(X × Y, polarizedForm β) ≃ H(Y × X, polarizedForm (-β.flip))`, `((x, y), t) ↦ ((y, x), t)`. -/
def swapHeisenbergEquiv :
    HeisenbergGroup (polarizedForm β) ≃* HeisenbergGroup (polarizedForm (-β.flip)) where
  toFun g := ⟨g.vec.swap, g.cen⟩
  invFun g := ⟨g.vec.swap, g.cen⟩
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp
  map_mul' g h := by
    refine HeisenbergGroup.ext ?_ ?_
    · change (g.vec + h.vec).swap = g.vec.swap + h.vec.swap
      rfl
    · change g.cen + h.cen + ⅟2 * polarizedForm β g.vec h.vec =
        g.cen + h.cen + ⅟2 * polarizedForm (-β.flip) g.vec.swap h.vec.swap
      rw [polarizedForm_neg_flip_swap]

@[simp] theorem swapHeisenbergEquiv_apply (g : HeisenbergGroup (polarizedForm β)) :
    swapHeisenbergEquiv β g = ⟨g.vec.swap, g.cen⟩ := rfl

end Swap

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] [IsTopologicalAddGroup Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}

variable (β) in
omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y]
  [FiniteDimensional F Y] in
/-- `x ↦ -β(x, y)` read from `-β.flip` is continuous in its first variable. -/
theorem continuous_neg_flip_left (x : X) : Continuous fun y : Y => (-β.flip) y x := by
  simp only [LinearMap.neg_apply, LinearMap.flip_apply]
  exact ((continuous_pairing β).comp (continuous_const.prodMk continuous_id)).neg

variable (hψ : Continuous ψ)

/-- **The Schrödinger model on `S(Y)`** of the Lagrangian `X × 0` (GKT Theorem 1.13 with the roles
of the two Lagrangians exchanged): the Schrödinger model of the swapped polarization, read through
`swapHeisenbergEquiv`. The element `((x₀, y₀), t)` acts by
`f ↦ (y ↦ ψ(t - β(x₀, y) - ½ β(x₀, y₀)) f(y + y₀))`. -/
def schrodingerSBDual : Representation ℂ (HeisenbergGroup (polarizedForm β)) (SchwartzBruhat Y) :=
  (schrodingerSB hψ (continuous_neg_flip_left β)).comp (swapHeisenbergEquiv β).toMonoidHom

omit [IsTopologicalAddGroup X] [FiniteDimensional F Y] in
theorem schrodingerSBDual_apply (g : HeisenbergGroup (polarizedForm β)) (f : SchwartzBruhat Y)
    (y : Y) : (schrodingerSBDual hψ g f : Y → ℂ) y =
      ψ g.cen * (ψ (-β g.vec.1 y - ⅟2 * β g.vec.1 g.vec.2) * (f : Y → ℂ) (y + g.vec.2)) := by
  change ψ g.cen • schrodingerFun ψ (-β.flip) g.vec.swap f y = _
  simp only [schrodingerFun_apply, Prod.fst_swap, Prod.snd_swap, LinearMap.neg_apply,
    LinearMap.flip_apply, smul_eq_mul]
  congr 3
  ring

section Fourier

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [β.IsPerfPair]
  (hψ1 : ψ ≠ 1)

omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
include hψ hψ1 in
/-- `ψ ∘ β` is a perfect pairing of `X` and `Y` (GKT (1.12)). -/
theorem isPerfectBicharacter_psi_pairing : IsPerfectBicharacter fun x y => ψ (β x y) :=
  isPerfectBicharacter_of_nondegenerate hψ
    (SchrodingerIrreducible.Internal.norm_addChar_eq_one hψ) hψ1 β
    (fun y hy => (LinearMap.IsPerfPair.bijective_right β).1
      (LinearMap.ext fun x => by simpa using hy x))
    (fun x hx => (LinearMap.IsPerfPair.bijective_left β).1
      (LinearMap.ext fun y => by simpa using hx y))

variable (μ : Measure X) [μ.IsAddHaarMeasure]

variable (β) in
/-- **The Fourier transform `F_{Y,X}`** (GKT Proposition 1.24, Theorem 1.25):
`φ ↦ (y ↦ ∫ ψ(β(x, y)) φ(x) dμ(x))`, from the Schrödinger model on `S(X)` to the one on `S(Y)`. -/
def schrodingerFourier : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y where
  toFun φ := ⟨pairingFourier μ (fun x y => ψ (β x y)) φ,
    pairingFourier_mem μ (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) φ.2⟩
  map_add' φ φ' := Subtype.ext <| funext fun y => by
    have hc := (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1).continuous
    have hi : ∀ f : SchwartzBruhat X, Integrable (fun x => ψ (β x y) * (f : X → ℂ) x) μ := fun f =>
      ((hc.comp (continuous_id.prodMk continuous_const)).mul
        f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
    change ∫ x, ψ (β x y) * ((φ : X → ℂ) x + φ' x) ∂μ =
      (∫ x, ψ (β x y) * (φ : X → ℂ) x ∂μ) + ∫ x, ψ (β x y) * (φ' : X → ℂ) x ∂μ
    simp_rw [mul_add]
    exact integral_add (hi φ) (hi φ')
  map_smul' a φ := Subtype.ext <| funext fun y => by
    change ∫ x, ψ (β x y) * (a * (φ : X → ℂ) x) ∂μ = a * ∫ x, ψ (β x y) * (φ : X → ℂ) x ∂μ
    simp_rw [mul_left_comm _ a]
    exact integral_const_mul a _

omit [Invertible (2 : F)] [MeasurableSpace Y] [BorelSpace Y] in
theorem schrodingerFourier_apply (φ : SchwartzBruhat X) (y : Y) :
    (schrodingerFourier β hψ hψ1 μ φ : Y → ℂ) y = ∫ x, ψ (β x y) * (φ : X → ℂ) x ∂μ := rfl

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- **GKT Theorem 1.25, intertwining**: `F_{Y,X} ∘ σ_X(h) = σ_Y(h) ∘ F_{Y,X}`. -/
theorem schrodingerFourier_schrodinger (g : HeisenbergGroup (polarizedForm β))
    (φ : SchwartzBruhat X) :
    schrodingerFourier β hψ hψ1 μ (schrodingerSB hψ (fun _ => (continuous_pairing β).comp
        (continuous_id.prodMk continuous_const)) g φ) =
      schrodingerSBDual hψ g (schrodingerFourier β hψ hψ1 μ φ) := by
  obtain ⟨⟨x₀, y₀⟩, t⟩ := g
  refine Subtype.ext (funext fun y => ?_)
  rw [schrodingerSBDual_apply, schrodingerFourier_apply, schrodingerFourier_apply]
  have h := integral_add_right_eq_self (μ := μ) (fun x => ψ (β x y) *
    (schrodingerSB hψ (fun _ => (continuous_pairing β).comp
      (continuous_id.prodMk continuous_const)) ⟨(x₀, y₀), t⟩ φ : X → ℂ) x) (-x₀)
  rw [← h]
  have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  have e : ∀ x, ψ (β (x + -x₀) y) * (schrodingerSB hψ (fun _ => (continuous_pairing β).comp
      (continuous_id.prodMk continuous_const)) ⟨(x₀, y₀), t⟩ φ : X → ℂ) (x + -x₀) =
      ψ t * (ψ (-β x₀ y - ⅟2 * β x₀ y₀) * (ψ (β x (y + y₀)) * (φ : X → ℂ) x)) := fun x => by
    rw [schrodingerSB_apply, schrodinger_apply, Pi.smul_apply, schrodingerFun_apply, smul_eq_mul]
    simp only [neg_add_cancel_right]
    have hph : β (x + -x₀) y + (β (x + -x₀) y₀ + ⅟2 * β x₀ y₀) =
        (-β x₀ y - ⅟2 * β x₀ y₀) + β x (y + y₀) := by
      simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
      linear_combination (β x₀ y₀) * h2
    calc ψ (β (x + -x₀) y) * (ψ t * (ψ (β (x + -x₀) y₀ + ⅟2 * β x₀ y₀) * (φ : X → ℂ) x))
        = ψ t * (ψ (β (x + -x₀) y + (β (x + -x₀) y₀ + ⅟2 * β x₀ y₀)) * (φ : X → ℂ) x) := by
          simp only [AddChar.map_add_eq_mul]; ring
      _ = ψ t * (ψ ((-β x₀ y - ⅟2 * β x₀ y₀) + β x (y + y₀)) * (φ : X → ℂ) x) := by rw [hph]
      _ = _ := by rw [AddChar.map_add_eq_mul]; ring
  simp only [e, integral_const_mul]


variable [CompactOpenExhaustion X] [CompactOpenExhaustion Y] [LocallyCompactSpace X]
  [LocallyCompactSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

variable (β) in
/-- **The inverse transform `F_{X,Y}`** (GKT Remark 1.26): `f ↦ (x ↦ ∫ ψ(-β(x, y)) f(y) dμ'(y))`
for the dual measure `μ'` of `μ`, written as `x ↦ ℱ'_{μ'} f (-x)`. -/
def schrodingerFourierInv : SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat X :=
  have := isAddHaarMeasure_pairingDualMeasure (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) μ
  { toFun := fun f => ⟨fun x => pairingFourierDual (pairingDualMeasure μ fun x y => ψ (β x y))
        (fun x y => ψ (β x y)) f (-x), by
      have hm := pairingFourierDual_mem (pairingDualMeasure μ fun x y => ψ (β x y))
        (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) f.2
      exact ⟨hm.1.comp_continuous continuous_neg,
        hm.2.comp_homeomorph (Homeomorph.neg X)⟩⟩
    map_add' := fun f f' => Subtype.ext <| funext fun x => by
      have hc := (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1).continuous
      have hi : ∀ g : SchwartzBruhat Y, Integrable (fun y => ψ (β (-x) y) * (g : Y → ℂ) y)
          (pairingDualMeasure μ fun x y => ψ (β x y)) := fun g =>
        ((hc.comp (continuous_const.prodMk continuous_id)).mul
          g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
      change ∫ y, ψ (β (-x) y) * ((f : Y → ℂ) y + f' y) ∂_ =
        (∫ y, ψ (β (-x) y) * (f : Y → ℂ) y ∂_) + ∫ y, ψ (β (-x) y) * (f' : Y → ℂ) y ∂_
      simp_rw [mul_add]
      exact integral_add (hi f) (hi f')
    map_smul' := fun a f => Subtype.ext <| funext fun x => by
      change ∫ y, ψ (β (-x) y) * (a * (f : Y → ℂ) y) ∂_ = a * ∫ y, ψ (β (-x) y) * (f : Y → ℂ) y ∂_
      simp_rw [mul_left_comm _ a]
      exact integral_const_mul a _ }

omit [Invertible (2 : F)] in
theorem schrodingerFourierInv_apply (f : SchwartzBruhat Y) (x : X) :
    (schrodingerFourierInv β hψ hψ1 μ f : X → ℂ) x =
      ∫ y, ψ (-β x y) * (f : Y → ℂ) y ∂(pairingDualMeasure μ fun x y => ψ (β x y)) := by
  change ∫ y, ψ (β (-x) y) * (f : Y → ℂ) y ∂_ = _
  simp only [map_neg, LinearMap.neg_apply]

variable (β) in
/-- **GKT Theorem 1.25**: the Fourier transform is an isomorphism of representations from the
Schrödinger model on `S(X)` to the one on `S(Y)`, with inverse `schrodingerFourierInv`
(Remark 1.26: `F_{X,Y} = F_{Y,X}⁻¹`). -/
def schrodingerFourierEquiv :
    (schrodingerSB hψ (fun _ => (continuous_pairing β).comp
      (continuous_id.prodMk continuous_const))).Equiv (schrodingerSBDual (β := β) hψ) :=
  Representation.Equiv.mk
    { schrodingerFourier β hψ hψ1 μ with
      invFun := schrodingerFourierInv β hψ hψ1 μ
      left_inv := fun φ => Subtype.ext <| funext fun x => by
        change pairingFourierDual (pairingDualMeasure μ fun x y => ψ (β x y))
          (fun x y => ψ (β x y)) (pairingFourier μ (fun x y => ψ (β x y)) φ) (-x) = _
        rw [pairingFourierDual_pairingDualMeasure_pairingFourier
          (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) μ φ.2, neg_neg]
      right_inv := fun f => Subtype.ext <| funext fun y => by
        change pairingFourier μ (fun x y => ψ (β x y)) (fun x => pairingFourierDual
          (pairingDualMeasure μ fun x y => ψ (β x y)) (fun x y => ψ (β x y)) f (-x)) y = _
        rw [pairingFourier_comp_neg (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) μ,
          pairingFourier_pairingFourierDual_pairingDualMeasure
            (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) μ f.2, neg_neg] }
    (fun g => LinearMap.ext fun φ => schrodingerFourier_schrodinger hψ hψ1 μ g φ)

theorem schrodingerFourierEquiv_apply (φ : SchwartzBruhat X) :
    schrodingerFourierEquiv β hψ hψ1 μ φ = schrodingerFourier β hψ hψ1 μ φ := rfl

omit [Invertible (2 : F)] in
/-- **GKT Theorem 1.25, unitarity**: for the dual measure `μ'` on `Y`,
`∫ |F φ|² dμ' = ∫ |φ|² dμ`. -/
theorem lintegral_enorm_schrodingerFourier_sq (φ : SchwartzBruhat X) :
    ∫⁻ y, ‖(schrodingerFourier β hψ hψ1 μ φ : Y → ℂ) y‖ₑ ^ 2
        ∂(pairingDualMeasure μ fun x y => ψ (β x y)) = ∫⁻ x, ‖(φ : X → ℂ) x‖ₑ ^ 2 ∂μ :=
  lintegral_enorm_pairingFourier_sq_pairingDualMeasure
    (isPerfectBicharacter_psi_pairing (β := β) hψ hψ1) μ φ.2

end Fourier

end Local

end Langlands.HeisenbergGroup
