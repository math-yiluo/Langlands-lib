import Langlands.Correspondence.HenniartUnramified.SplitDegree
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Explicit coinduction from a stage of finite degree -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uG uH uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

section Conj

variable (D : SplitDegree G)

/-- Conjugation of inertia by a power of the chosen lift. -/
def cj (k : ℕ) : D.inertia →* D.inertia := (MulAut.conjNormal (D.lift ^ k)).toMonoidHom

theorem coe_cj (k : ℕ) (n : D.inertia) :
    ((D.cj k n : D.inertia) : G) = D.lift ^ k * n * (D.lift ^ k)⁻¹ :=
  MulAut.conjNormal_apply _ _

theorem cj_zero (n : D.inertia) : D.cj 0 n = n := by
  apply Subtype.ext
  simp [coe_cj]

theorem cj_conj (k : ℕ) (n : D.inertia) :
    D.cj k (MulAut.conjNormal D.lift n) = D.cj (k + 1) n := by
  apply Subtype.ext
  simp only [coe_cj, MulAut.conjNormal_apply, pow_succ]
  group

theorem cj_add (k l : ℕ) (n : D.inertia) : D.cj k (D.cj l n) = D.cj (k + l) n := by
  apply Subtype.ext
  simp only [coe_cj, pow_add]
  group

theorem continuous_cj [IsTopologicalGroup G] (k : ℕ) : Continuous (D.cj k) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end Conj

variable {H : Type uH} [Group H] [TopologicalSpace H]

/-- A stage of degree `f`: an injective map whose degree is `f` times the stage degree,
sending the stage lift to the `f`th power of the lift, with a continuous inverse on inertia. -/
structure Stage (D : SplitDegree G) (E : SplitDegree H) (f : ℕ) where
  ι : H →* G
  injective : Function.Injective ι
  continuous_ι : Continuous ι
  κ : D.inertia →* H
  continuous_κ : Continuous κ
  ι_κ : ∀ n : D.inertia, ι (κ n) = n
  degree_ι : ∀ h : H, D.intDegree (ι h) = f * E.intDegree h
  ι_lift : ι E.lift = D.lift ^ f

section Block

variable {J : Type*} [Group J] {I : Type*} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The block-diagonal representation with prescribed blocks on the same carrier. -/
def blockRep (ρ : I → Representation ℂ J V) : Representation ℂ J (I → V) where
  toFun n := LinearMap.pi fun k => (ρ k n).comp (LinearMap.proj k)
  map_one' := LinearMap.ext fun v => funext fun k => by simp
  map_mul' a b := LinearMap.ext fun v => funext fun k => by simp

@[simp] theorem blockRep_apply (ρ : I → Representation ℂ J V) (n : J) (v : I → V) (k : I) :
    blockRep ρ n v k = ρ k n (v k) := rfl

end Block

section Cyclic

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Rotation of `f = m + 1` coordinates, applying `T` at the last one. -/
def cyclicEquiv (m : ℕ) (T : V ≃ₗ[ℂ] V) : (Fin (m + 1) → V) ≃ₗ[ℂ] (Fin (m + 1) → V) :=
  (LinearEquiv.funCongrLeft ℂ V (finRotate (m + 1))).trans
    (LinearEquiv.piCongrRight fun k => if k = Fin.last m then T else LinearEquiv.refl ℂ V)

theorem cyclicEquiv_apply_last (m : ℕ) (T : V ≃ₗ[ℂ] V) (v : Fin (m + 1) → V) :
    cyclicEquiv m T v (Fin.last m) = T (v 0) := by
  simp [cyclicEquiv, LinearEquiv.funCongrLeft_apply]

theorem cyclicEquiv_apply_of_ne (m : ℕ) (T : V ≃ₗ[ℂ] V) (v : Fin (m + 1) → V)
    {k : Fin (m + 1)} (hk : k ≠ Fin.last m) :
    cyclicEquiv m T v k = v (finRotate (m + 1) k) := by
  simp [cyclicEquiv, LinearEquiv.funCongrLeft_apply, hk]

end Cyclic

variable {D : SplitDegree G} {E : SplitDegree H} {m : ℕ}

section LiftUnit

variable (E) (m)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)

/-- The operator of the lift on the coinduced space. -/
def cycUnit : (Module.End ℂ (Fin (m + 1) → V))ˣ :=
  GeneralLinearGroup.ofLinearEquiv
    (cyclicEquiv m (GeneralLinearGroup.toLinearEquiv (τ.asGroupHom E.lift)))

theorem cycUnit_apply_last (v : Fin (m + 1) → V) :
    (cycUnit E m τ : Module.End ℂ _) v (Fin.last m) = τ E.lift (v 0) :=
  cyclicEquiv_apply_last m _ v

theorem cycUnit_apply_of_ne (v : Fin (m + 1) → V) {k : Fin (m + 1)} (hk : k ≠ Fin.last m) :
    (cycUnit E m τ : Module.End ℂ _) v k = v (finRotate (m + 1) k) :=
  cyclicEquiv_apply_of_ne m _ v hk

end LiftUnit

namespace Stage

variable (S : Stage D E (m + 1))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)

theorem κ_conj_lift (n : D.inertia) :
    S.κ (D.cj (m + 1) n) * E.lift = E.lift * S.κ n := by
  apply S.injective
  rw [map_mul, map_mul, S.ι_κ, S.ι_κ, S.ι_lift, coe_cj]
  group

/-- The conjugate inertia blocks `τ ∘ κ ∘ conj(lift^k)`. -/
def block (k : ℕ) : Representation ℂ D.inertia V := τ.comp (S.κ.comp (D.cj k))

@[simp] theorem block_apply (k : ℕ) (n : D.inertia) : S.block τ k n = τ (S.κ (D.cj k n)) := rfl

/-- The inertia part of the coinduced representation. -/
def inertiaRep : Representation ℂ D.inertia (Fin (m + 1) → V) :=
  blockRep fun k : Fin (m + 1) => S.block τ k

@[simp] theorem inertiaRep_apply (n : D.inertia) (v : Fin (m + 1) → V) (k : Fin (m + 1)) :
    S.inertiaRep τ n v k = τ (S.κ (D.cj k n)) (v k) := rfl


theorem inertiaRep_conj_mul (n : D.inertia) :
    S.inertiaRep τ (MulAut.conjNormal D.lift n) * (cycUnit E m τ : Module.End ℂ _) =
      (cycUnit E m τ : Module.End ℂ _) * S.inertiaRep τ n := by
  apply LinearMap.ext
  intro v
  funext k
  simp only [Module.End.mul_apply, inertiaRep_apply, cj_conj]
  by_cases hk : k = Fin.last m
  · subst hk
    rw [cycUnit_apply_last, cycUnit_apply_last, inertiaRep_apply]
    simp only [Fin.val_last, Fin.val_zero, cj_zero]
    rw [← Module.End.mul_apply, ← map_mul, S.κ_conj_lift, map_mul, Module.End.mul_apply]
  · rw [cycUnit_apply_of_ne _ _ _ v hk, cycUnit_apply_of_ne _ _ _ _ hk, inertiaRep_apply,
      coe_finRotate_of_ne_last hk]

theorem compatible (n : D.inertia) :
    (S.inertiaRep τ).asGroupHom (MulAut.conjNormal D.lift n) =
      cycUnit E m τ * (S.inertiaRep τ).asGroupHom n * (cycUnit E m τ)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, asGroupHom_apply, asGroupHom_apply,
    ← S.inertiaRep_conj_mul, mul_assoc, Units.mul_inv, mul_one]

/-- Coinduction from the stage, on the explicit carrier `Fin (m + 1) → V`. -/
def coind : Representation ℂ G (Fin (m + 1) → V) :=
  D.extend (S.inertiaRep τ) (cycUnit E m τ) (S.compatible τ)

@[simp] theorem coind_inertia (n : D.inertia) : S.coind τ n = S.inertiaRep τ n :=
  D.extend_on_inertia _ _ _ n

theorem coind_lift : S.coind τ D.lift = (cycUnit E m τ : Module.End ℂ _) := by
  have h1 : D.intDegree D.lift = 1 := by
    rw [intDegree, D.lift_degree]
    rfl
  have hf : D.factor D.lift = 1 := by
    apply Subtype.ext
    simp [factor, h1]
  rw [coind, extend_apply, hf, h1, map_one, zpow_one, one_mul]

end Stage

end Langlands.FiniteRepresentation.SplitDegree
