import Langlands.Geometry.Building.SemilinearCocycleAction
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-! # Twisted conjugation on stabilizers of semilinear actions -/

noncomputable section

namespace Langlands.Geometry.Building.SemilinearCocycleAction

universe uΓ uH uX

variable {Γ : Type uΓ} [Group Γ] {H : Type uH} [Group H]
  {X : Type uX} [MulAction H X]
  (ρ : Γ →* MulAut H) (A : Γ →* Equiv.Perm X)
  (hA : ∀ σ g x, A σ (g • x) = ρ σ g • A σ x)
  (c : Γ → H) (hc : ∀ σ τ, c (σ * τ) = c σ * ρ σ (c τ))

/-- Inner-twisted coefficient automorphisms form an action on the group itself. -/
def conjugationAction : Γ →* MulAut H where
  toFun σ := MulAut.conj (c σ) * ρ σ
  map_one' := by
    ext g
    simp [cocycle_one ρ c hc]
  map_mul' σ τ := by
    ext g
    simp [hc, mul_assoc]

@[simp] theorem conjugationAction_apply (σ : Γ) (g : H) :
    conjugationAction ρ c hc σ g = c σ * ρ σ g * (c σ)⁻¹ := rfl

/-- The twisted point action is semilinear for twisted conjugation. -/
theorem action_smul (σ : Γ) (g : H) (x : X) :
    action ρ A hA c hc σ (g • x) =
      conjugationAction ρ c hc σ g • action ρ A hA c hc σ x := by
  simp only [action_apply, conjugationAction_apply, hA, mul_smul, inv_smul_smul]

/-- The twisted automorphism transports the stabilizer to that of the twisted point. -/
theorem conjugationAction_mem_stabilizer_iff (σ : Γ) (g : H) (x : X) :
    conjugationAction ρ c hc σ g ∈
        MulAction.stabilizer H (action ρ A hA c hc σ x) ↔
      g ∈ MulAction.stabilizer H x := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    ← action_smul ρ A hA c hc]
  exact (action ρ A hA c hc σ).injective.eq_iff

/-- An automorphism action restricts to a subgroup stable under all its elements.
Stability for inverse group elements supplies the inverse maps. -/
def restrictGroupAction (ψ : Γ →* MulAut H) (P : Subgroup H)
    (hP : ∀ σ g, g ∈ P → ψ σ g ∈ P) : Γ →* MulAut P where
  toFun σ :=
    { toFun g := ⟨ψ σ g, hP σ g g.property⟩
      invFun g := ⟨ψ σ⁻¹ g, hP σ⁻¹ g g.property⟩
      left_inv g := by
        apply Subtype.ext
        change ψ σ⁻¹ (ψ σ g) = g
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv g := by
        apply Subtype.ext
        change ψ σ (ψ σ⁻¹ g) = g
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' g h := by
        apply Subtype.ext
        exact map_mul (ψ σ) (g : H) (h : H) }
  map_one' := by
    ext g
    change ψ 1 g = g
    rw [map_one, MulAut.one_apply]
  map_mul' σ τ := by
    ext g
    change ψ (σ * τ) g = ψ σ (ψ τ g)
    rw [map_mul, MulAut.mul_apply]

@[simp] theorem restrictGroupAction_apply (ψ : Γ →* MulAut H) (P : Subgroup H)
    (hP : ∀ σ g, g ∈ P → ψ σ g ∈ P) (σ : Γ) (g : P) :
    (restrictGroupAction ψ P hP σ g : H) = ψ σ g := rfl

/-- At a twisted-fixed point, twisted conjugation acts on the actual point stabilizer. -/
def stabilizerAction (x : X)
    (hx : ∀ σ, action ρ A hA c hc σ x = x) :
    Γ →* MulAut (MulAction.stabilizer H x) :=
  restrictGroupAction (conjugationAction ρ c hc) (MulAction.stabilizer H x) (by
    intro σ g hg
    have h := (conjugationAction_mem_stabilizer_iff ρ A hA c hc σ g x).mpr hg
    simpa only [hx σ] using h)

@[simp] theorem stabilizerAction_apply (x : X)
    (hx : ∀ σ, action ρ A hA c hc σ x = x)
    (σ : Γ) (g : MulAction.stabilizer H x) :
    (stabilizerAction ρ A hA c hc x hx σ g : H) =
      c σ * ρ σ g * (c σ)⁻¹ := rfl

/-- Normality makes a coefficient-stable subgroup stable under twisted conjugation. -/
theorem conjugationAction_mem_normal_iff (N : Subgroup H) [hN : N.Normal]
    (hρN : ∀ σ g, ρ σ g ∈ N ↔ g ∈ N) (σ : Γ) (g : H) :
    conjugationAction ρ c hc σ g ∈ N ↔ g ∈ N := by
  rw [conjugationAction_apply]
  constructor
  · intro h
    apply (hρN σ g).mp
    have h' := hN.conj_mem _ h (c σ)⁻¹
    simpa [mul_assoc] using h'
  · intro h
    exact hN.conj_mem _ ((hρN σ g).mpr h) (c σ)

/-- Twisted conjugation acts on the intersection of a stable normal subgroup
with the stabilizer of a twisted-fixed point. -/
def normalStabilizerAction (N : Subgroup H) [N.Normal]
    (hρN : ∀ σ g, ρ σ g ∈ N ↔ g ∈ N)
    (x : X) (hx : ∀ σ, action ρ A hA c hc σ x = x) :
    Γ →* MulAut ↥(N ⊓ MulAction.stabilizer H x) :=
  restrictGroupAction (conjugationAction ρ c hc) (N ⊓ MulAction.stabilizer H x) (by
    intro σ g hg
    refine Subgroup.mem_inf.mpr
      ⟨(conjugationAction_mem_normal_iff ρ c hc N hρN σ g).mpr hg.1, ?_⟩
    have h := (conjugationAction_mem_stabilizer_iff ρ A hA c hc σ g x).mpr hg.2
    simpa only [hx σ] using h)

@[simp] theorem normalStabilizerAction_apply (N : Subgroup H) [N.Normal]
    (hρN : ∀ σ g, ρ σ g ∈ N ↔ g ∈ N)
    (x : X) (hx : ∀ σ, action ρ A hA c hc σ x = x)
    (σ : Γ) (g : ↥(N ⊓ MulAction.stabilizer H x)) :
    (normalStabilizerAction ρ A hA c hc N hρN x hx σ g : H) =
      c σ * ρ σ g * (c σ)⁻¹ := rfl

end Langlands.Geometry.Building.SemilinearCocycleAction
