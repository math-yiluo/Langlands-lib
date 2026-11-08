import Langlands.Cohomology.ModuleComplex.ObstructionConeOpenStatement
import Langlands.Cohomology.ModuleComplex.ObstructionCone.Transfer
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # A three-term complex of finite projective modules computing the obstruction cone

For a complex `K` and the data of an obstruction cone, together with a presentation
`G₁ → G₀ → Q → 0`, this module builds linear maps `a : F^∨ × K⁰ → G₀^∨ × K¹` and
`b : G₀^∨ × K¹ → G₁^∨ × K²`. After tensoring with any module `M`, middle exactness of
`a ⊗ M`, `b ⊗ M` is equivalent to `HOneVanishes K dK δ θ z M`.
-/

set_option autoImplicit false

universe u

open TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.ObstructionCone.Model

variable {A : Type u} [CommRing A]
  {K : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  (dK : ∀ i, K i →ₗ[A] K (i + 1))
  {F Q G₀ G₁ : Type u} [AddCommGroup F] [Module A F] [AddCommGroup Q] [Module A Q]
  [AddCommGroup G₀] [Module A G₀] [AddCommGroup G₁] [Module A G₁]
  (δ : Q →ₗ[A] F) (p : G₀ →ₗ[A] Q) (g : G₁ →ₗ[A] G₀)
  (θ : K 1 ⊗[A] F) (z₀ : K 2 ⊗[A] G₀)

/-- Contraction of a cochain with values in `F` against a linear form on `F`. -/
def contract {X N : Type u} [AddCommGroup X] [Module A X] [AddCommGroup N] [Module A N]
    (t : X ⊗[A] N) (M : Type u) [AddCommGroup M] [Module A M] : (N →ₗ[A] M) →ₗ[A] X ⊗[A] M :=
  LinearMap.applyₗ t ∘ₗ LinearMap.lTensorHom (M := X)

@[simp]
lemma contract_apply {X N : Type u} [AddCommGroup X] [Module A X] [AddCommGroup N] [Module A N]
    (t : X ⊗[A] N) (M : Type u) [AddCommGroup M] [Module A M] (D : N →ₗ[A] M) :
    contract t M D = D.lTensor X t := rfl

/-- The first map of the model complex. -/
def a : (Module.Dual A F × K 0) →ₗ[A] (Module.Dual A G₀ × K 1) :=
  LinearMap.prod (-(LinearMap.lcomp A A (δ ∘ₗ p) ∘ₗ LinearMap.fst A _ _))
    ((TensorProduct.rid A (K 1)).toLinearMap ∘ₗ contract θ A ∘ₗ LinearMap.fst A _ _ +
      dK 0 ∘ₗ LinearMap.snd A _ _)

/-- The second map of the model complex. -/
def b : (Module.Dual A G₀ × K 1) →ₗ[A] (Module.Dual A G₁ × K 2) :=
  LinearMap.prod (LinearMap.lcomp A A g ∘ₗ LinearMap.fst A _ _)
    ((TensorProduct.rid A (K 2)).toLinearMap ∘ₗ contract z₀ A ∘ₗ LinearMap.fst A _ _ +
      dK 1 ∘ₗ LinearMap.snd A _ _)

lemma a_apply (f : Module.Dual A F) (β : K 0) :
    a dK δ p θ (f, β) = (-(f ∘ₗ (δ ∘ₗ p)), TensorProduct.rid A (K 1) (f.lTensor (K 1) θ) + dK 0 β) :=
  rfl

lemma b_apply (f : Module.Dual A G₀) (γ : K 1) :
    b dK g z₀ (f, γ) = (f ∘ₗ g, TensorProduct.rid A (K 2) (f.lTensor (K 2) z₀) + dK 1 γ) :=
  rfl

variable (M : Type u) [AddCommGroup M] [Module A M]

/-- The first map with coefficients in `M`. -/
def aM : ((F →ₗ[A] M) × (K 0 ⊗[A] M)) →ₗ[A] ((G₀ →ₗ[A] M) × (K 1 ⊗[A] M)) :=
  LinearMap.prod (-(LinearMap.lcomp A M (δ ∘ₗ p) ∘ₗ LinearMap.fst A _ _))
    (contract θ M ∘ₗ LinearMap.fst A _ _ + (dK 0).rTensor M ∘ₗ LinearMap.snd A _ _)

/-- The second map with coefficients in `M`. -/
def bM : ((G₀ →ₗ[A] M) × (K 1 ⊗[A] M)) →ₗ[A] ((G₁ →ₗ[A] M) × (K 2 ⊗[A] M)) :=
  LinearMap.prod (LinearMap.lcomp A M g ∘ₗ LinearMap.fst A _ _)
    (contract z₀ M ∘ₗ LinearMap.fst A _ _ + (dK 1).rTensor M ∘ₗ LinearMap.snd A _ _)

lemma aM_apply (D : F →ₗ[A] M) (β : K 0 ⊗[A] M) :
    aM dK δ p θ M (D, β) = (-(D ∘ₗ (δ ∘ₗ p)), D.lTensor (K 1) θ + (dK 0).rTensor M β) :=
  rfl

lemma bM_apply (w : G₀ →ₗ[A] M) (γ : K 1 ⊗[A] M) :
    bM dK g z₀ M (w, γ) = (w ∘ₗ g, w.lTensor (K 2) z₀ + (dK 1).rTensor M γ) :=
  rfl

/-- The identification of `(G^∨ × X) ⊗ M` with `Hom(G, M) × (X ⊗ M)`. -/
def termEquiv (G X : Type u) [AddCommGroup G] [Module A G] [Module.Finite A G]
    [Module.Projective A G] [AddCommGroup X] [Module A X] :
    (Module.Dual A G × X) ⊗[A] M ≃ₗ[A] (G →ₗ[A] M) × (X ⊗[A] M) :=
  (TensorProduct.prodLeft A A (Module.Dual A G) X M).trans
    ((dualTensorHomEquiv A G M).prodCongr (LinearEquiv.refl A _))

@[simp]
lemma termEquiv_tmul (G X : Type u) [AddCommGroup G] [Module A G] [Module.Finite A G]
    [Module.Projective A G] [AddCommGroup X] [Module A X] (f : Module.Dual A G) (x : X)
    (m : M) : termEquiv M G X ((f, x) ⊗ₜ m) = (dualTensorHom A G M (f ⊗ₜ m), x ⊗ₜ m) := by
  simp only [termEquiv, LinearEquiv.trans_apply, TensorProduct.prodLeft_tmul,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rfl

/-- Contraction commutes with tensoring a linear form by an element of `M`. -/
lemma rid_contract_tmul {X N : Type u} [AddCommGroup X] [Module A X] [AddCommGroup N]
    [Module A N] (t : X ⊗[A] N) (f : Module.Dual A N) (m : M) :
    (TensorProduct.rid A X (f.lTensor X t)) ⊗ₜ m = (dualTensorHom A N M (f ⊗ₜ m)).lTensor X t := by
  induction t using TensorProduct.inductionOn with
  | tmul x n =>
      simp [dualTensorHom_apply, TensorProduct.smul_tmul]
  | add x y hx hy =>
      rw [map_add, map_add, TensorProduct.add_tmul, hx, hy, map_add]


section Ladder

variable [Module.Finite A F] [Module.Projective A F] [Module.Finite A G₀]
  [Module.Projective A G₀] [Module.Finite A G₁] [Module.Projective A G₁]

lemma ladder_a : (termEquiv M G₀ (K 1)).toLinearMap ∘ₗ (a dK δ p θ).rTensor M =
    aM dK δ p θ M ∘ₗ (termEquiv M F (K 0)).toLinearMap := by
  apply TensorProduct.ext'
  rintro ⟨f, β⟩ m
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, a_apply,
    termEquiv_tmul, aM_apply]
  refine Prod.ext ?_ ?_
  · ext x
    simp [dualTensorHom_apply]
  · simp only [TensorProduct.add_tmul]
    rw [rid_contract_tmul]

lemma ladder_b : (termEquiv M G₁ (K 2)).toLinearMap ∘ₗ (b dK g z₀).rTensor M =
    bM dK g z₀ M ∘ₗ (termEquiv M G₀ (K 1)).toLinearMap := by
  apply TensorProduct.ext'
  rintro ⟨f, γ⟩ m
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, b_apply,
    termEquiv_tmul, bM_apply]
  refine Prod.ext ?_ ?_
  · ext x
    simp [dualTensorHom_apply]
  · simp only [TensorProduct.add_tmul]
    rw [rid_contract_tmul]

/-- Middle exactness of the model complex after `⊗ M` is middle exactness of the maps with
coefficients in `M`. -/
lemma exact_rTensor_iff : Function.Exact ((a dK δ p θ).rTensor M) ((b dK g z₀).rTensor M) ↔
    Function.Exact (aM dK δ p θ M) (bM dK g z₀ M) :=
  (Function.Exact.iff_of_ladder_linearEquiv (ladder_a dK δ p θ M).symm
    (ladder_b dK g z₀ M).symm).symm

end Ladder


/-- The model maps form a complex. -/
lemma b_comp_a (hpg : p ∘ₗ g = 0) (zh : K 2 ⊗[A] Q) (hz₀ : p.lTensor (K 2) z₀ = zh)
    (hθ : (dK 1).rTensor F θ = δ.lTensor (K 2) zh) (hdK : dK 1 ∘ₗ dK 0 = 0) :
    b dK g z₀ ∘ₗ a dK δ p θ = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨f, β⟩ := x
  rw [LinearMap.comp_apply, a_apply, b_apply, LinearMap.zero_apply]
  refine Prod.ext ?_ ?_
  · simp [LinearMap.neg_comp, LinearMap.comp_assoc, hpg]
  · have h1 : ∀ t : K 1 ⊗[A] F, dK 1 (TensorProduct.rid A (K 1) (f.lTensor (K 1) t)) =
        TensorProduct.rid A (K 2) (f.lTensor (K 2) ((dK 1).rTensor F t)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    have h2 : (-(f ∘ₗ (δ ∘ₗ p))).lTensor (K 2) z₀ = -((f ∘ₗ δ).lTensor (K 2) zh) := by
      rw [LinearMap.lTensor_neg, LinearMap.neg_apply, ← LinearMap.comp_assoc,
        LinearMap.lTensor_comp, LinearMap.comp_apply, hz₀]
    have h3 : dK 1 (dK 0 β) = 0 := by
      rw [← LinearMap.comp_apply, hdK, LinearMap.zero_apply]
    simp only [Prod.snd_zero]
    rw [h2, map_add, h1, h3, add_zero, hθ, ← LinearMap.comp_apply (f.lTensor (K 2)),
      ← LinearMap.lTensor_comp, map_neg, neg_add_cancel]

/-- Middle exactness of the maps with coefficients in `M` is the vanishing of the first
cohomology of the obstruction cone. -/
theorem exact_aM_bM_iff (hp : Function.Surjective p) (hgp : Function.Exact g p)
    (zh : K 2 ⊗[A] Q) (hz₀ : p.lTensor (K 2) z₀ = zh)
    (hθ : (dK 1).rTensor F θ = δ.lTensor (K 2) zh) (hdK : dK 1 ∘ₗ dK 0 = 0) :
    Function.Exact (aM dK δ p θ M) (bM dK g z₀ M) ↔ HOneVanishes K dK δ θ zh M := by
  have hpg : p ∘ₗ g = 0 := hgp.linearMap_comp_eq_zero
  have hlt : ∀ ψ : Q →ₗ[A] M, (ψ ∘ₗ p).lTensor (K 2) z₀ = ψ.lTensor (K 2) zh := by
    intro ψ
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hz₀]
  constructor
  · intro hex c ψ hc
    have h0 : bM dK g z₀ M (ψ ∘ₗ p, c) = 0 := by
      rw [bM_apply, LinearMap.comp_assoc, hpg, LinearMap.comp_zero, hlt, add_comm, hc]
      rfl
    obtain ⟨⟨D, β⟩, hDβ⟩ := (hex _).mp h0
    rw [aM_apply, Prod.mk.injEq] at hDβ
    refine ⟨β, D, by rw [← hDβ.2, add_comm], ?_⟩
    ext q
    obtain ⟨x, rfl⟩ := hp q
    have := LinearMap.congr_fun hDβ.1 x
    simp only [LinearMap.neg_apply, LinearMap.comp_apply] at this
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, ← this,
      neg_add_cancel]
  · intro hH y
    obtain ⟨w, γ⟩ := y
    constructor
    · intro hy
      rw [bM_apply] at hy
      have hy₁ : w ∘ₗ g = 0 := congrArg Prod.fst hy
      have hy₂ : w.lTensor (K 2) z₀ + (dK 1).rTensor M γ = 0 := congrArg Prod.snd hy
      have hle : LinearMap.range g ≤ LinearMap.ker w := by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hy₁, LinearMap.zero_apply]
      let ψ : Q →ₗ[A] M :=
        (LinearMap.range g).liftQ w hle ∘ₗ (hgp.linearEquivOfSurjective hp).symm.toLinearMap
      have hψ : ψ ∘ₗ p = w := by
        ext x
        simp [ψ, Function.Exact.linearEquivOfSurjective_symm_apply]
      have hc : (dK 1).rTensor M γ + ψ.lTensor (K 2) zh = 0 := by
        have h1 := hlt ψ
        rw [hψ] at h1
        rw [← h1]
        exact (add_comm _ _).trans hy₂
      obtain ⟨β, D, hβ, hD⟩ := hH γ ψ hc
      refine ⟨(D, β), ?_⟩
      rw [aM_apply, ← hψ, eq_neg_of_add_eq_zero_left hD, hβ, add_comm]
      simp [LinearMap.neg_comp, LinearMap.comp_assoc]
    · rintro ⟨⟨D, β⟩, hDβ⟩
      rw [← hDβ, aM_apply, bM_apply]
      refine Prod.ext ?_ ?_
      · simp [LinearMap.neg_comp, LinearMap.comp_assoc, hpg]
      · simp only [map_add, Prod.snd_zero]
        rw [Transfer.rTensor_lTensor, hθ, ← LinearMap.comp_apply ((dK 1).rTensor M),
          ← LinearMap.rTensor_comp, hdK, LinearMap.rTensor_zero, LinearMap.zero_apply, add_zero,
          LinearMap.lTensor_neg, LinearMap.neg_apply, ← LinearMap.comp_assoc, hlt,
          ← LinearMap.comp_apply (D.lTensor (K 2)), ← LinearMap.lTensor_comp, neg_add_cancel]

end Langlands.Cohomology.ModuleComplex.ObstructionCone.Model
