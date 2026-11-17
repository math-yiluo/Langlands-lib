import Langlands.Automorphic.ArchimedeanMultiplicityActions

/-! # Separating a compact and Lie factor with arbitrary commuting residual operators -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.GKTensorEvaluation

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe uK uL uV uW uI

variable {K : Type uK} [Group K]
  {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {I : Type uI}
  (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W)

local instance gkResidualMultiplicityGroup : AddCommGroup (Multiplicity ρ π ρ' π') :=
  (gkHoms ρ π ρ' π').addCommGroup

/-- Joint irreducibility for the chosen local actions and a supplied family
of remaining operators. -/
def IsIrreducibleWith (τ : I → Module.End ℂ W) : Prop :=
  Nontrivial W ∧ ∀ N : Submodule ℂ W,
    (∀ k w, w ∈ N → ρ' k w ∈ N) →
    (∀ X w, w ∈ N → π' X w ∈ N) →
    (∀ i w, w ∈ N → τ i w ∈ N) → N = ⊥ ∨ N = ⊤

variable (τ : I → Module.End ℂ W)
  (hτk : ∀ i k w, τ i (ρ' k w) = ρ' k (τ i w))
  (hτl : ∀ i X w, τ i (π' X w) = π' X (τ i w))

/-- The remaining operators act on local multiplicities by postcomposition. -/
def residualOperator (i : I) : Module.End ℂ (Multiplicity ρ π ρ' π') :=
  postcompose ρ π ρ' π' (τ i) (hτk i) (hτl i)

@[simp]
theorem residualOperator_apply (i : I) (f : Multiplicity ρ π ρ' π') (v : V) :
    (residualOperator ρ π ρ' π' τ hτk hτl i f).val v = τ i (f.val v) := rfl

variable [TopologicalSpace K]
include hτk hτl

/-- Nonzero multiplicities span a jointly irreducible target by tensor evaluation. -/
theorem evaluation_surjective
    (h : GKModuleDensity.Hyp ρ π)
    (hjoint : IsIrreducibleWith ρ' π' τ)
    (hM : Nontrivial (Multiplicity ρ π ρ' π')) :
    Function.Surjective (evaluation ρ π ρ' π') := by
  let := h.irreducible.1
  let := hM
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ := exists_ne (0 : Multiplicity ρ π ρ' π')
  have hfa : f.val v ≠ 0 := by
    intro hf0
    apply hf
    apply evalAt_injective ρ π ρ' π' h.irreducible hv
    exact hf0
  let R := LinearMap.range (evaluation ρ π ρ' π')
  have hR : R ≠ ⊥ := by
    intro hR
    have hm : f.val v ∈ R := ⟨v ⊗ₜ[ℂ] f, rfl⟩
    rw [hR, Submodule.mem_bot] at hm
    exact hfa hm
  have htop : R = ⊤ := (hjoint.2 R
    (range_compact ρ π ρ' π')
    (range_lie ρ π ρ' π')
    (fun i => range_commuting ρ π ρ' π' (τ i) (hτk i) (hτl i))).resolve_left hR
  exact LinearMap.range_eq_top.mp htop

/-- Tensor evaluation separates the local factor from every remaining operator. -/
def evaluationEquiv
    (h : GKModuleDensity.Hyp ρ π)
    (hjoint : IsIrreducibleWith ρ' π' τ)
    (hM : Nontrivial (Multiplicity ρ π ρ' π')) :
    V ⊗[ℂ] Multiplicity ρ π ρ' π' ≃ₗ[ℂ] W :=
  LinearEquiv.ofBijective (evaluation ρ π ρ' π')
    ⟨evaluation_injective ρ π ρ' π' h,
      evaluation_surjective ρ π ρ' π' τ hτk hτl h hjoint hM⟩

@[simp]
theorem evaluationEquiv_tmul
    (h : GKModuleDensity.Hyp ρ π)
    (hjoint : IsIrreducibleWith ρ' π' τ)
    (hM : Nontrivial (Multiplicity ρ π ρ' π'))
    (v : V) (f : Multiplicity ρ π ρ' π') :
    evaluationEquiv ρ π ρ' π' τ hτk hτl h hjoint hM (v ⊗ₜ[ℂ] f) = f.val v := rfl

/-- Removing one factor leaves a nonzero multiplicity space irreducible for
the remaining actual operator family. -/
theorem residual_irreducible
    (h : GKModuleDensity.Hyp ρ π)
    (hjoint : IsIrreducibleWith ρ' π' τ)
    (hM : Nontrivial (Multiplicity ρ π ρ' π')) :
    Nontrivial (Multiplicity ρ π ρ' π') ∧
      ∀ N : Submodule ℂ (Multiplicity ρ π ρ' π'),
        (∀ i f, f ∈ N → residualOperator ρ π ρ' π' τ hτk hτl i f ∈ N) →
          N = ⊥ ∨ N = ⊤ := by
  classical
  refine ⟨hM, ?_⟩
  intro N hNstable
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  let := h.irreducible.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨f, hfN, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let T : V ⊗[ℂ] N →ₗ[ℂ] V ⊗[ℂ] Multiplicity ρ π ρ' π' :=
    TensorProduct.map LinearMap.id N.subtype
  let R := LinearMap.range (evaluation ρ π ρ' π' ∘ₗ T)
  have hRk : ∀ k t, ρ' k (evaluation ρ π ρ' π' (T t)) ∈ R := by
    intro k t
    induction t with
    | tmul a f =>
      exact ⟨ρ k a ⊗ₜ[ℂ] f, f.val.property.1 k a⟩
    | add t t' ht ht' => simpa only [map_add] using R.add_mem ht ht'
  have hRl : ∀ X t, π' X (evaluation ρ π ρ' π' (T t)) ∈ R := by
    intro X t
    induction t with
    | tmul a f =>
      exact ⟨π X a ⊗ₜ[ℂ] f, f.val.property.2 X a⟩
    | add t t' ht ht' => simpa only [map_add] using R.add_mem ht ht'
  have hRτ : ∀ i t, τ i (evaluation ρ π ρ' π' (T t)) ∈ R := by
    intro i t
    induction t with
    | tmul a f =>
      exact ⟨a ⊗ₜ[ℂ] (⟨residualOperator ρ π ρ' π' τ hτk hτl i f.val,
        hNstable i f.val f.property⟩ : N), rfl⟩
    | add t t' ht ht' => simpa only [map_add] using R.add_mem ht ht'
  have hR : R ≠ ⊥ := by
    intro hR
    have hm : f.val v ∈ R := ⟨v ⊗ₜ[ℂ] (⟨f, hfN⟩ : N), rfl⟩
    rw [hR, Submodule.mem_bot] at hm
    apply hf
    apply evalAt_injective ρ π ρ' π' h.irreducible hv
    exact hm
  have hRtop : R = ⊤ := (hjoint.2 R
    (by rintro k _ ⟨t, rfl⟩; exact hRk k t)
    (by rintro X _ ⟨t, rfl⟩; exact hRl X t)
    (by rintro i _ ⟨t, rfl⟩; exact hRτ i t)).resolve_left hR
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let Φ : V ⊗[ℂ] Multiplicity ρ π ρ' π' →ₗ[ℂ] Multiplicity ρ π ρ' π' :=
    (TensorProduct.lid ℂ _).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hΦ : ∀ t, Φ (T t) ∈ N := by
    intro t
    induction t with
    | tmul a f =>
      change φ a • f.val ∈ N
      exact N.smul_mem _ f.property
    | add t t' ht ht' => simpa only [map_add] using N.add_mem ht ht'
  apply eq_top_iff.mpr
  intro g _
  have hgR : g.val v ∈ R := hRtop ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := hgR
  have ht' : T t = v ⊗ₜ[ℂ] g := evaluation_injective ρ π ρ' π' h ht
  have hm := hΦ t
  rw [ht'] at hm
  have hval : Φ (v ⊗ₜ[ℂ] g) = g := by
    change φ v • g = g
    rw [hφ, one_smul]
  exact hval ▸ hm

end Langlands.Archimedean.GKTensorEvaluation
