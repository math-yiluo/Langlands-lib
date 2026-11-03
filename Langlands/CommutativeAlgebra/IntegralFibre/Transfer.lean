import Langlands.CommutativeAlgebra.IntegralFibre.ModelSplit
import Langlands.CommutativeAlgebra.IntegralFibre.TaylorSmooth

/-! # From a Noetherian model to local splitting -/

open TensorProduct MvPolynomial

namespace Langlands.CommutativeAlgebra.IntegralFibre

section Transfer

lemma LocallySplit.of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : LocallySplit R M) : LocallySplit R N := by
  intro n x
  obtain ⟨r, φ, y, hy⟩ := h n (fun i ↦ e.symm (x i))
  refine ⟨r, φ ∘ₗ e.symm.toLinearMap, fun j ↦ e (y j), fun i ↦ ?_⟩
  have := congrArg e (hy i)
  simpa [map_sum, map_smul] using this

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
variable {R₀ S₀ : Type*} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [Algebra R₀ B]
  (e : B ⊗[R₀] S₀ ≃ₐ[B] S)

/-- The model map `S₀ → S`. -/
noncomputable def modelMap : S₀ →+* S :=
  e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R₀) (A := B) (B := S₀)).toRingHom

lemma modelMap_apply (s : S₀) : modelMap e s = e (1 ⊗ₜ s) := rfl

variable (σ : S →ₐ[B] B) (σ₀ : S₀ →ₐ[R₀] R₀)
  (hσ : ∀ s, algebraMap R₀ B (σ₀ s) = σ (modelMap e s))
  {d : ℕ} (t : Fin d → S) (t₀ : Fin d → S₀) (htt : ∀ i, modelMap e (t₀ i) = t i)
include htt in
lemma tpow_modelMap (α : Fin d →₀ ℕ) :
    modelMap e (tpow (A := R₀) t₀ α) = tpow (A := B) t α := by
  simp only [tpow, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod, map_prod,
    map_pow, htt]

lemma modelMap_algebraMap (a : R₀) :
    modelMap e (algebraMap R₀ S₀ a) = algebraMap B S (algebraMap R₀ B a) := by
  rw [modelMap_apply, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, ← Algebra.TensorProduct.algebraMap_apply]
  exact e.commutes _

include hσ in
lemma ker_le_comap_modelMap : RingHom.ker σ₀ ≤ (RingHom.ker σ).comap (modelMap e) := by
  intro s hs
  rw [Ideal.mem_comap, RingHom.mem_ker, ← hσ, RingHom.mem_ker.mp hs, map_zero]

include hσ htt in
/-- Injectivity of the model Taylor maps follows from injectivity over `B`. -/
lemma theta_injective_of_model (hinj : Function.Injective (algebraMap R₀ B))
    (hθB : ∀ k, Function.Injective (theta σ t k)) (k : ℕ) :
    Function.Injective (theta σ₀ t₀ k) := by
  have hle : RingHom.ker σ₀ ^ k ≤ (RingHom.ker σ ^ k).comap (modelMap e) :=
    (Ideal.pow_right_mono (ker_le_comap_modelMap e σ σ₀ hσ) k).trans (Ideal.le_comap_pow _ k)
  let ι := Ideal.quotientMap (RingHom.ker σ ^ k) (modelMap e) hle
  have hsq : ∀ c, ι (theta σ₀ t₀ k c) =
      theta σ t k (Finsupp.mapRange (algebraMap R₀ B) (map_zero _) c) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c c' hc hc' => rw [map_add, map_add, hc, hc', Finsupp.mapRange_add (map_add _), map_add]
    | single α a =>
      rw [Finsupp.mapRange_single, theta_single, theta_single, Algebra.smul_def, Algebra.smul_def,
        map_mul]
      congr 1
      · rw [IsScalarTower.algebraMap_apply R₀ S₀ (S₀ ⧸ _),
          IsScalarTower.algebraMap_apply B S (S ⧸ _), Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk, modelMap_algebraMap]
      · rw [Ideal.quotientMap_mk, tpow_modelMap e t t₀ htt]
  rw [injective_iff_map_eq_zero]
  intro c hc
  have h1 := hsq c
  rw [hc, map_zero] at h1
  have h2 := hθB k (h1.symm.trans (map_zero _).symm)
  ext α
  have := congrArg (· α) h2
  simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at this
  exact hinj (this.trans (map_zero _).symm)

include hσ in
/-- Fibre injectivity over the model, from integrality of the fibres over `B`. -/
lemma smulInjOn_of_isDomain (P : Ideal B) [P.IsPrime] [IsDomain (P.ResidueField ⊗[B] S)]
    (u : S₀) (hu : σ₀ u = 1) : SMulInjOn R₀ u P.ResidueField := by
  let Φ : S₀ ⊗[R₀] P.ResidueField ≃+* P.ResidueField ⊗[B] S :=
    (Algebra.TensorProduct.comm R₀ S₀ P.ResidueField).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R₀ B P.ResidueField P.ResidueField
        S₀).symm.toRingEquiv.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : P.ResidueField ≃ₐ[B] P.ResidueField)
          e).toRingEquiv)
  have hΦu : Φ (u ⊗ₜ 1) = 1 ⊗ₜ modelMap e u := by
    simp [Φ, modelMap_apply]
  let ε : P.ResidueField ⊗[B] S →ₐ[B] P.ResidueField :=
    Algebra.TensorProduct.lift (AlgHom.id B P.ResidueField) ((Algebra.ofId B P.ResidueField).comp σ)
      (fun _ _ ↦ Commute.all _ _)
  have hne : Φ (u ⊗ₜ 1) ≠ 0 := by
    intro h0
    have h1 := congrArg ε h0
    rw [hΦu, map_zero] at h1
    simp only [ε, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
      one_mul, ← hσ, hu, map_one] at h1
    exact one_ne_zero h1
  have hmul : ∀ z : S₀ ⊗[R₀] P.ResidueField, u • z = (u ⊗ₜ 1) * z := by
    intro z
    induction z with
    | tmul s k => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, mul_add, hx, hy]
  intro a b hab
  simp only at hab
  rw [hmul, hmul] at hab
  apply Φ.injective
  have := congrArg Φ hab
  rw [map_mul, map_mul] at this
  exact mul_left_cancel₀ hne this

include hσ htt in
/-- **Local splitting from a Noetherian model.** -/
theorem locallySplit_of_noetherianModel [IsNoetherianRing R₀] [IsNoetherianRing S₀]
    [Module.Flat R₀ S₀] (hinj : Function.Injective (algebraMap R₀ B))
    (ht : ∀ i, σ (t i) = 0)
    (hJ₀ : RingHom.ker σ₀ ≤ Ideal.span (Set.range t₀) ⊔ RingHom.ker σ₀ ^ 2)
    (hθB : ∀ k, Function.Injective (theta σ t k))
    (hfib : ∀ (P : Ideal B) [P.IsPrime], IsDomain (P.ResidueField ⊗[B] S)) :
    LocallySplit B S := by
  have ht₀ : ∀ i, σ₀ (t₀ i) = 0 := fun i ↦ hinj (by rw [hσ, htt, ht, map_zero])
  have hθ : ∀ k, Function.Bijective (theta σ₀ t₀ k) := fun k ↦
    ⟨theta_injective_of_model e σ σ₀ hσ t t₀ htt hinj hθB k, theta_surjective σ₀ t₀ ht₀ hJ₀ k⟩
  have hfib₀ : ∀ (P : Ideal B) [P.IsPrime] (u : S₀), σ₀ u = 1 →
      SMulInjOn R₀ u P.ResidueField :=
    fun P _ u hu ↦ smulInjOn_of_isDomain e σ σ₀ hσ P u hu
  exact LocallySplit.of_linearEquiv e.toLinearEquiv (locallySplit_of_model σ₀ t₀ ht₀ hθ hfib₀)

end Transfer

end Langlands.CommutativeAlgebra.IntegralFibre
