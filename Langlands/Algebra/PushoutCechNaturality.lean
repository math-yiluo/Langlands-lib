import Langlands.Algebra.PushoutIdealTensor

/-! # Naturality of the componentwise pushout tensor map -/

universe u

open TensorProduct

namespace Langlands.Algebra.PushoutIdealTensor

section Naturality

variable {C A A' A₀ M M' : Type u} [CommRing C] [CommRing A] [CommRing A'] [CommRing A₀]
  [Algebra C A] [Algebra C A'] [Algebra C A₀]
  [AddCommGroup M] [Module C M] [Module A₀ M] [IsScalarTower C A₀ M]
  [AddCommGroup M'] [Module C M'] [Module A₀ M'] [IsScalarTower C A₀ M']
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (Γ Γ' Γ'' : ι → Type u) [∀ i, CommRing (Γ i)] [∀ i, CommRing (Γ' i)]
  [∀ i, CommRing (Γ'' i)] [∀ i, Algebra C (Γ i)]
  [∀ i, Algebra A (Γ' i)] [∀ i, Algebra C (Γ' i)] [∀ i, Algebra (Γ i) (Γ' i)]
  [∀ i, IsScalarTower C A (Γ' i)] [∀ i, IsScalarTower C (Γ i) (Γ' i)]
  [∀ i, Algebra.IsPushout C A (Γ i) (Γ' i)]
  [∀ i, Algebra A' (Γ'' i)] [∀ i, Algebra C (Γ'' i)] [∀ i, Algebra (Γ i) (Γ'' i)]
  [∀ i, IsScalarTower C A' (Γ'' i)] [∀ i, IsScalarTower C (Γ i) (Γ'' i)]
  [∀ i, Algebra.IsPushout C A' (Γ i) (Γ'' i)]
  (j : M →ₗ[C] A) (j' : M' →ₗ[C] A')

/-- The componentwise tensor map is natural in the test ring, the sections and the
coefficient module. -/
lemma cechTensorMap_natural (h : A →+* A') (H : ∀ i, Γ' i →+* Γ'' i)
    (hHA : ∀ i a, H i (algebraMap A (Γ' i) a) = algebraMap A' (Γ'' i) (h a))
    (hHΓ : ∀ i x, H i (algebraMap (Γ i) (Γ' i) x) = algebraMap (Γ i) (Γ'' i) x)
    (φ : M →ₗ[A₀] M') (hφ : ∀ m, j' (φ m) = h (j m))
    (y : (A₀ ⊗[C] (∀ i, Γ i)) ⊗[A₀] M) (i : ι) :
    H i (cechTensorMap Γ Γ' j y i) = cechTensorMap Γ Γ'' j' (φ.lTensor _ y) i := by
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [map_add, Pi.add_apply, h₁, h₂]
  | tmul t m =>
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, h₁, h₂]
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, cechTensorMap_tmul, cechTensorMap_tmul, map_mul, hHA, hHΓ,
        ← φ.map_smul, hφ]

/-- The componentwise tensor map intertwines a differential on the sections with an
`A`-linear differential on the base-changed sections. -/
lemma cechTensorMap_differential {κ : Type u} [Fintype κ] [DecidableEq κ]
    (Γ₁ Γ₁' : κ → Type u) [∀ t, CommRing (Γ₁ t)] [∀ t, CommRing (Γ₁' t)]
    [∀ t, Algebra C (Γ₁ t)] [∀ t, Algebra A (Γ₁' t)] [∀ t, Algebra C (Γ₁' t)]
    [∀ t, Algebra (Γ₁ t) (Γ₁' t)] [∀ t, IsScalarTower C A (Γ₁' t)]
    [∀ t, IsScalarTower C (Γ₁ t) (Γ₁' t)] [∀ t, Algebra.IsPushout C A (Γ₁ t) (Γ₁' t)]
    (D : (∀ i, Γ i) →ₗ[C] (∀ t, Γ₁ t)) (D' : (∀ i, Γ' i) →ₗ[A] (∀ t, Γ₁' t))
    (hD : ∀ x : ∀ i, Γ i, D' (fun i => algebraMap (Γ i) (Γ' i) (x i)) =
      fun t => algebraMap (Γ₁ t) (Γ₁' t) (D x t))
    (y : (A₀ ⊗[C] (∀ i, Γ i)) ⊗[A₀] M) :
    cechTensorMap Γ₁ Γ₁' j ((D.baseChange A₀).rTensor M y) = D' (cechTensorMap Γ Γ' j y) := by
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul t m =>
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
    | tmul a x =>
      have hx : cechTensorMap Γ Γ' j ((a ⊗ₜ[C] x) ⊗ₜ[A₀] m) =
          j (a • m) • fun i => algebraMap (Γ i) (Γ' i) (x i) := by
        funext i
        rw [cechTensorMap_tmul, Pi.smul_apply, Algebra.smul_def]
      rw [hx, LinearMap.map_smul, hD, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]
      funext t
      rw [cechTensorMap_tmul, Pi.smul_apply, Algebra.smul_def]

/-- If the coefficient ideal is square zero, products of values of the componentwise tensor
map vanish. -/
lemma cechTensorMap_mul_eq_zero (hj : ∀ m m', j m * j m' = 0)
    (y y' : (A₀ ⊗[C] (∀ i, Γ i)) ⊗[A₀] M) (i : ι) :
    cechTensorMap Γ Γ' j y i * cechTensorMap Γ Γ' j y' i = 0 := by
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [map_add, Pi.add_apply, add_mul, h₁, h₂, add_zero]
  | tmul t m =>
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, add_mul, h₁, h₂, add_zero]
    | tmul a x =>
      induction y' using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, Pi.add_apply, mul_add, h₁, h₂, add_zero]
      | tmul t' m' =>
        induction t' using TensorProduct.inductionOn with
        | add t₁ t₂ h₁ h₂ =>
          simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, mul_add, h₁, h₂, add_zero]
        | tmul a' x' =>
          rw [cechTensorMap_tmul, cechTensorMap_tmul]
          calc _ = algebraMap A (Γ' i) (j (a • m) * j (a' • m')) *
                (algebraMap (Γ i) (Γ' i) (x i) * algebraMap (Γ i) (Γ' i) (x' i)) := by
                rw [map_mul]; ring
            _ = 0 := by rw [hj, map_zero, zero_mul]

end Naturality

section Finiteness

variable {A : Type u} [CommRing A] {C C' : ℕ → Type u} [∀ i, AddCommGroup (C i)]
  [∀ i, Module A (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module A (C' i)]
  (d : ∀ i, C i →ₗ[A] C (i + 1)) (d' : ∀ i, C' i →ₗ[A] C' (i + 1))
  (e : ∀ i, C i ≃ₗ[A] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x))

/-- The cohomology modules of a cochain complex `(C, d)` of `A`-modules are finitely
generated, in the form used by `ObstructionCone.OpenStatement`. -/
def FiniteCohomology : Prop :=
  Module.Finite A (LinearMap.ker (d 0)) ∧
    ∀ i, Module.Finite A (LinearMap.ker (d (i + 1)) ⧸
      (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)

include he

/-- Finiteness of degree-zero cohomology transfers along an isomorphism of complexes. -/
lemma finite_ker_of_equiv [Module.Finite A (LinearMap.ker (d' 0))] :
    Module.Finite A (LinearMap.ker (d 0)) := by
  have hmem : ∀ x ∈ LinearMap.ker (d' 0), (e 0).symm x ∈ LinearMap.ker (d 0) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply (e 1).injective
    rw [he, LinearEquiv.apply_symm_apply, hx, map_zero]
  let g : LinearMap.ker (d' 0) →ₗ[A] LinearMap.ker (d 0) :=
    ((e 0).symm.toLinearMap.restrict hmem)
  refine Module.Finite.of_surjective g ?_
  rintro ⟨x, hx⟩
  refine ⟨⟨e 0 x, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [← he, hx, map_zero]
  · apply Subtype.ext
    simp [g]

/-- Finiteness of higher cohomology transfers along an isomorphism of complexes. -/
lemma finite_homology_of_equiv (i : ℕ)
    [Module.Finite A (LinearMap.ker (d' (i + 1)) ⧸
      (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)] :
    Module.Finite A (LinearMap.ker (d (i + 1)) ⧸
      (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) := by
  have hmem : ∀ x ∈ LinearMap.ker (d' (i + 1)),
      (e (i + 1)).symm x ∈ LinearMap.ker (d (i + 1)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply (e (i + 1 + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hx, map_zero]
  let g : LinearMap.ker (d' (i + 1)) →ₗ[A] LinearMap.ker (d (i + 1)) :=
    ((e (i + 1)).symm.toLinearMap.restrict hmem)
  have hrange : (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype ≤
      ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype).comap g := by
    rintro ⟨x, hx⟩ ⟨y, rfl⟩
    refine ⟨(e i).symm y, ?_⟩
    apply (e (i + 1)).injective
    simp [g, he]
  let g' := Submodule.mapQ _ _ g hrange
  refine Module.Finite.of_surjective g' ?_
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ z
  refine ⟨Submodule.Quotient.mk ⟨e (i + 1) x, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [← he, hx, map_zero]
  · simp only [g', Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    simp [g]

/-- Finiteness of all cohomology modules transfers along an isomorphism of complexes. -/
lemma finiteCohomology_of_equiv (h : FiniteCohomology d') : FiniteCohomology d := by
  obtain ⟨h₀, h₁⟩ := h
  exact ⟨finite_ker_of_equiv d d' e he, fun i => finite_homology_of_equiv d d' e he i⟩

end Finiteness

end Langlands.Algebra.PushoutIdealTensor
