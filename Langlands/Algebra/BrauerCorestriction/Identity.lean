import Langlands.Algebra.BrauerCorestriction.BrauerClass

/-!
# Corestriction along the identity extension

For `L = K` there is exactly one `K`-embedding `K → N`, the tensor product of conjugates is
`N ⊗[K] A`, and the descended algebra is `A` itself, embedded by `a ↦ ⨂ (1 ⊗ a)`. Hence the
corestriction `BrauerGroup K → BrauerGroup K` along the identity extension is the identity.
-/

universe u u₁ u₃ u₄

open TensorProduct PiTensorProduct Module

namespace Langlands.BrauerCorestriction

section Identity

variable (K : Type u₁) (N : Type u₃) [Field K] [Field N] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra K A]

/-- The pure tensor `⨂_σ (1 ⊗ a)` over the `K`-embeddings `σ : K → N` (there is only one). -/
noncomputable def idTensor (a : A) : ConjTensor K K N A :=
  PiTensorProduct.tprod N (fun σ : K →ₐ[K] N => (1 : Twist σ) ⊗ₜ[K] a)

theorem one_tmul_smul (σ : K →ₐ[K] N) (k : K) (a : A) :
    (1 : Twist σ) ⊗ₜ[K] (k • a) = (algebraMap K N k) • ((1 : Twist σ) ⊗ₜ[K] a) := by
  rw [← TensorProduct.smul_tmul, smul_tmul']
  congr 1
  change ((σ : K →+* N) k * 1 : N) = algebraMap K N k * 1
  rw [AlgHom.coe_toRingHom, mul_one, mul_one]
  exact σ.commutes k

/-- The embedding `A → ⨂_σ (N ⊗_σ A)`, `a ↦ ⨂_σ (1 ⊗ a)`, over the unique `K`-embedding
`σ : K → N`. -/
noncomputable def idEmbed : A →ₐ[K] ConjTensor K K N A := by
  classical
  let σ₀ : K →ₐ[K] N := Algebra.ofId K N
  have hS : ∀ f : ∀ σ : K →ₐ[K] N, Conj A σ,
      subsingletonEquiv (R := N) (s := fun σ : K →ₐ[K] N => Conj A σ) σ₀
        (PiTensorProduct.tprod N f) = f σ₀ := fun f => subsingletonEquiv_apply_tprod σ₀ f
  refine AlgHom.ofLinearMap
    { toFun := idTensor K N A
      map_add' := fun a b => ?_
      map_smul' := fun k a => ?_ } ?_ ?_
  · apply (subsingletonEquiv (R := N) (s := fun σ : K →ₐ[K] N => Conj A σ) σ₀).injective
    simp only [idTensor, map_add, hS, tmul_add]
  · simp only [idTensor, RingHom.id_apply]
    have hf : (fun σ : K →ₐ[K] N => (1 : Twist σ) ⊗ₜ[K] (k • a)) =
        fun σ => (fun _ => algebraMap K N k) σ • ((1 : Twist σ) ⊗ₜ[K] a) :=
      funext fun σ => one_tmul_smul K N A σ k a
    rw [hf, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_one_iff.mpr ⟨σ₀, fun σ => Subsingleton.elim _ _⟩, pow_one, algebraMap_smul]
  · rfl
  · intro a b
    simp only [LinearMap.coe_mk, AddHom.coe_mk, idTensor, tprod_mul_tprod]
    congr 1
    funext σ
    simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem idEmbed_apply (a : A) : idEmbed K N A a = idTensor K N A a := rfl

theorem idEmbed_mem_corAlg (a : A) : idEmbed K N A a ∈ corAlg K K N A := by
  rw [mem_corAlg]
  intro g
  rw [idEmbed_apply, idTensor, actMap_tprod]
  congr 1
  funext τ
  rw [conjMap_tmul, twistHom_apply]
  congr 1
  exact map_one g

/-- The embedding of `A` into its descended algebra along the identity extension. -/
noncomputable def idCorHom : A →ₐ[K] corAlg K K N A :=
  (idEmbed K N A).codRestrict (corAlg K K N A) (idEmbed_mem_corAlg K N A)

variable [FiniteDimensional K N] [IsGalois K N] [FiniteDimensional K A] [IsSimpleRing A]

theorem idCorHom_bijective : Function.Bijective (idCorHom K N A) := by
  have : FiniteDimensional K (corAlg K K N A) := finiteDimensional_corAlg K K N A
  have hcard : Nat.card (K →ₐ[K] N) = 1 := Nat.card_of_subsingleton (Algebra.ofId K N)
  have hpos : 0 < finrank K (corAlg K K N A) := by
    rw [finrank_corAlg_eq_pow]
    exact pow_pos Module.finrank_pos _
  have : Nontrivial (corAlg K K N A) := Module.nontrivial_of_finrank_pos hpos
  have hinj : Function.Injective (idCorHom K N A) := by
    rcases IsSimpleRing.injective_ringHom_or_subsingleton_codomain (R := A)
      (S := corAlg K K N A) (idCorHom K N A).toRingHom with h | h
    · exact h
    · exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hd : finrank K A = finrank K (corAlg K K N A) := by
    rw [finrank_corAlg_eq_pow, hcard, pow_one]
  have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := K)
    (V := A) (V₂ := corAlg K K N A) (f := (idCorHom K N A).toLinearMap) hd
  exact key.mp hinj

/-- Along the identity extension the descended algebra is the original algebra. -/
noncomputable def idCorEquiv : A ≃ₐ[K] corAlg K K N A :=
  AlgEquiv.ofBijective (idCorHom K N A) (idCorHom_bijective K N A)

end Identity

section Brauer

variable (K : Type u) [Field K]

/-- Corestriction along the identity extension `K/K` is the identity of `BrauerGroup K`. -/
theorem cor_self : cor K K = id := by
  have hN : Nat.card (K →ₐ[K] K) = finrank K K := by
    rw [Nat.card_of_subsingleton (AlgHom.id K K), Module.finrank_self]
  funext x
  induction x using Quotient.ind with
  | _ A =>
    rw [cor_mk_eq_of_closure K K K hN A]
    apply Quotient.sound (s := Brauer.CSA_Setoid K)
    exact isBrauerEquivalent_of_algEquiv (idCorEquiv K K A).symm

end Brauer

end Langlands.BrauerCorestriction
