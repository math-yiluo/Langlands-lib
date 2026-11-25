import Langlands.MathlibBase

/-! # Approximating derivations of `k` by derivations of a field extension

This is the linear-algebra input to the claim in the proof of Stacks, Smoothing Ring Maps,
Lemma 16.11.1 (07FG): if `H₁(L_{κ/k})` is finite dimensional, then every derivation of `k` with
values in a `κ`-module agrees with the restriction of a derivation of `κ` modulo a finitely
generated `k`-submodule. -/

namespace Langlands.CommutativeAlgebra.Popescu.ArtinianFlat

open KaehlerDifferential TensorProduct Module

/-- If `H₁(L_{κ/k})` is finite, the kernel of `κ ⊗_k Ω_{k/ℤ} → Ω_{κ/ℤ}` is finitely generated. -/
theorem fg_ker_mapBaseChange {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (h : Module.Finite κ (Algebra.H1Cotangent k κ)) :
    (LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ k κ)).FG := by
  rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ k κ).linearMap_ker_eq, LinearMap.range_eq_map]
  exact h.fg_top.map _

/-- If the kernel of `κ ⊗_k Ω_{k/ℤ} → Ω_{κ/ℤ}` is finitely generated, then every derivation
`θ : k → I` into a `κ`-module agrees with the restriction of a derivation `D : κ → I` up to a
finitely generated `k`-submodule of `I`. -/
theorem exists_derivation_approx {k κ I : Type*} [Field k] [Field κ] [Algebra k κ]
    [AddCommGroup I] [Module κ I] [Module k I] [IsScalarTower k κ I]
    (hV : (LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ k κ)).FG)
    (θ : Derivation ℤ k I) :
    ∃ (D : Derivation ℤ κ I) (S : Finset I), ∀ a : k,
      θ a - D (algebraMap k κ a) ∈ Submodule.span k (S : Set I) := by
  classical
  set φ := KaehlerDifferential.mapBaseChange ℤ k κ
  let b := Basis.ofVectorSpace k Ω[k⁄ℤ]
  let bκ := Algebra.TensorProduct.basis κ b
  obtain ⟨G, hG⟩ := hV
  let J0 : Finset _ := G.biUnion (fun v ↦ (bκ.repr v).support)
  have hVle : LinearMap.ker φ ≤ Submodule.span κ (bκ '' (J0 : Set _)) := by
    rw [← hG, Submodule.span_le]
    intro v hv
    refine Submodule.span_mono ?_ (bκ.mem_span_repr_support v)
    refine Set.image_mono ?_
    intro i hi
    simp only [J0, Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨v, hv, hi⟩
  let w : {i // i ∉ J0} → Ω[κ⁄ℤ] := fun i ↦ φ (bκ i)
  have hli : LinearIndependent κ w := by
    have h1 : LinearIndependent κ (fun i : {i // i ∉ J0} ↦ bκ i) :=
      bκ.linearIndependent.comp _ Subtype.val_injective
    refine h1.map (f := φ) ?_
    refine Disjoint.mono_right hVle ?_
    have hr : Set.range (fun i : {i // i ∉ J0} ↦ bκ i) = bκ '' {i | i ∉ J0} := by
      ext x
      simp
    rw [hr]
    exact bκ.linearIndependent.disjoint_span_image (by
      rw [Set.disjoint_left]
      intro i hi hi'
      exact hi hi')
  let ξ : κ ⊗[k] Ω[k⁄ℤ] →ₗ[κ] I := θ.liftKaehlerDifferential.liftBaseChange κ
  let ℓ₀ := (Basis.span hli).constr κ (fun i ↦ ξ (bκ i))
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓw : ∀ i : {i // i ∉ J0}, ℓ (w i) = ξ (bκ i) := by
    intro i
    have h1 : ((Basis.span hli i : Submodule.span κ (Set.range w)) : Ω[κ⁄ℤ]) = w i := by
      rw [Basis.span_apply]
    have h2 := congrArg (fun f ↦ f (Basis.span hli i)) hℓ
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h1] at h2
    rw [h2]
    exact (Basis.span hli).constr_basis κ (fun i ↦ ξ (bκ i)) i
  let η : Ω[k⁄ℤ] →ₗ[k] I := ((ξ - ℓ ∘ₗ φ).restrictScalars k) ∘ₗ (TensorProduct.mk k κ _ 1)
  have hηapp : ∀ x, η x = ξ (1 ⊗ₜ x) - ℓ (φ (1 ⊗ₜ x)) := fun x ↦ rfl
  have hη : ∀ i ∉ J0, η (b i) = 0 := by
    intro i hi
    have := hℓw ⟨i, hi⟩
    simp only [w, bκ, Algebra.TensorProduct.basis_apply] at this
    rw [hηapp, this, sub_self]
  refine ⟨ℓ.compDer (KaehlerDifferential.D ℤ κ), J0.image (fun i ↦ η (b i)), fun a ↦ ?_⟩
  have key : θ a - ℓ.compDer (KaehlerDifferential.D ℤ κ) (algebraMap k κ a) =
      η (KaehlerDifferential.D ℤ k a) := by
    rw [hηapp]
    have h1 : ξ (1 ⊗ₜ KaehlerDifferential.D ℤ k a) = θ a := by
      simp only [ξ, LinearMap.liftBaseChange_tmul, one_smul,
        Derivation.liftKaehlerDifferential_comp_D]
    have h2 : φ (1 ⊗ₜ KaehlerDifferential.D ℤ k a) =
        KaehlerDifferential.D ℤ κ (algebraMap k κ a) := by
      simp only [φ, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    rw [h1, h2]
    rfl
  rw [key]
  have hle : Submodule.span k (Set.range b) ≤
      (Submodule.span k ((J0.image (fun i ↦ η (b i)) : Finset I) : Set I)).comap η := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ J0
    · exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨i, hi, rfl⟩)
    · simp only [SetLike.mem_coe, Submodule.mem_comap, hη i hi, zero_mem]
  exact hle (b.span_eq ▸ Submodule.mem_top)

/-- A variant of `exists_derivation_approx` for a map `θ : k → I` satisfying the Leibniz rule with
respect to the `κ`-module structure of `I`; the conclusion is stated with explicit coefficients. -/
theorem exists_derivation_approx' {k κ I : Type*} [Field k] [Field κ] [Algebra k κ]
    [AddCommGroup I] [Module κ I]
    (hV : (LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ k κ)).FG)
    (θ : k → I) (hadd : ∀ a b, θ (a + b) = θ a + θ b)
    (hmul : ∀ a b, θ (a * b) = algebraMap k κ a • θ b + algebraMap k κ b • θ a) :
    ∃ (D : Derivation ℤ κ I) (S : Finset I), ∀ a : k, ∃ c : I → k,
      θ a - D (algebraMap k κ a) = ∑ s ∈ S, algebraMap k κ (c s) • s := by
  let _ : Module k I := Module.compHom I (algebraMap k κ)
  have _ : IsScalarTower k κ I := ⟨fun c ζ x ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let θ' : Derivation ℤ k I :=
    Derivation.mk' (AddMonoidHom.mk' θ hadd).toIntLinearMap (fun a b ↦ hmul a b)
  obtain ⟨D, S, hS⟩ := exists_derivation_approx hV θ'
  refine ⟨D, S, fun a ↦ ?_⟩
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp (hS a)
  exact ⟨c, hc.symm⟩

end Langlands.CommutativeAlgebra.Popescu.ArtinianFlat
