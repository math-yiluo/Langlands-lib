import Langlands.ClassFieldTheory.Local.ClosureInflationIndependenceStatement

/-! # Proof that closure inflation does not depend on the chosen isomorphism

Transport of relative `H²` along field isomorphisms is functorial, and transport
along an automorphism is the identity (inner automorphisms act trivially). Two
`K`-isomorphic normal subfields of the algebraic closure coincide, so two
identifications differ by an automorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u v w x

section Transport

variable {K : Type u} {L : Type v} {M : Type w} {N : Type x}
  [Field K] [Field L] [Field M] [Field N] [Algebra K L] [Algebra K M] [Algebra K N]

theorem relativeAutPullback_trans (e : L ≃ₐ[K] M) (e' : M ≃ₐ[K] N) (s : Gal(N/K)) :
    relativeAutPullback (e.trans e') s =
      relativeAutPullback e (relativeAutPullback e' s) := by
  ext y
  simp

theorem relativeAutPullback_refl (s : Gal(L/K)) :
    relativeAutPullback (AlgEquiv.refl : L ≃ₐ[K] L) s = s := by
  ext y
  simp

/-- Pulling back along an automorphism is conjugation in the Galois group. -/
theorem relativeAutPullback_self (τ s : Gal(L/K)) :
    relativeAutPullback τ s = τ⁻¹ * s * τ := by
  ext y
  simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv]

/-- On an automorphism, the unit transport is the Galois action. -/
theorem relativeUnitTransport_self (τ : Gal(L/K)) (a : unitsRepresentation K L) :
    relativeUnitTransport τ a = (unitsRepresentation K L).ρ τ a := by
  apply Units.ext
  rfl

theorem relativeCocycleTransport_trans (e : L ≃ₐ[K] M) (e' : M ≃ₐ[K] N)
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    relativeCocycleTransport (e.trans e') z =
      relativeCocycleTransport e' (relativeCocycleTransport e z) := by
  apply groupCohomology.cocycles₂_ext
  intro s t
  simp only [relativeCocycleTransport_apply, relativeAutPullback_trans]
  apply Units.ext
  rfl

theorem relativeCocycleTransport_refl
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    relativeCocycleTransport (AlgEquiv.refl : L ≃ₐ[K] L) z = z := by
  apply groupCohomology.cocycles₂_ext
  intro s t
  simp only [relativeCocycleTransport_apply, relativeAutPullback_refl]
  apply Units.ext
  rfl

/-- Transport of relative `H²` along a composite is the composite of transports. -/
theorem relativeH2Equiv_trans (e : L ≃ₐ[K] M) (e' : M ≃ₐ[K] N)
    (y : relativeCohomology K L 2) :
    relativeH2Equiv (e.trans e') y = relativeH2Equiv e' (relativeH2Equiv e y) := by
  induction y using groupCohomology.H2_induction_on with | h z =>
    rw [relativeH2Equiv_H2π, relativeH2Equiv_H2π, relativeH2Equiv_H2π,
      relativeCocycleTransport_trans]

/-- Transport of relative `H²` along the identity is the identity. -/
theorem relativeH2Equiv_refl (y : relativeCohomology K L 2) :
    relativeH2Equiv (AlgEquiv.refl : L ≃ₐ[K] L) y = y := by
  induction y using groupCohomology.H2_induction_on with | h z =>
    rw [relativeH2Equiv_H2π, relativeCocycleTransport_refl]

/-- Inner automorphisms act trivially: transport of relative `H²` along an
automorphism is the identity. The explicit primitive is
`b g = z (τ, τ⁻¹ g τ) - z (g, τ)`. -/
theorem relativeH2Equiv_self (τ : Gal(L/K)) (y : relativeCohomology K L 2) :
    relativeH2Equiv τ y = y := by
  induction y using groupCohomology.H2_induction_on with | h z =>
    rw [relativeH2Equiv_H2π]
    apply (groupCohomology.H2π_eq_iff _ _).2
    refine ⟨fun g => z (τ, τ⁻¹ * g * τ) - z (g, τ), ?_⟩
    funext st
    rcases st with ⟨s, t⟩
    have hz := (groupCohomology.mem_cocycles₂_iff (z : Gal(L/K) × Gal(L/K) → _)).1 z.2
    have h₁ := hz τ (τ⁻¹ * s * τ) (τ⁻¹ * t * τ)
    have h₂ := hz s τ (τ⁻¹ * t * τ)
    have h₃ := hz s t τ
    have e₁ : τ * (τ⁻¹ * s * τ) = s * τ := by group
    have e₂ : τ⁻¹ * s * τ * (τ⁻¹ * t * τ) = τ⁻¹ * (s * t) * τ := by group
    have e₃ : τ * (τ⁻¹ * t * τ) = t * τ := by group
    rw [e₁, e₂] at h₁
    rw [e₃] at h₂
    simp only [Pi.sub_apply, groupCohomology.d₁₂_hom_apply, relativeCocycleTransport_apply]
    rw [relativeAutPullback_self, relativeAutPullback_self, relativeUnitTransport_self,
      map_sub]
    have h₁' := eq_sub_of_add_eq h₁.symm
    rw [h₁']
    have h₂' := eq_sub_of_add_eq h₂
    have h₃' := eq_sub_of_add_eq' h₃.symm
    rw [h₂', h₃']
    abel

end Transport

/-- Closure inflation does not depend on the isomorphism used to place `L` in
the algebraic closure. -/
theorem closureInflationTransportIndependence :
    ClosureInflationTransportIndependence.{u,v} := by
  intro K _ L _ _ E₁ E₂ _ _ _ _ e₁ e₂ y
  have hE : E₁ = E₂ := by
    let ψ : E₂ →ₐ[K] AlgebraicClosure K :=
      E₁.val.comp (e₂.symm.trans e₁).toAlgHom
    have h₂ : ψ.fieldRange = E₂ := AlgHom.fieldRange_of_normal ψ
    have h₁ : ψ.fieldRange = E₁ := by
      ext a
      constructor
      · rintro ⟨w, rfl⟩
        exact (e₁ (e₂.symm w)).2
      · intro ha
        refine ⟨e₂ (e₁.symm ⟨a, ha⟩), ?_⟩
        simp [ψ]
    rw [← h₁, h₂]
  subst hE
  have he : e₂ = e₁.trans (e₁.symm.trans e₂) := by
    ext a
    simp
  rw [he, relativeH2Equiv_trans, relativeH2Equiv_self]

end Langlands.ClassFieldTheory.Local
