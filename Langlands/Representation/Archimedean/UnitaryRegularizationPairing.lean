import Langlands.Representation.Archimedean.UnitaryRegularizationGraph
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace Langlands.Archimedean

variable {G V E : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem denseRange_of_nonzero_intertwining (π : G →* (E →L[ℂ] E))
    (hirr : IsTopologicallyIrreducible π) (L : G → V → V) (S : V →ₗ[ℂ] E) (hS : S ≠ 0)
    (hL : ∀ g f, S (L g f) = π g (S f)) : DenseRange S := by
  let W := S.range.topologicalClosure
  have hstable (g : G) : Set.MapsTo (π g) (W : Set E) W := by
    apply Set.MapsTo.closure _ (π g).continuous
    rintro _ ⟨v, rfl⟩
    exact ⟨L g v, hL g v⟩
  rcases hirr.2 W S.range.isClosed_topologicalClosure hstable with hb | ht
  · exfalso
    exact hS (LinearMap.range_eq_bot.mp (le_bot_iff.mp (hb ▸ S.range.le_topologicalClosure)))
  · exact denseRange_iff_closure_range.mpr
      (congrArg (fun U : Submodule ℂ E => (U : Set E)) ht)

private theorem exists_hilbertConjugation :
    ∃ γ : E ≃ₗᵢ⋆[ℂ] E, ∀ x y, inner ℂ (γ x) (γ y) = inner ℂ y x := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  let γ : E ≃ₗᵢ⋆[ℂ] E := b.repr.trans ((starₗᵢ ℂ).trans b.repr.symm)
  refine ⟨γ, fun x y => ?_⟩
  change inner ℂ (b.repr.symm (star (b.repr x))) (b.repr.symm (star (b.repr y))) = _
  rw [b.repr.symm.inner_map_map, ← b.repr.inner_map_map y x]
  simp only [lp.inner_eq_tsum, lp.star_apply, RCLike.inner_apply, starRingEnd_apply,
    star_star, mul_comm]

private theorem adjoint_intertwines (π σ : G →* (E →L[ℂ] E))
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (T : E →L[ℂ] E) (hT : ∀ g x, T (π g x) = σ g (T x)) (g : G) (y : E) :
    T.adjoint (σ g y) = π g (T.adjoint y) := by
  have hInv (x : E) : π g (π g⁻¹ x) = x := by
    change (π g * π g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  apply ext_inner_right ℂ
  intro x
  calc
    inner ℂ (T.adjoint (σ g y)) x = inner ℂ (σ g y) (σ g (T (π g⁻¹ x))) := by
      rw [ContinuousLinearMap.adjoint_inner_left, ← hT, hInv]
    _ = inner ℂ y (T (π g⁻¹ x)) := hσ g _ _
    _ = inner ℂ (π g (T.adjoint y)) x := by
      rw [← ContinuousLinearMap.adjoint_inner_left T (π g⁻¹ x) y,
        ← hπ g (T.adjoint y) (π g⁻¹ x), hInv]

/-- Pairing symmetry for two equivariant regularizations and for the self-pairing of the
nonzero reference regularization implies proportionality of the regularizations. -/
theorem proportional_of_unitary_regularization_symmetry (π : G →* (E →L[ℂ] E))
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hirr : IsTopologicallyIrreducible π) (θ : G ≃* G) (J : V ≃ₗ⋆[ℂ] V) (L : G → V → V)
    (hJ : ∀ g f, J (L g f) = L (θ g) (J f)) (S₀ S₁ : V →ₗ[ℂ] E) (h₀ : S₀ ≠ 0)
    (hL₀ : ∀ g f, S₀ (L g f) = π g (S₀ f)) (hL₁ : ∀ g f, S₁ (L g f) = π g (S₁ f))
    (hsym₀ : ∀ f g, inner ℂ (S₀ f) (S₀ g) = inner ℂ (S₀ (J g)) (S₀ (J f)))
    (hsym₁ : ∀ f g, inner ℂ (S₁ f) (S₀ g) = inner ℂ (S₁ (J g)) (S₀ (J f))) :
    ∃ c : ℂ, S₁ = c • S₀ := by
  by_cases h₁ : S₁ = 0
  · exact ⟨0, by rw [h₁, zero_smul]⟩
  obtain ⟨γ, hγ⟩ := exists_hilbertConjugation (E := E)
  let σ : G →* (E →L[ℂ] E) :=
    { toFun := fun g => γ.toLinearIsometry.toContinuousLinearMap.comp
        ((π (θ g)).comp γ.symm.toLinearIsometry.toContinuousLinearMap)
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        change γ (π (θ 1) (γ.symm x)) = x
        rw [map_one, map_one]
        exact γ.apply_symm_apply x
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro x
        change γ (π (θ (g * h)) (γ.symm x)) =
          γ (π (θ g) (γ.symm (γ (π (θ h) (γ.symm x)))))
        rw [γ.symm_apply_apply, map_mul, map_mul]
        rfl }
  have hσ (g : G) (x y : E) : inner ℂ (σ g x) (σ g y) = inner ℂ x y := by
    change inner ℂ (γ (π (θ g) (γ.symm x))) (γ (π (θ g) (γ.symm y))) = _
    rw [hγ, hπ, ← hγ, γ.apply_symm_apply, γ.apply_symm_apply]
  let A : V →ₗ[ℂ] E := γ.toLinearEquiv.toLinearMap.comp (S₀.comp J.toLinearMap)
  have hA : A ≠ 0 := by
    intro he
    apply h₀
    apply LinearMap.ext
    intro f
    obtain ⟨f', rfl⟩ := J.surjective f
    apply γ.injective
    change A f' = γ 0
    simp [he]
  have hcompare (S : V →ₗ[ℂ] E) (hS : S ≠ 0) (hL : ∀ g f, S (L g f) = π g (S f))
      (hsym : ∀ f g, inner ℂ (S f) (S₀ g) = inner ℂ (S (J g)) (S₀ (J f))) :
      ∃ T : E →L[ℂ] E, (∀ f, T (S f) = A f) ∧ (∀ g x, T (π g x) = σ g (T x)) := by
    refine exists_unitaryIntertwiner_of_regularization_pairing π σ hπ hσ hirr S A hS
      (fun g f => ⟨L g f, hL g f, ?_⟩) S₀ (fun f => γ (S (J f))) ?_ ?_
    · change γ (S₀ (J (L g f))) = γ (π (θ g) (γ.symm (γ (S₀ (J f)))))
      rw [γ.symm_apply_apply, hJ, hL₀]
    · have hD := denseRange_of_nonzero_intertwining π hirr L S hS hL
      have hDJ : DenseRange ((S : V → E) ∘ (J : V → V)) := by
        change Dense (Set.range ((S : V → E) ∘ (J : V → V)))
        rw [Set.range_comp, J.surjective.range_eq, Set.image_univ]
        exact hD
      exact γ.surjective.denseRange.comp hDJ γ.continuous
    · intro f g
      change inner ℂ (γ (S₀ (J f))) (γ (S (J g))) = _
      rw [hγ, ← hsym]
  obtain ⟨T₀, hT₀, hT₀L⟩ := hcompare S₀ h₀ hL₀ hsym₀
  obtain ⟨T₁, hT₁, hT₁L⟩ := hcompare S₁ h₁ hL₁ hsym₁
  have hT₁_ne : T₁ ≠ 0 := by
    intro he
    apply hA
    exact LinearMap.ext fun f => (hT₁ f).symm.trans (by rw [he]; rfl)
  have hcomm (T : E →L[ℂ] E) (hT : ∀ g x, T (π g x) = σ g (T x)) (g : G) :
      Commute (T₁.adjoint.comp T) (π g) := by
    apply ContinuousLinearMap.ext
    intro x
    change T₁.adjoint (T (π g x)) = π g (T₁.adjoint (T x))
    rw [hT, adjoint_intertwines π σ hπ hσ T₁ hT₁L]
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_unitary_commute π hπ hirr _ (hcomm T₀ hT₀L)
  obtain ⟨d, hd⟩ := exists_eq_scalar_of_unitary_commute π hπ hirr _ (hcomm T₁ hT₁L)
  have hd_ne : d ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hd
    exact hT₁_ne (ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hd)
  refine ⟨d⁻¹ * c, LinearMap.ext fun f => ?_⟩
  have heq : d • S₁ f = c • S₀ f := calc
    d • S₁ f = T₁.adjoint (T₁ (S₁ f)) :=
      (congrArg (fun T : E →L[ℂ] E => T (S₁ f)) hd).symm
    _ = T₁.adjoint (T₀ (S₀ f)) := by rw [hT₁, hT₀]
    _ = c • S₀ f := congrArg (fun T : E →L[ℂ] E => T (S₀ f)) hc
  have h := congrArg (fun v : E => d⁻¹ • v) heq
  simpa only [smul_smul, inv_mul_cancel₀ hd_ne, one_smul, LinearMap.smul_apply] using h

end Langlands.Archimedean
