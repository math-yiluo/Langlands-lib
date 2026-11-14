import Langlands.Geometry.Building.KPApartmentCoefficientChart
import Langlands.Geometry.Building.KPBuilding

/-! # Coefficient charts that fix an apartment point -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData.CoefficientChart

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom] {ω : kˣ → ℝ} {D : KPApartmentData i ω}
  {θ : MulAut (rationalPoints G)} {s : kˣ → kˣ} (A : D.CoefficientChart θ s)

attribute [local instance] RootTranslationMetric.normedAddCommGroup in
/-- Two apartment points whose values agree at a point with finite value of every relative
root coincide. -/
theorem apartment_eq_of_val_eq [Fintype (relativeRoots i)] {x y : D.Apartment}
    (h : ∀ α : relativeRoots i, ∃ u, x.val α u ≠ ⊤ ∧ y.val α u = x.val α u) : y = x := by
  have hzero : ∀ α : relativeRoots i, rootForm i α (y -ᵥ x) = 0 := by
    intro α
    obtain ⟨u, hne, hu⟩ := h α
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
    have h1 := val_eq_val_add_rootForm y x α u
    rw [hu, ← hr, ← WithTop.coe_add, WithTop.coe_inj] at h1
    linarith
  have hn : ‖(y -ᵥ x : TranslationSpace i)‖ = ‖(0 : TranslationSpace i)‖ :=
    RootTranslationMetric.norm_eq_of_rootForm_equiv i i (Equiv.refl _) _ _ fun α => by
      rw [Equiv.refl_apply, hzero, map_zero]
  rw [norm_zero, norm_eq_zero] at hn
  exact vsub_eq_zero_iff_eq.mp hn

section InfiniteField

variable [Infinite k] (hG : IsConnectedReductive G) (hi : IsSplitSubtorus i)
include hG hi

/-- If `θ` maps the torus points onto the torus points, the correcting element of a chart is
a normalizer point. -/
theorem c_mem_normalizerPoints
    (hθ : ∀ t, ∃ t', θ (rationalPoints.map i t) = rationalPoints.map i t')
    (hθ' : ∀ t, ∃ t', rationalPoints.map i t = θ (rationalPoints.map i t')) :
    A.c ∈ normalizerPoints i := by
  apply mem_normalizerPoints_of_conj hG i hi
  · intro t
    obtain ⟨t₁, ht₁⟩ := hθ (A.τ t)
    refine ⟨t₁, ?_⟩
    rw [← ht₁, ← A.torus t]
    group
  · intro t
    obtain ⟨t₀, ht₀⟩ := hθ' t
    refine ⟨A.τ.symm t₀, ?_⟩
    rw [ht₀, ← A.torus (A.τ.symm t₀), Equiv.apply_symm_apply]

/-- **Fixed apartment points of a chart.** If `θ` acts on the torus points compatibly with
`s` on character values, and every relative root has a `θ`-fixed root-group point at which
`x` is finite, then the corrected chart fixes `x`. -/
theorem smul_a_eq [Fintype (relativeRoots i)]
    (hθ : ∀ t, ∃ t', θ (rationalPoints.map i t) = rationalPoints.map i t' ∧
      ∀ χ, s (torusCharacterValue χ t') = torusCharacterValue χ t)
    (hθ' : ∀ t, ∃ t', rationalPoints.map i t = θ (rationalPoints.map i t'))
    (x : D.Apartment)
    (hroot : ∀ α : relativeRoots i, ∃ u, x.val α u ≠ ⊤ ∧ θ u = u) :
    (⟨A.c, A.c_mem_normalizerPoints hG hi (fun t => (hθ t).imp fun _ h => h.1) hθ'⟩ :
      normalizerPoints i) • A.a x = x := by
  set n : normalizerPoints i :=
    ⟨A.c, A.c_mem_normalizerPoints hG hi (fun t => (hθ t).imp fun _ h => h.1) hθ'⟩ with hn
  -- the relabelling corrected by the Weyl action of `n⁻¹` is the identity
  have hβ : ∀ b, A.β (weylAction i n⁻¹ b) = b := by
    intro b
    apply torusCharacterValue_injective hi.1
    intro t
    obtain ⟨t₀, rfl⟩ := A.τ.surjective t
    obtain ⟨t₁, ht₁, hχ⟩ := hθ (A.τ t₀)
    have hconj : rationalPoints.map i t₁ =
        ((n⁻¹ : normalizerPoints i) : rationalPoints G)⁻¹ * rationalPoints.map i t₀ *
          ((n⁻¹ : normalizerPoints i) : rationalPoints G) := by
      rw [Subgroup.coe_inv, inv_inv, ← ht₁, ← A.torus t₀]
      simp only [hn]
      group
    rw [A.char, weylAction_torusCharacterValue i _ b hconj, hχ]
  apply apartment_eq_of_val_eq
  intro α
  obtain ⟨u, hne, hu⟩ := hroot α
  refine ⟨u, hne, ?_⟩
  rw [val_smul, RootFunctionFamily.smul_apply]
  have hu' : ((n : rationalPoints G))⁻¹ * u * (n : rationalPoints G) =
      A.c⁻¹ * θ u * A.c := by
    rw [hu]
  rw [hu', A.a_val, hβ]

/-- The fixed-point statement on the reduced building: the correcting element carries the image
of `a x` back to the image of `x`. -/
theorem c_smul_apartment_a_eq [Fintype (relativeRoots i)]
    (hθ : ∀ t, ∃ t', θ (rationalPoints.map i t) = rationalPoints.map i t' ∧
      ∀ χ, s (torusCharacterValue χ t') = torusCharacterValue χ t)
    (hθ' : ∀ t, ∃ t', rationalPoints.map i t = θ (rationalPoints.map i t'))
    (x : D.Apartment)
    (hroot : ∀ α : relativeRoots i, ∃ u, x.val α u ≠ ⊤ ∧ θ u = u) :
    A.c • ApartmentQuotient.apartment D.sharpFixerFamily (A.a x) =
      ApartmentQuotient.apartment D.sharpFixerFamily x :=
  (ApartmentQuotient.apartment_smul D.sharpFixerFamily
    ⟨A.c, A.c_mem_normalizerPoints hG hi (fun t => (hθ t).imp fun _ h => h.1) hθ'⟩
    (A.a x)).symm.trans
    (congrArg (ApartmentQuotient.apartment D.sharpFixerFamily)
      (A.smul_a_eq hG hi hθ hθ' x hroot))

end InfiniteField

end Langlands.Geometry.Building.KPApartmentData.CoefficientChart
