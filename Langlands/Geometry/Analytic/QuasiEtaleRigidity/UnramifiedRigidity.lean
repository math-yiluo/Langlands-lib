import Langlands.Geometry.Analytic.QuasiEtaleRigidity.DiagonalAnnihilator
import Langlands.Geometry.Analytic.AffinoidIdempotents

/-! # Spectrally close maps out of an unramified algebra are equal -/

noncomputable section

universe u v w

namespace Langlands.Analytic.QuasiEtaleRigidity

open TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Points of the spectrum are subadditive on finite sums. -/
theorem spectrum_sum_le {A : Type v} [NormedCommRing A] (x : BanachSpectrum A) {ι : Type*}
    (s : Finset ι) (g : ι → A) : x (∑ i ∈ s, g i) ≤ ∑ i ∈ s, x (g i) :=
  Finset.le_sum_of_subadditive (fun a => x a) (map_zero x.toMulRingSeminorm).le
    (map_add_le_add x.toMulRingSeminorm) s g

omit [CompleteSpace K] in
/-- A point of the spectrum of the target, pulled back along a bounded map, is bounded by the
norm of the source. -/
theorem spectrum_apply_le_norm {S : Type v} [NormedCommRing S] [Algebra K S]
    {C : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K S C) (x : BanachSpectrum C) (a : S) :
    x (φ a) ≤ ‖a‖ :=
  (BanachSpectrum.comap φ.toBoundedRingHom x).le_norm a

/-- **Rigidity of unramified maps (algebraic core of Berkovich's Key Lemma 7.2).** Let
`f : R → S` be a bounded map of finite type and let `e ∈ S` kill `Ω[S⁄R]`. There are a finite
set `G ⊆ S`, an exponent `n` and a constant `M` such that two bounded maps `φ₁ φ₂ : S → C` to a
presented affinoid algebra which agree on `R` are equal as soon as, at every point `x` of the
spectrum of `C`, `M · ∑_{g ∈ G} |φ₁ g - φ₂ g|(x) < |φ₁ e|(x)ⁿ`. -/
theorem exists_unramified_rigidity_bound {R : Type v} {S : Type w} [NormedCommRing R]
    [Algebra K R] [NormedCommRing S] [Algebra K S] (f : BoundedAlgHom K R S)
    (hf : f.toAlgHom.toRingHom.FiniteType) (e : S)
    (he : letI : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
      e ∈ Module.annihilator S Ω[S⁄R]) :
    ∃ (G : Finset S) (n : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ (C : PresentedAffinoidAlgebra K)
      (φ₁ φ₂ : BoundedAlgHom K S C), (∀ r, φ₁ (f r) = φ₂ (f r)) →
      (∀ x : BanachSpectrum C, M * ∑ g ∈ G, x (φ₁ g - φ₂ g) < x (φ₁ e) ^ n) → φ₁ = φ₂ := by
  classical
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FiniteType R S := hf
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := R) (A := S)
  obtain ⟨n, c, hc⟩ := exists_diagonal_annihilator G hG he
  choose P hP using fun g => TensorProduct.exists_finset (R := R) (c g)
  let Mg : G → ℝ := fun g => ∑ p ∈ P g, ‖p.1‖ * ‖p.2‖
  have hMg0 : ∀ g, 0 ≤ Mg g := fun g =>
    Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨G, n, ∑ g, Mg g, Finset.sum_nonneg fun g _ => hMg0 g,
    fun C φ₁ φ₂ hR hlt => ?_⟩
  have hR' : φ₁.toAlgHom.toRingHom.comp (algebraMap R S) =
      φ₂.toAlgHom.toRingHom.comp (algebraMap R S) := RingHom.ext fun r => hR r
  obtain ⟨Ψ, hΨ⟩ := exists_tensorProduct_lift φ₁.toAlgHom.toRingHom φ₂.toAlgHom.toRingHom hR'
  suffices hunit : IsUnit (φ₁ e ^ n + ∑ g, Ψ (c g) * (φ₂ (g : S) - φ₁ (g : S))) by
    have key := eq_of_isUnit_image G hG hc φ₁.toAlgHom.toRingHom φ₂.toAlgHom.toRingHom hR' Ψ
      hΨ hunit
    exact BoundedAlgHom.ext fun a => RingHom.congr_fun key a
  rw [PresentedAffinoidAlgebra.isUnit_iff_forall_ne_zero]
  intro x
  have hMg : ∀ g, x (Ψ (c g)) ≤ Mg g := by
    intro g
    rw [hP g, map_sum]
    refine (spectrum_sum_le x _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    change x.toMulRingSeminorm (Ψ (p.1 ⊗ₜ[R] p.2)) ≤ ‖p.1‖ * ‖p.2‖
    rw [hΨ, map_mul]
    exact mul_le_mul (spectrum_apply_le_norm φ₁ x p.1) (spectrum_apply_le_norm φ₂ x p.2)
      (apply_nonneg _ _) (norm_nonneg _)
  set T := ∑ g : G, Ψ (c g) * (φ₂ (g : S) - φ₁ (g : S))
  have hsum : x T ≤ (∑ g, Mg g) * ∑ g ∈ G, x (φ₁ g - φ₂ g) := by
    refine (spectrum_sum_le x _ _).trans ?_
    rw [← Finset.sum_coe_sort G (fun g => x (φ₁ g - φ₂ g)), Finset.mul_sum]
    refine Finset.sum_le_sum fun g _ => ?_
    change x.toMulRingSeminorm (Ψ (c g) * (φ₂ (g : S) - φ₁ (g : S))) ≤ _
    rw [map_mul, ← map_neg_eq_map x.toMulRingSeminorm (φ₂ (g : S) - φ₁ (g : S)), neg_sub]
    have h1 : Mg g ≤ ∑ g, Mg g :=
      Finset.single_le_sum (fun g _ => hMg0 g) (Finset.mem_univ g)
    exact mul_le_mul ((hMg g).trans h1) le_rfl (apply_nonneg _ _)
      (Finset.sum_nonneg fun g _ => hMg0 g)
  have hpow : x (φ₁ e ^ n) = x (φ₁ e) ^ n := map_pow x.toMulRingSeminorm _ _
  have htri : x (φ₁ e ^ n) ≤ x (φ₁ e ^ n + T) + x T := by
    have := map_add_le_add x.toMulRingSeminorm (φ₁ e ^ n + T) (-T)
    rwa [add_neg_cancel_right, map_neg_eq_map] at this
  intro h0
  have := hlt x
  change x.toMulRingSeminorm (φ₁ e ^ n + T) = 0 at h0
  change x.toMulRingSeminorm (φ₁ e ^ n) ≤ x.toMulRingSeminorm (φ₁ e ^ n + T) +
    x.toMulRingSeminorm T at htri
  change x.toMulRingSeminorm (φ₁ e ^ n) = _ at hpow
  linarith

end Langlands.Analytic.QuasiEtaleRigidity
