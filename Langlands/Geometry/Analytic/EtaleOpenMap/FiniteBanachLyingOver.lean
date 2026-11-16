import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRadiusRealization
import Langlands.Geometry.Analytic.Spectrum.ResidueField
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Lying over for finite Banach maps over arbitrary valued fields -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- Norm-controlled finite coefficients bound every ring homomorphism whose
restriction to the coefficient algebra is contractive. -/
theorem IsFiniteBanach.exists_norm_bound {f : BoundedAlgHom K A B}
    (hf : f.IsFiniteBanach) {C : Type z} [NormedCommRing C]
    (ψ : B →+* C) (hψ : ∀ a, ‖ψ (f a)‖ ≤ ‖a‖) :
    ∃ M > (0 : ℝ), ∀ b, ‖ψ b‖ ≤ M * ‖b‖ := by
  obtain ⟨n, d, L, hL, hd⟩ := hf
  let D : ℝ := ∑ j : Fin n, ‖ψ (d j)‖
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨L * (D + 1), mul_pos hL (by positivity), fun b => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hd b
  calc
    ‖ψ b‖ = ‖∑ j : Fin n, ψ (f (c j)) * ψ (d j)‖ := by
      rw [← hc, coefficientMap_apply, map_sum]
      simp only [map_mul]
    _ ≤ ∑ j : Fin n, ‖ψ (f (c j)) * ψ (d j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, ‖c‖ * ‖ψ (d j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ((hψ _).trans (norm_le_pi_norm c j)) (norm_nonneg _))
    _ = ‖c‖ * D := (Finset.mul_sum _ _ _).symm
    _ ≤ (L * ‖b‖) * D := mul_le_mul_of_nonneg_right hcn hD
    _ ≤ (L * ‖b‖) * (D + 1) := by gcongr; linarith
    _ = (L * (D + 1)) * ‖b‖ := by ring

end BoundedAlgHom

namespace BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- Lying over for a finite Banach map, including trivial valuations. -/
theorem exists_comap_eq_of_isFiniteBanach (i : BoundedAlgHom K A B)
    (hfin : i.IsFiniteBanach) (x : BanachSpectrum A)
    (hx : RingHom.ker i.toAlgHom.toRingHom ≤ x.kernel) :
    ∃ y : BanachSpectrum B, comap i.toBoundedRingHom y = x := by
  classical
  let : Algebra A B := i.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite A B := hfin.finite
  have : x.kernel.IsPrime := kernel_isPrime x
  obtain ⟨q, -, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.kernel
    (⊥ : Ideal B) (fun a ha => hx (by
      change i a = 0
      exact (Submodule.mem_bot B).mp ha))
  -- Realize one radius to get a nontrivial complete extension of the residue field.
  let H := CompletedResidueField K x
  obtain ⟨E⟩ := FiniteRadiusRealization.nonempty (K := H) (fun _ : Unit => (2 : ℝ))
    (by intro _; norm_num)
  let : NontriviallyNormedField E.L :=
    { (inferInstance : NormedField E.L) with
      non_trivial := ⟨E.c (), by rw [E.norm_c]; norm_num⟩ }
  let Ω := AlgebraicClosure E.L
  let : NormedField Ω := spectralNorm.normedField E.L Ω
  let : NormedAlgebra E.L Ω := spectralNorm.normedAlgebra E.L Ω
  let ρ : A →+* Ω := ((algebraMap E.L Ω).comp E.ι).comp
    (completedResidueMap K x).toAlgHom.toRingHom
  have hρ (a : A) : ‖ρ a‖ = x a := by
    change ‖algebraMap E.L Ω (E.ι (completedResidueMap K x a))‖ = x a
    rw [norm_algebraMap', E.norm_ι, norm_completedResidueMap]
  let p := q.comap (algebraMap A B)
  have hpx : p = x.kernel := hqp
  have hρp (a : A) : ρ a = 0 ↔ a ∈ p := by
    rw [hpx, ← norm_eq_zero, hρ]
    rfl
  let R := A ⧸ p
  let ρ' : R →+* Ω := Ideal.Quotient.lift p ρ fun a ha => (hρp a).mpr ha
  let : Algebra R Ω := ρ'.toAlgebra
  have : IsDomain (B ⧸ q) := Ideal.Quotient.isDomain q
  have : IsDomain R := Ideal.Quotient.isDomain p
  have : Module.IsTorsionFree R (B ⧸ q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  have : Module.IsTorsionFree R Ω := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    refine (injective_iff_map_eq_zero ρ').mpr fun r hr => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hρp a).mp hr)
  have : Algebra.IsAlgebraic R (B ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φ : (B ⧸ q) →ₐ[R] Ω := IsAlgClosed.lift
  let ψ : B →+* Ω := φ.toRingHom.comp (Ideal.Quotient.mk q)
  have hψ (a : A) : ψ (algebraMap A B a) = ρ a := by
    change φ (Ideal.Quotient.mk q (algebraMap A B a)) = ρ a
    exact φ.commutes (Ideal.Quotient.mk p a)
  obtain ⟨M, hM, hbound⟩ := hfin.exists_norm_bound ψ (fun a => by
    change ‖ψ (algebraMap A B a)‖ ≤ ‖a‖
    rw [hψ, hρ]
    exact x.le_norm a)
  let ψb : BoundedRingHom B Ω := { ψ with bounded := ⟨M, hM, hbound⟩ }
  refine ⟨comap ψb (fieldPoint Ω), ext fun a => ?_⟩
  change ‖ψ (i a)‖ = x a
  exact (congrArg norm (hψ a)).trans (hρ a)

end BanachSpectrum

end Langlands.Analytic
