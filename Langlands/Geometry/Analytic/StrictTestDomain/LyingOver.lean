import Langlands.Geometry.Analytic.FiniteBanachAlgebra
import Langlands.Geometry.Analytic.Spectrum.ResidueField
import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Lying over for finite bounded maps of Banach algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.BanachSpectrum

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]

/-- The completed residue field of a point is nontrivially normed: it contains `K`
isometrically. -/
@[reducible] def completedResidueNontriviallyNormedField (x : BanachSpectrum A) :
    NontriviallyNormedField (CompletedResidueField K x) :=
  { (inferInstance : NormedField (CompletedResidueField K x)) with
    non_trivial := by
      obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
      exact ⟨algebraMap K (CompletedResidueField K x) c, by rwa [norm_algebraMap']⟩ }

/-- Lying over for a finite bounded map of Banach algebras: every point killing the
kernel of the map is the restriction of a point of the target. The point is the norm
of an algebraic closure of the completed residue field, pulled back along a map
extending the residue map; the finite Banach-algebra theorem makes it bounded. -/
theorem exists_comap_eq_of_finite [CompleteSpace K] (i : BoundedAlgHom K A B)
    (hfin : i.toAlgHom.toRingHom.Finite) (x : BanachSpectrum A)
    (hx : RingHom.ker i.toAlgHom.toRingHom ≤ x.kernel) :
    ∃ y : BanachSpectrum B, comap i.toBoundedRingHom y = x := by
  classical
  let : Algebra A B := i.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  have : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq fun c => (i.toAlgHom.commutes c).symm
  have hAB : Continuous (algebraMap A B) := i.continuous
  have : x.kernel.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime x.kernel).mp
      (inferInstanceAs (IsDomain (ResidueDomain x)))
  obtain ⟨q, -, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.kernel
    (⊥ : Ideal B) (fun a ha => hx (by
      change i a = 0
      exact (Submodule.mem_bot B).mp ha))
  -- The residue field, its algebraic closure, and their norms.
  let H := CompletedResidueField K x
  let : NontriviallyNormedField H := completedResidueNontriviallyNormedField x
  let Ω := AlgebraicClosure H
  let : NormedField Ω := spectralNorm.normedField H Ω
  let : NormedAlgebra H Ω := spectralNorm.normedAlgebra H Ω
  let : NormedAlgebra K Ω :=
    { (inferInstance : Algebra K Ω) with
      norm_smul_le := fun c z => by
        rw [Algebra.smul_def, norm_mul, IsScalarTower.algebraMap_apply K H Ω,
          norm_algebraMap', norm_algebraMap'] }
  -- The residue map, the quotient of `A` under `q`, and the algebra structures.
  let ρ : A →+* Ω := (algebraMap H Ω).comp (completedResidueMap K x).toAlgHom.toRingHom
  have hρ (a : A) : ‖ρ a‖ = x a := by
    change ‖algebraMap H Ω (completedResidueMap K x a)‖ = x a
    rw [norm_algebraMap', norm_completedResidueMap]
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
    have h := φ.commutes (Ideal.Quotient.mk p a)
    exact h
  let : Algebra A Ω := ρ.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap K Ω c = algebraMap H Ω (completedResidueMap K x (algebraMap K A c))
    rw [(completedResidueMap K x).toAlgHom.commutes c, ← IsScalarTower.algebraMap_apply]
  let ψA : B →ₐ[A] Ω := { ψ with commutes' := hψ }
  have hAΩ : Continuous (algebraMap A Ω) :=
    AddMonoidHomClass.continuous_of_bound (algebraMap A Ω) 1 fun a => by
      rw [one_mul]
      change ‖ρ a‖ ≤ ‖a‖
      rw [hρ]
      exact x.le_norm a
  obtain ⟨M, hM0, hM⟩ := FiniteBanachAlgebra.exists_norm_bound (K := K) ψA hAB hAΩ
  let ψb : BoundedRingHom B Ω :=
    { toRingHom := ψ
      bounded := ⟨M + 1, by linarith, fun b =>
        (hM b).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg b))⟩ }
  refine ⟨comap ψb (fieldPoint Ω), ext fun a => ?_⟩
  change ‖ψ (i a)‖ = x a
  exact (congrArg norm (hψ a)).trans (hρ a)

end Langlands.Analytic.BanachSpectrum
