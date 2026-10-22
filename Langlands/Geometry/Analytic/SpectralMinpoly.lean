import Langlands.Geometry.Analytic.GaussAlgebraicClosure
import Langlands.Geometry.Analytic.TateIntegralClosure
import Langlands.Geometry.Analytic.FiniteBanachAlgebra
import Langlands.Geometry.Analytic.PowerBounds
import Mathlib.FieldTheory.Extension

/-! # Spectral control of the actual minimal polynomial in the domain case -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Polynomial

/-- The coefficients of a split monic polynomial whose roots are in
the norm unit ball are themselves in that ball, with all root
multiplicities retained. -/
theorem coeff_norm_le_one_of_roots {C : Type*} [NormedField C]
    [IsUltrametricDist C] (p : Polynomial C) (hp : p.Monic)
    (hs : p.Splits) (hr : ∀ y ∈ p.roots, ‖y‖ ≤ 1) :
    ∀ i, ‖p.coeff i‖ ≤ 1 := by
  let S := normUnitBallSubring C
  have hmem : p ∈ Polynomial.lifts S.subtype :=
    hs.mem_lift_of_roots_mem_range hp S.subtype fun y hy =>
      ⟨⟨y, hr y hy⟩, rfl⟩
  intro i
  obtain ⟨a, ha⟩ := (Polynomial.lifts_iff_coeff_lifts p).mp hmem i
  rw [← ha]
  exact a.property

namespace StrictTateAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] (n : ℕ)
  {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [IsDomain B] [Algebra (StrictTateAlgebra (Fin n) K) B]
  [IsScalarTower K (StrictTateAlgebra (Fin n) K) B]
  [Module.Finite (StrictTateAlgebra (Fin n) K) B]
  [Module.IsTorsionFree (StrictTateAlgebra (Fin n) K) B]

/-- Spectral values at most one force coefficient norms at most one
for the actual minimal polynomial over the finite injective Tate base.
The ambient normed algebraic closure and every test point are constructed. -/
theorem minpoly_coeff_norm_le_one
    (hAB : Continuous (algebraMap (StrictTateAlgebra (Fin n) K) B))
    (b : B) (hb : ∀ x : BanachSpectrum B, x b ≤ 1) :
    ∀ i, ‖(minpoly (StrictTateAlgebra (Fin n) K) b).coeff i‖ ≤ 1 := by
  classical
  let T := StrictTateAlgebra (Fin n) K
  let F := FractionRing T
  let L := FractionRing B
  let C := GaussAlgebraicClosure K n
  let _ : Algebra F L := FractionRing.liftAlgebra T L
  let p := minpoly T b
  have hp : p.Monic := minpoly.monic (IsIntegral.of_finite T b)
  have hpC : (p.map (algebraMap T C)).Monic := hp.map _
  have hroots : ∀ y ∈ (p.map (algebraMap T C)).roots, ‖y‖ ≤ 1 := by
    intro y hy
    have hyT : Polynomial.aeval y p = 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using
        (Polynomial.mem_roots hpC.ne_zero).mp hy
    have hyF : Polynomial.aeval y (minpoly F (algebraMap B L b)) = 0 := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F L (IsIntegral.of_finite T b),
        Polynomial.aeval_map_algebraMap]
      exact hyT
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (F := F) (E := L) (K := C)
      (fun z => ⟨IsIntegral.of_finite F z, IsAlgClosed.splits _⟩) hyF
    let ψ : B →ₐ[T] C :=
      (φ.restrictScalars T).comp (IsScalarTower.toAlgHom T B L)
    have hAC : Continuous (algebraMap T C) :=
      AddMonoidHomClass.continuous_of_bound (algebraMap T C) 1 fun a => by
        simpa only [one_mul] using (norm_gaussClosure_algebraMap K n a).le
    obtain ⟨M, hM, hbound⟩ :=
      FiniteBanachAlgebra.exists_norm_bound (K := K) ψ hAB hAC
    let ψb : BoundedRingHom B C :=
      { toRingHom := ψ.toRingHom
        bounded := ⟨M + 1, by linarith, fun a =>
          (hbound a).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a))⟩ }
    have h := hb (BanachSpectrum.comap ψb (BanachSpectrum.fieldPoint C))
    change ‖ψ b‖ ≤ 1 at h
    change ‖φ (algebraMap B L b)‖ ≤ 1 at h
    rwa [hφ] at h
  have hc := coeff_norm_le_one_of_roots (p.map (algebraMap T C)) hpC
    (IsAlgClosed.splits _) hroots
  intro i
  have := hc i
  rw [Polynomial.coeff_map] at this
  change ‖algebraMap (StrictTateAlgebra (Fin n) K)
    (GaussAlgebraicClosure K n) ((minpoly (StrictTateAlgebra (Fin n) K) b).coeff i)‖ ≤ 1
    at this
  rwa [norm_gaussClosure_algebraMap] at this

end StrictTateAlgebra

end Langlands.Analytic
