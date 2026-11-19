import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerNormalizationCharts
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Polynomial charts near the closed fibre of a DVR -/

open IsLocalRing
open Langlands.AlgebraicGeometry.NoetherianApproximation

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- An injective polynomial chart in which the specified prime is quasi-finite. -/
def ClosedFibrePolynomialChart (q : Ideal A) [q.IsPrime] : Type u :=
  Σ n : ℕ, {f : MvPolynomial (Fin n) R →ₐ[R] A // Function.Injective f ∧
    letI := f.toRingHom.toAlgebra
    Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) q}

variable [IsDomain R] [IsDiscreteValuationRing R] [IsDomain A]
  [Algebra.FiniteType R A]

/-- Lift a Noether normalization of the special fibre to a polynomial chart
that is injective and quasi-finite at the chosen special-fibre prime. -/
theorem nonempty_closedFibrePolynomialChart (hRA : Function.Injective (algebraMap R A))
    {π : R} (hπ : Irreducible π) (q : Ideal A) [q.IsPrime]
    (hq : algebraMap R A π ∈ q) : Nonempty (ClosedFibrePolynomialChart R A q) := by
  classical
  let m := maximalIdeal R
  let J := m.map (algebraMap R A)
  have hJ : J = Ideal.span {algebraMap R A π} := by
    rw [show J = (maximalIdeal R).map (algebraMap R A) from rfl,
      hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hJq : J ≤ q := hJ ▸ (q.span_singleton_le_iff_mem.mpr hq)
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top ‹q.IsPrime›) hJq)
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Algebra (R ⧸ m) (A ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  have : IsScalarTower R (R ⧸ m) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType (R ⧸ m) (A ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ m) (A ⧸ J)
  obtain ⟨n, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg (R ⧸ m) (A ⧸ J)
  choose x hx using fun i : Fin n ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let f : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval x
  let e : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) (R ⧸ m) :=
    MvPolynomial.map (Ideal.Quotient.mk m)
  have hcomm : (Ideal.Quotient.mk J).comp f.toRingHom = g.toRingHom.comp e := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, e]
      exact IsScalarTower.algebraMap_apply R (R ⧸ m) (A ⧸ J) r
    · intro i
      simpa [f, e] using hx i
  have hfi : Function.Injective f := by
    apply injective_of_ker_le_span_singleton f.toRingHom (MvPolynomial.C π)
    · intro h
      exact hπ.not_isUnit (by simpa using h.map MvPolynomial.constantCoeff)
    · simpa [f] using (map_ne_zero_iff (algebraMap R A) hRA).mpr hπ.ne_zero
    · intro P hP
      apply Ideal.mem_span_singleton.mpr
      apply (MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk m) π
        (fun r ↦ by rw [Ideal.Quotient.eq_zero_iff_mem,
          show m = Ideal.span {π} from hπ.maximalIdeal_eq, Ideal.mem_span_singleton]) P).mpr
      apply hg
      change g (e P) = g 0
      rw [map_zero, ← show Ideal.Quotient.mk J (f P) = g (e P) from
        congrArg (fun h : MvPolynomial (Fin n) R →+* A ⧸ J ↦ h P) hcomm]
      simpa using congrArg (Ideal.Quotient.mk J) hP
  refine ⟨⟨n, f, hfi, ?_⟩⟩
  let : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : Algebra.FiniteType (MvPolynomial (Fin n) R) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have hfinite : ((Ideal.Quotient.mk J).comp f.toRingHom).Finite := by
    rw [hcomm]
    have he : e.Finite := RingHom.Finite.of_surjective e
      (MvPolynomial.map_surjective _ (Ideal.Quotient.mk_surjective (I := m)))
    exact RingHom.Finite.comp (g := g.toRingHom) (f := e) hgf he
  have : Module.Finite (MvPolynomial (Fin n) R) (A ⧸ J) := by
    apply RingHom.finite_algebraMap.mp
    exact hfinite
  apply quasiFiniteAt_of_finite_quotient q J
  rw [hJ, Ideal.span_singleton_le_iff_mem]
  have hC : MvPolynomial.C π ∈ q.under (MvPolynomial (Fin n) R) := by
    change f (MvPolynomial.C π) ∈ q
    simpa [f] using hq
  have hπmap : algebraMap (MvPolynomial (Fin n) R) A (MvPolynomial.C π) = algebraMap R A π := by
    change f (MvPolynomial.C π) = _
    simp [f]
  rw [← hπmap]
  exact Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) A) hC

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
