import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerPolynomialChartStatement
import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerNormalizationCharts
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Linarith

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  let : P.IsPrime := hP
  by_cases h : P = ⊥
  · subst P
    apply le_antisymm ?_ bot_le
    intro z hz
    have hu := Int.isUnit_iff.mp (Ideal.mem_jacobson_bot.mp hz z)
    change z = 0
    rcases hu with hu | hu <;> nlinarith [sq_nonneg z]
  · let : P.IsMaximal := IsPrime.to_maximal_ideal h
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_injective_quasiFiniteAt_mvPolynomial_integer
    (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (q : Ideal A) [q.IsMaximal] :
    ∃ n : ℕ, ∃ f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] A,
      Function.Injective f ∧
        letI := f.toRingHom.toAlgebra
        Algebra.QuasiFiniteAt (MvPolynomial (Fin n) ℤ) q := by
  classical
  let := Ideal.Quotient.field q
  let := isJacobsonRing_int
  have : Module.Finite ℤ (A ⧸ q) :=
    finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ q)
  let m : Ideal ℤ := q.under ℤ
  have hm : m.IsMaximal := by
    have heq : m = RingHom.ker (algebraMap ℤ (A ⧸ q)) := by
      ext z
      change algebraMap ℤ A z ∈ q ↔ Ideal.Quotient.mk q (algebraMap ℤ A z) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.symm
    rw [heq]
    exact Algebra.ker_algebraMap_isMaximal_of_isIntegral ℤ (A ⧸ q)
  let := Ideal.Quotient.field m
  let r : ℤ := Submodule.IsPrincipal.generator m
  have hmr : Ideal.span {r} = m := Ideal.span_singleton_generator m
  have hr : ¬ IsUnit r := by
    intro h
    exact hm.ne_top (hmr.symm.trans (Ideal.span_singleton_eq_top.mpr h))
  have hr0 : r ≠ 0 := by
    intro h
    exact Ring.ne_bot_of_isMaximal_of_not_isField hm Int.not_isField
      (hmr.symm.trans (by simp [h]))
  let J : Ideal A := m.map (algebraMap ℤ A)
  have hJq : J ≤ q := Ideal.map_le_iff_le_comap.mpr le_rfl
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top ‹q.IsMaximal›) hJq)
  let : Algebra (ℤ ⧸ m) (A ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  have : IsScalarTower ℤ (ℤ ⧸ m) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType (ℤ ⧸ m) (A ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ℤ ⧸ m) (A ⧸ J)
  obtain ⟨n, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg (ℤ ⧸ m) (A ⧸ J)
  choose x hx using fun i : Fin n ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] A := MvPolynomial.aeval x
  let π : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) (ℤ ⧸ m) :=
    MvPolynomial.map (Ideal.Quotient.mk m)
  have hcomm : (Ideal.Quotient.mk J).comp f.toRingHom = g.toRingHom.comp π := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [f, π]
    · intro i
      simpa [f, π] using hx i
  have hfi : Function.Injective f := by
    apply injective_of_ker_le_span_singleton f.toRingHom (MvPolynomial.C r)
    · intro h
      exact hr (by simpa using h.map MvPolynomial.constantCoeff)
    · simpa [f] using (Int.cast_ne_zero.mpr hr0 : (r : A) ≠ 0)
    · intro P hP
      apply Ideal.mem_span_singleton.mpr
      apply (MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk m) r
        (fun z ↦ by rw [Ideal.Quotient.eq_zero_iff_mem, ← hmr, Ideal.mem_span_singleton]) P).mpr
      apply hg
      change g (π P) = g 0
      rw [map_zero, ← show Ideal.Quotient.mk J (f P) = g (π P) from
        congrArg (fun h : MvPolynomial (Fin n) ℤ →+* A ⧸ J ↦ h P) hcomm]
      simpa using congrArg (Ideal.Quotient.mk J) hP
  refine ⟨n, f, hfi, ?_⟩
  let := f.toRingHom.toAlgebra
  have : IsScalarTower ℤ (MvPolynomial (Fin n) ℤ) A :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (f.commutes z).symm
  have : Algebra.FiniteType (MvPolynomial (Fin n) ℤ) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  have hfinite : ((Ideal.Quotient.mk J).comp f.toRingHom).Finite := by
    rw [hcomm]
    have hπ : π.Finite := RingHom.Finite.of_surjective π
      (MvPolynomial.map_surjective _ (Ideal.Quotient.mk_surjective (I := m)))
    exact RingHom.Finite.comp (g := g.toRingHom) (f := π) hgf hπ
  have : Module.Finite (MvPolynomial (Fin n) ℤ) (A ⧸ J) := by
    apply RingHom.finite_algebraMap.mp
    exact hfinite
  apply quasiFiniteAt_of_finite_quotient q J
  dsimp only [J]
  rw [← hmr, Ideal.map_span, Set.image_singleton]
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  have hCr : MvPolynomial.C r ∈ q.under (MvPolynomial (Fin n) ℤ) := by
    change f (MvPolynomial.C r) ∈ q
    simpa [f] using (show algebraMap ℤ A r ∈ q from
      Submodule.IsPrincipal.generator_mem m)
  simpa [f] using Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) ℤ) A) hCr

theorem integerPolynomialChart : IntegerPolynomialChartStatement :=
  exists_injective_quasiFiniteAt_mvPolynomial_integer

end Langlands.AlgebraicGeometry.NoetherianApproximation
