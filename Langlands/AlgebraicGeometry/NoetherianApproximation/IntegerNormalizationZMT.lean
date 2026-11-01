import Langlands.AlgebraicGeometry.NoetherianApproximation.ClosedFiberPolynomialCharts
import Langlands.AlgebraicGeometry.NoetherianApproximation.FiniteFieldNormalization

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- At a maximal ideal, a characteristic-zero integer domain has a finite
normalization chart given by a module-finite polynomial subalgebra. -/
theorem exists_finite_normalization_zmt_chart
    (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (q : Ideal A) [q.IsMaximal] :
    ∃ n : ℕ, ∃ f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] A,
      Function.Injective f ∧
        letI := f.toRingHom.toAlgebra
        ∃ C : Subalgebra (MvPolynomial (Fin n) ℤ) A, ∃ r : C,
          r.val ∉ q ∧
          Function.Bijective (Localization.awayMap C.val.toRingHom r) ∧
          Module.Finite C (integralClosure C (FractionRing C)) := by
  obtain ⟨n, f, hfi, hq⟩ :=
    exists_injective_quasiFiniteAt_mvPolynomial_integer A q
  have hP : Algebra.FiniteType ℤ (MvPolynomial (Fin n) ℤ) := inferInstance
  refine ⟨n, f, hfi, ?_⟩
  let := f.toRingHom.toAlgebra
  have : IsScalarTower ℤ (MvPolynomial (Fin n) ℤ) A :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (f.commutes z).symm
  have : Algebra.FiniteType (MvPolynomial (Fin n) ℤ) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  have : FaithfulSMul (MvPolynomial (Fin n) ℤ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hfi
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin n) ℤ) q := hq
  obtain ⟨C, hC, r, hr, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := MvPolynomial (Fin n) ℤ) q
  have : Module.Finite (MvPolynomial (Fin n) ℤ) C :=
    ⟨(Submodule.fg_top _).mpr hC⟩
  have : FaithfulSMul (MvPolynomial (Fin n) ℤ) C :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h ↦
      hfi (congrArg (fun z : C ↦ z.val) h)
  exact ⟨C, r, hr, hbij,
    @finite_normalization_of_normal_finite_subbase (MvPolynomial (Fin n) ℤ) C
      _ _ _ _ hP _ _ _ _ _⟩

end Langlands.AlgebraicGeometry.NoetherianApproximation
