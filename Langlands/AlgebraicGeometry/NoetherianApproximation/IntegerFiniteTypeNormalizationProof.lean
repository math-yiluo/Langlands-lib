import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationStatement
import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerNormalizationZMT
import Langlands.AlgebraicGeometry.NoetherianApproximation.NormalizationLocalization

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- The finite-field branch reduces the unconditional target to characteristic zero. -/
theorem integerFiniteTypeNormalization_of_charZero
    (hzero : ∀ (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
      [Algebra.FiniteType ℤ A],
      Module.Finite A (integralClosure A (FractionRing A))) :
    IntegerFiniteTypeNormalizationStatement.{u} := by
  intro A _ _ _
  rcases CharP.exists' A with hzeroA | ⟨p, hp, hchar⟩
  · let := hzeroA
    exact hzero A
  · let := hp
    let := hchar
    exact finite_normalization_of_prime_characteristic A p

/-- Finite normalization in characteristic zero, patched from Zariski charts. -/
theorem finite_normalization_of_charZero
    (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  apply finite_of_finite_localizations_near_maximal
  intro q hq
  let := hq
  obtain ⟨n, f, hfi, hchart⟩ := exists_finite_normalization_zmt_chart A q
  let := f.toRingHom.toAlgebra
  obtain ⟨C, r, hr, hbij, hfiniteC⟩ := hchart
  let := hfiniteC
  exact ⟨r.val, hr, finite_normalization_localized_of_finite_subalgebra C r
    (fun hz ↦ hr (hz ▸ q.zero_mem)) hbij⟩

/-- A finite type integer domain has module-finite normalization in its fraction field. -/
theorem integerFiniteTypeNormalization : IntegerFiniteTypeNormalizationStatement.{u} :=
  integerFiniteTypeNormalization_of_charZero finite_normalization_of_charZero

end Langlands.AlgebraicGeometry.NoetherianApproximation
