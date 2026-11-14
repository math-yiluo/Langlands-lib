/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 570, 14 November 2026: extract source M346.001,
adapt its namespace and imports, and prove the fully applied published target.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer.MonogeneityStatements

/-! # Integral elements in an Eisenstein power-basis algebra -/

namespace Langlands.NYLL.PortInternal.M346

theorem d001
    {R K' L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K'] [Field L]
    [Algebra R K'] [Algebra K' L] [Algebra R L]
    [IsScalarTower R K' L] [IsFractionRing R K']
    [FiniteDimensional K' L] [Algebra.IsSeparable K' L]
    (B : PowerBasis K' L) (pi : R) (hpi : Irreducible pi)
    (hBint : IsIntegral R B.gen)
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Ideal.span ({pi} : Set R)))
    {z : L} (hzint : IsIntegral R z) :
    d001Statement (R := R) (K' := K') (L := L)
      B pi hpi hBint hei (z := z) hzint := by
  change z ∈ Algebra.adjoin R ({B.gen} : Set L)
  have hdiscInt :
      IsIntegral R (Algebra.discr K' B.basis) :=
    Algebra.discr_isIntegral K' (fun i => by
      simpa using hBint.pow (i : ℕ))
  obtain ⟨d, hd⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hdiscInt
  have hd0 : d ≠ 0 := by
    intro hd0
    have hdisc0 : Algebra.discr K' B.basis ≠ 0 :=
      Algebra.discr_not_zero_of_basis K' B.basis
    apply hdisc0
    rw [← hd, hd0, map_zero]
  obtain ⟨m, unit, hdu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hpi
  have H :=
    Algebra.discr_mul_isIntegral_mem_adjoin K' hBint hzint
  rw [← hd, hdu, map_mul, map_pow] at H
  have Hpow :
      pi ^ m • z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
    have HR :
        ((↑unit : R) * pi ^ m) • z ∈
          Algebra.adjoin R ({B.gen} : Set L) := by
      rw [← IsScalarTower.algebraMap_smul K']
      simpa [map_mul, map_pow] using H
    have Hu :=
      Subalgebra.smul_mem
        (Algebra.adjoin R ({B.gen} : Set L)) HR (↑(unit⁻¹) : R)
    simpa [smul_smul, ← mul_assoc] using Hu
  exact mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hpi)
    hBint hzint Hpow hei

end Langlands.NYLL.PortInternal.M346
