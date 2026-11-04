import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one

/-! # Dimension of a finite-type domain over a field -/

universe u v w

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen

/-- The natural dimension computed from the transcendence degree of the actual algebra. -/
noncomputable def finiteTypeDomainDimension (k : Type u) (A : Type v)
    [Field k] [CommRing A] [IsDomain A] [Algebra k A] : ℕ :=
  (Algebra.trdeg k A).toNat

/-- Noether normalization compares the transcendence-degree construction
with the actual Krull dimension. -/
theorem ringKrullDim_eq_finiteTypeDomainDimension
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = (finiteTypeDomainDimension k A : WithBot ℕ∞) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have : Module.Finite P A := (RingHom.finite_algebraMap).mp hfin
  have ht := lift_trdeg_add_eq k P A
  rw [trdeg_eq_zero (R := P) (A := A), Cardinal.lift_zero, add_zero,
    MvPolynomial.trdeg_of_isDomain] at ht
  have hn : n = finiteTypeDomainDimension k A := by
    simpa [finiteTypeDomainDimension] using congrArg Cardinal.toNat ht
  rw [← hn]
  exact (ringKrullDim_eq_of_ringHom_isIntegral_of_injective
    g.toRingHom hfin.to_isIntegral hinj).symm.trans (ringKrullDim_mvPolynomial_fin k n)

/-- An injective algebraic map between finite-type domains preserves dimension. -/
theorem ringKrullDim_eq_of_finiteType_of_isAlgebraic
    (k : Type u) (A : Type v) (B : Type w) [Field k]
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [FaithfulSMul A B] [Algebra.IsAlgebraic A B] :
    ringKrullDim A = ringKrullDim B := by
  rw [ringKrullDim_eq_finiteTypeDomainDimension k A,
    ringKrullDim_eq_finiteTypeDomainDimension k B]
  have ht := lift_trdeg_add_eq k A B
  rw [trdeg_eq_zero (R := A) (A := B), Cardinal.lift_zero, add_zero] at ht
  have hn : finiteTypeDomainDimension k A = finiteTypeDomainDimension k B := by
    simpa [finiteTypeDomainDimension] using congrArg Cardinal.toNat ht
  rw [hn]

/-- Every nonempty principal chart of a finite-type domain has its original dimension. -/
theorem ringKrullDim_away_eq_of_finiteType_domain
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (s : A) (hs : s ≠ 0) :
    ringKrullDim (Localization.Away s) = ringKrullDim A := by
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  have : FaithfulSMul A (Localization.Away s) :=
    (faithfulSMul_iff_algebraMap_injective A (Localization.Away s)).mpr
      (IsLocalization.injective (Localization.Away s)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hs))
  have : Algebra.IsAlgebraic A (Localization.Away s) :=
    IsLocalization.isAlgebraic (Localization.Away s) (Submonoid.powers s)
  exact (ringKrullDim_eq_of_finiteType_of_isAlgebraic k A (Localization.Away s)).symm

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
