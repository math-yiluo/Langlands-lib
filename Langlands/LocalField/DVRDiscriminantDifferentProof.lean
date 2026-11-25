import Langlands.LocalField.DVRDiscriminantDifferentStatement
import Langlands.LocalFactor.Ramification.Monogenic
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# The discriminant of an extension of DVRs is the norm of its different: proof

A finite extension of DVRs `A → B` with separable residue extension is monogenic: `B = A[x]`
(`Ramification.exists_adjoin_singleton_eq_top_of_isSeparable_residueField`). For the power basis
`1, x, …, x^{n-1}`, the discriminant is `± N_{B/A}(f'(x))` with `f` the minimal polynomial of `x`
(Mathlib's formula over the fraction fields, `Algebra.discr_powerBasis_eq_norm`, brought down by
localization), and the different is `(f'(x))` (Mathlib's `conductor_mul_differentIdeal`, the
conductor of a generator being `B`). So the discriminant ideal is the norm of the different. Any
other basis differs by an invertible matrix, whose determinant is a unit. If the different is
`m_B ^ d`, its norm is `m_A ^ (f d)` (Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`).
-/

namespace Langlands.LocalField

universe uA uB uK uL uι

namespace DiscriminantDifferent

open Polynomial IsLocalRing
open scoped nonZeroDivisors Matrix

section ChangeOfBasis

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The discriminant ideal does not depend on the basis. -/
theorem span_discr_eq_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e b : Module.Basis ι A B) :
    Ideal.span {Algebra.discr A b} = Ideal.span {Algebra.discr A e} := by
  have hb : (b : ι → B) = (e : ι → B) ᵥ* (e.toMatrix b).map (algebraMap A B) := by
    funext j
    rw [← e.sum_toMatrix_smul_self b j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def, mul_comm]
  rw [hb, Algebra.discr_of_matrix_vecMul, ← Module.Basis.det_apply]
  exact Ideal.span_singleton_mul_left_unit ((e.isUnit_det b).pow 2) _

end ChangeOfBasis

section PowerBasis

variable {A B K L : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
  [IsIntegrallyClosed A]

variable (K L) in
/-- The power basis of `L` over `K` induced by a power basis of `B` over `A`. -/
noncomputable def localizedPowerBasis (pb : PowerBasis A B) : PowerBasis K L :=
  haveI := IsIntegralClosure.isLocalization A K L B
  { gen := algebraMap B L pb.gen
    dim := pb.dim
    basis := pb.basis.localizationLocalization K A⁰ L
    basis_eq_pow := fun i => by
      simp [Module.Basis.localizationLocalization_apply, pb.basis_eq_pow, map_pow] }

omit [IsFractionRing B L] in
variable (K L) in
/-- **The discriminant of a power basis over the ring** is `± N(f'(x))`. -/
theorem discr_powerBasis_eq_norm_of_isFractionRing (pb : PowerBasis A B) :
    Algebra.discr A pb.basis =
      (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
        Algebra.norm A (aeval pb.gen (derivative (minpoly A pb.gen))) := by
  have := IsIntegralClosure.isLocalization A K L B
  have : Module.Free A B := Module.Free.of_basis pb.basis
  have : Module.Finite A B := Module.Finite.of_basis pb.basis
  apply IsFractionRing.injective A K
  rw [← Algebra.discr_localizationLocalization A A⁰ L pb.basis]
  change Algebra.discr K (localizedPowerBasis K L pb).basis = _
  rw [Algebra.discr_powerBasis_eq_norm]
  have hgen : (localizedPowerBasis K L pb).gen = algebraMap B L pb.gen := rfl
  rw [hgen, minpoly.isIntegrallyClosed_eq_field_fractions K L pb.isIntegral_gen, derivative_map,
    aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.norm_localization A A⁰]
  simp [map_mul, map_pow, map_neg, map_one]

end PowerBasis

section Main

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field K] [Field L] [Algebra A B] [IsLocalHom (algebraMap A B)]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
  [Module.Finite A B]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [Module.IsTorsionFree A B] [Module.Free A B]

omit [IsLocalHom (algebraMap A B)] [IsFractionRing B L] [Module.Finite A B]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [Module.Free A B] in
variable (K L) in
/-- The different of a monogenic extension `B = A[x]` is `(f'(x))`. -/
theorem differentIdeal_eq_span_aeval (x : B) (hx : Algebra.adjoin A {x} = ⊤)
    (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have h := conductor_mul_differentIdeal A K L x hxL
  rwa [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul] at h

omit [IsFractionRing B L] in
variable (K L) in
include K L in
/-- **The discriminant ideal is the norm of the different.** -/
theorem span_discr_eq_spanNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) :
    Ideal.span {Algebra.discr A b} = Ideal.spanNorm A (differentIdeal A B) := by
  have hinj : Function.Injective (algebraMap A B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  obtain ⟨x, hx⟩ :=
    Ramification.exists_adjoin_singleton_eq_top_of_isSeparable_residueField (A := A) (B := B) hinj
  have hint : IsIntegral A x := Algebra.IsIntegral.isIntegral x
  let pb := PowerBasis.ofAdjoinEqTop' hint hx
  have hgen : pb.gen = x := PowerBasis.ofAdjoinEqTop'_gen hint hx
  let e : Module.Basis ι A B := pb.basis.reindex (b.indexEquiv pb.basis).symm
  rw [span_discr_eq_of_basis e b]
  have hde : Algebra.discr A e = Algebra.discr A pb.basis := by
    rw [Module.Basis.coe_reindex]
    exact Algebra.discr_reindex A pb.basis _
  rw [hde, discr_powerBasis_eq_norm_of_isFractionRing K L pb,
    Ideal.span_singleton_mul_left_unit ((isUnit_neg_one (α := A)).pow _),
    ← Algebra.intNorm_eq_norm, ← Ideal.spanNorm_singleton, hgen]
  congr 1
  have hxL : Algebra.adjoin K {algebraMap B L x} = ⊤ := by
    have := (localizedPowerBasis K L pb).adjoin_gen_eq_top
    rwa [show (localizedPowerBasis K L pb).gen = algebraMap B L x from by
      rw [← hgen]; rfl] at this
  exact (differentIdeal_eq_span_aeval K L x hx hxL).symm

omit [IsDiscreteValuationRing A] [IsLocalHom (algebraMap A B)] [FiniteDimensional K L]
  [IsIntegralClosure B A L] [Module.Finite A B]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [Module.IsTorsionFree A B] in
variable (K L) in
include K L in
/-- The fraction rings inherit separability. -/
theorem isSeparable_fractionRing : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

variable (K L) in
include K L in
/-- **The valuation of the discriminant**: if the different is `m_B ^ d`, the discriminant ideal
is `m_A ^ (f d)`. -/
theorem span_discr_eq_maximalIdeal_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) (d : ℕ) (hd : differentIdeal A B = maximalIdeal B ^ d) :
    Ideal.span {Algebra.discr A b} = maximalIdeal A ^ ((maximalIdeal B).inertiaDeg A * d) := by
  have := isSeparable_fractionRing (A := A) (B := B) K L
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  rw [span_discr_eq_spanNorm K L b, hd, Ideal.spanNorm_eq, map_pow,
    Ideal.relNorm_eq_pow_of_isMaximal (maximalIdeal B) (maximalIdeal A), ← pow_mul]

end Main

end DiscriminantDifferent

open DiscriminantDifferent in
/-- **The discriminant of an extension of DVRs is the norm of its different.** -/
theorem dvrDiscriminantDifferent : DVRDiscriminantDifferent.{uA, uB, uK, uL, uι} := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι _ _ b
  have := isTorsionFree_of_isFractionRing_tower A B K L
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  exact ⟨span_discr_eq_spanNorm K L b, span_discr_eq_maximalIdeal_pow K L b⟩

end Langlands.LocalField
