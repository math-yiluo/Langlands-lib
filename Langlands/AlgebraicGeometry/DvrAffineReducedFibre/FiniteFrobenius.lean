import Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.Perfect

/-! # Frobenius on a complete DVR with perfect residue field -/

open IsLocalRing

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Frobenius

variable (R : Type u) [CommRing R] (p : ℕ) [ExpChar R p]

/-- The algebra structure on a copy of `R` with scalar map given by Frobenius. -/
@[instance_reducible]
def frobeniusAlgebra : Algebra R (ULift.{0} R) :=
  ((ULift.ringEquiv : ULift.{0} R ≃+* R).symm.toRingHom.comp (frobenius R p)).toAlgebra

/-- Form the Frobenius-linear combination of the powers of `π` below exponent `p`. -/
def frobeniusUniformizerExpansionMap (π : R) :
    let alg := frobeniusAlgebra R p
    let : Module R (ULift.{0} R) := alg.toModule
    (Fin p → R) →ₗ[R] ULift.{0} R := by
  let alg := frobeniusAlgebra R p
  let : Module R (ULift.{0} R) := alg.toModule
  let : SMul R (ULift.{0} R) := alg.toSMul
  exact (Pi.basisFun R (Fin p)).constr R (fun i => ULift.up (π ^ i.val))

end Frobenius

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectField (ResidueField R)]

private theorem exists_uniformizer_expansion_mod_pow {π : R} (hπ : Irreducible π)
    (n : ℕ) (r : R) :
    ∃ (c : Fin n → R) (b : R), r = (∑ i, c i ^ p * π ^ i.val) + π ^ n * b := by
  have hchar : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by rw [← map_natCast (residue R), CharP.cast_eq_zero R p, map_zero])
  induction n generalizing r with
  | zero =>
    exact ⟨Fin.elim0, r, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := surjective_frobenius (ResidueField R) p (residue R r)
    obtain ⟨d, hd⟩ := residue_surjective z
    have hmem : r - d ^ p ∈ Ideal.span {π} := by
      rw [← hπ.maximalIdeal_eq, ← residue_eq_zero_iff, map_sub, map_pow, hd, sub_eq_zero]
      exact hz.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨c, b, hc⟩ := ih t
    refine ⟨Fin.cons d c, b, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one, Fin.cons_succ, Fin.val_succ,
      pow_succ, ← mul_assoc, ← Finset.sum_mul]
    linear_combination -ht + π * hc

variable (R)

/-- Frobenius is module-finite on a complete DVR of positive characteristic with
perfect residue field. The powers of a uniformizer below exponent `p` generate
the target under the Frobenius scalar action. -/
theorem finite_frobenius_of_isAdicComplete [IsAdicComplete (maximalIdeal R) R] :
    (frobenius R p).Finite := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let T := ULift.{0} R
  let e : T ≃+* R := ULift.ringEquiv
  let alg : Algebra R T := frobeniusAlgebra R p
  let : Algebra R T := alg
  let : Module R T := alg.toModule
  let : SMul R T := alg.toSMul
  have hg (x : R) : algebraMap R T x = ULift.up (x ^ p) := rfl
  let I := maximalIdeal R
  have hm : I.map (algebraMap R T) = Ideal.span {(ULift.up (π ^ p) : T)} := by
    rw [show I = maximalIdeal R from rfl, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      hg]
  have hproper : I.map (algebraMap R T) ≠ ⊤ := by
    intro h
    have hu : IsUnit (ULift.up (π ^ p) : T) := Ideal.span_singleton_eq_top.mp (hm ▸ h)
    exact hπ.not_isUnit <| (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
      (show IsUnit (π ^ p) from hu.map e.toRingHom)
  have : IsDomain T := e.toMulEquiv.isDomain
  have : IsNoetherianRing T := isNoetherianRing_of_ringEquiv R e.symm
  have : IsScalarTower R T T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsHausdorff I T :=
    (IsHausdorff.map_algebraMap_iff (R := R) (S := T)).mp (IsHausdorff.of_isDomain _ hproper)
  have : IsAdicComplete I (Fin p → R) := IsAdicComplete.of_finite_of_isNoetherianRing _ _
  let L : (Fin p → R) →ₗ[R] T := frobeniusUniformizerExpansionMap R p π
  have hL (c : Fin p → R) : e (L c) = ∑ i, c i ^ p * π ^ i.val := by
    simp only [L, frobeniusUniformizerExpansionMap, Module.Basis.constr_apply_fintype,
      Pi.basisFun_equivFun, LinearEquiv.refl_apply, map_sum]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have hsurj : Function.Surjective L := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨c, b, hc⟩ := exists_uniformizer_expansion_mod_pow p hπ p (e y)
    refine ⟨c, ?_⟩
    change Submodule.Quotient.mk (L c) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, Ideal.smul_top_eq_map (S := T) I, hm]
    exact Ideal.mem_span_singleton'.mpr ⟨ULift.up (-b), e.injective (by
      rw [map_sub, hL, map_mul]
      change -b * π ^ p = _
      linear_combination hc)⟩
  have hfinite : Module.Finite R T := Module.Finite.of_surjective L hsurj
  have hf : (algebraMap R T).Finite := RingHom.finite_algebraMap.mpr hfinite
  have hcomp : e.toRingHom.comp (algebraMap R T) = frobenius R p := by
    ext x
    rfl
  rw [← hcomp]
  exact (RingHom.Finite.of_surjective _ e.surjective).comp hf

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
