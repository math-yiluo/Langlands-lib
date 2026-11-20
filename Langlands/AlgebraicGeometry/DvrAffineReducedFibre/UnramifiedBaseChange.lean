import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Base change at a weakly unramified vertical local ring -/

open IsLocalRing TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Residue

variable (R S B : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [CommRing B] [IsLocalRing B] [Algebra R B]

local notation "T" => S ⊗[R] B

/-- If the extension of local base rings preserves the residue field, and the
base maximal ideal generates that of `B`, the residue tensor of the base change
is the residue field of `B`. -/
def residueTensorBaseChangeEquiv
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    (hB : (maximalIdeal R).map (algebraMap R B) = maximalIdeal B) :
    ResidueField S ⊗[S] T ≃+* ResidueField B := by
  let f : ResidueField R ≃ₐ[R] ResidueField S :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField S))
      ⟨(algebraMap (ResidueField R) (ResidueField S)).injective, hres⟩
  let e₁ := Algebra.TensorProduct.cancelBaseChange R S (ResidueField S) (ResidueField S) B
  let e₂ := Algebra.TensorProduct.congr f.symm (AlgEquiv.refl : B ≃ₐ[R] B)
  let e₃ := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal R)).symm
  exact e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
    (e₃.toRingEquiv.trans (Ideal.quotEquivOfEq hB)))

end Residue

private theorem isDomain_of_regular_principal_maximalIdeal (T : Type*) [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] {t : T} (ht : t ∈ nonZeroDivisors T)
    (hm : maximalIdeal T = Ideal.span {t}) : IsDomain T := by
  have hregular := mem_nonZeroDivisors_iff_left.mp ht
  have : NoZeroDivisors T := by
    constructor
    intro a b hab
    by_cases hb : b = 0
    · exact Or.inr hb
    left
    have hpow : ∀ n : ℕ, ∀ c : T, c * b = 0 → c ∈ maximalIdeal T ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro c hc
        have hnu : ¬ IsUnit c := fun h => hb (h.mul_right_eq_zero.mp hc)
        have hcm : c ∈ Ideal.span {t} := hm ▸ (mem_maximalIdeal c).mpr hnu
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hcm
        have hdb : d * b = 0 := hregular (d * b) (by rw [← mul_assoc, ← hd, hc])
        have htm : t ∈ maximalIdeal T := hm.symm ▸ Ideal.mem_span_singleton_self t
        rw [hd, pow_succ']
        exact Ideal.mul_mem_mul htm (ih d hdb)
    exact IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal T) T) a (by
      intro n
      simpa [SModEq.zero, Ideal.smul_top_eq_map] using hpow n a hab)
  exact NoZeroDivisors.to_isDomain T

section DVR

variable (R S B : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra R B] [Module.Flat R B]

local notation "T" => S ⊗[R] B

/-- A finite DVR extension with the same residue field preserves a weakly
unramified Noetherian local algebra. Its tensor product is a DVR in which the
new base maximal ideal generates the maximal ideal. -/
theorem tensorProduct_dvr_of_residueEquiv (hinj : Function.Injective (algebraMap R S))
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    (hB : (maximalIdeal R).map (algebraMap R B) = maximalIdeal B) :
    ∃ (_ : IsDomain T) (_ : IsDiscreteValuationRing T),
      (maximalIdeal S).map (algebraMap S T) = maximalIdeal T := by
  let J := (maximalIdeal S).map (algebraMap S T)
  let e : (T ⧸ J) ≃+* ResidueField B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal S)).toRingEquiv.trans
      (residueTensorBaseChangeEquiv R S B hres hB)
  have hJ : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ (e.isField (Field.toIsField _))
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R B T := Algebra.TensorProduct.right_isScalarTower
  have : Module.Finite B T := Module.Finite.equiv (Algebra.TensorProduct.commRight R B S).toLinearEquiv
  have : IsNoetherianRing T := IsNoetherianRing.of_finite B T
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hJspan : J = Ideal.span {algebraMap S T s} := by
    rw [show J = (maximalIdeal S).map (algebraMap S T) from rfl, hs.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  have hRS : algebraMap R S r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr.ne_zero
  obtain ⟨n, u, hmul⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hRS hs
  have hlocal : IsLocalRing T := IsLocalRing.of_unique_max_ideal ⟨J, hJ, fun p hp => by
    have hpB : (p.under B).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal p
    have hrp : algebraMap R T r ∈ p := by
      rw [IsScalarTower.algebraMap_apply R B T]
      change algebraMap R B r ∈ p.under B
      rw [eq_maximalIdeal hpB, ← hB]
      exact Ideal.mem_map_of_mem _ (hr.maximalIdeal_eq.symm ▸ Ideal.mem_span_singleton_self r)
    have hsp : algebraMap S T s ∈ p := by
      rw [IsScalarTower.algebraMap_apply R S T, hmul, map_mul, map_pow,
        Ideal.unit_mul_mem_iff_mem p (u.isUnit.map (algebraMap S T))] at hrp
      exact hp.isPrime.mem_of_pow_mem n hrp
    symm
    apply hJ.eq_of_le hp.ne_top
    rwa [hJspan, Ideal.span_singleton_le_iff_mem]⟩
  have hJT : J = maximalIdeal T := eq_maximalIdeal hJ
  have hprincipal : maximalIdeal T = Ideal.span {algebraMap S T s} := hJT.symm.trans hJspan
  have : Module.Flat S T := inferInstance
  have hreg : algebraMap S T s ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := T)
      (mem_nonZeroDivisors_of_ne_zero hs.ne_zero)
    exact h (show s • x = s • (0 : T) by rw [Algebra.smul_def, hx, smul_zero])
  have : IsDomain T := isDomain_of_regular_principal_maximalIdeal T hreg hprincipal
  have hnf : ¬ IsField T := by
    rw [isField_iff_maximalIdeal_eq, hprincipal, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hreg
  have hP : (maximalIdeal T).IsPrincipal := hprincipal.symm ▸ inferInstance
  exact ⟨inferInstance, ((IsDiscreteValuationRing.TFAE T hnf).out 5 1).mp hP, hJT⟩

end DVR

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
