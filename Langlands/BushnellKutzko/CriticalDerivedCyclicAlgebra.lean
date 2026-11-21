import Mathlib.RingTheory.AdjoinRoot

/-! # The commutative algebra for the cyclic lift -/

noncomputable section

open Polynomial

namespace Langlands.BushnellKutzko.CriticalDerived

universe u

variable {F : Type u} [Field F]

/-- An algebra with the two root relations and a rectangular power basis. -/
structure CyclicAlgebra (Q : Polynomial F) (h f : ℕ) (π : Fˣ) (a : ℤ) where
  A : Type u
  [ring : CommRing A]
  [alg : Algebra F A]
  U : Aˣ
  T : Aˣ
  eval_zero : aeval (U : A) Q = 0
  carry : T ^ h = Units.map (algebraMap F A).toMonoidHom π * U ^ a
  basis : Module.Basis (Fin h × Fin f) F A
  basis_apply : ∀ j : Fin h × Fin f, basis j = (T : A) ^ (j.1 : ℕ) * (U : A) ^ (j.2 : ℕ)

attribute [instance] CyclicAlgebra.ring CyclicAlgebra.alg

private theorem isUnit_root_of_isUnit_coeff_zero {R : Type*} [CommRing R] {Q : Polynomial R}
    (hQ : IsUnit (Q.coeff 0)) : IsUnit (AdjoinRoot.root Q) := by
  let x := AdjoinRoot.root Q
  have h : aeval x (X * Q.divX + C (Q.coeff 0)) = 0 := by
    rw [X_mul_divX_add, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [map_add, map_mul, aeval_X, aeval_C] at h
  exact isUnit_of_mul_isUnit_left ((add_eq_zero_iff_eq_neg.mp h).symm ▸
    (hQ.map (algebraMap R (AdjoinRoot Q))).neg)

set_option maxHeartbeats 450000 in
/-- First adjoin a root of `Q`, then an `h`th root of `π U^a`. Both roots are units;
monic power bases give the stated basis in the resulting commutative algebra. -/
theorem exists_cyclicAlgebra (Q : Polynomial F) (hQ : Q.Monic) (hQ₀ : IsUnit (Q.coeff 0))
    (π : Fˣ) (a : ℤ) {h f : ℕ} (hh : 0 < h) (hf : Q.natDegree = f) (hf₀ : 0 < f) :
    Nonempty (CyclicAlgebra Q h f π a) := by
  let A := AdjoinRoot Q
  let : Nontrivial A := (AdjoinRoot.nontrivial_iff_of_monic hQ).mpr
    (natDegree_pos_iff_degree_pos.mp (hf ▸ hf₀ : 0 < Q.natDegree))
  obtain ⟨U, hU⟩ := isUnit_root_of_isUnit_coeff_zero hQ₀
  let c : Aˣ := Units.map (algebraMap F A).toMonoidHom π * U ^ a
  let H : Polynomial A := X ^ h - C (c : A)
  let J := AdjoinRoot H
  have hH : H.Monic := monic_X_pow_sub_C _ hh.ne'
  have hdeg : H.natDegree = h := natDegree_X_pow_sub_C
  have hcarry : (AdjoinRoot.root H) ^ h = algebraMap A J (c : A) := by
    have hz : aeval (AdjoinRoot.root H) H = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    exact sub_eq_zero.mp (by simpa only [H, map_sub, map_pow, aeval_C, aeval_X] using hz)
  have hunit : IsUnit (AdjoinRoot.root H) :=
    (isUnit_pow_iff hh.ne').mp (hcarry.symm ▸ c.isUnit.map (algebraMap A J))
  obtain ⟨T, hT⟩ := hunit
  let U' : Jˣ := Units.map (algebraMap A J).toMonoidHom U
  let bU := (AdjoinRoot.powerBasis' hQ).basis.reindex (finCongr hf)
  let bT := (AdjoinRoot.powerBasis' hH).basis.reindex (finCongr hdeg)
  let b := (bU.smulTower bT).reindex (Equiv.prodComm (Fin f) (Fin h))
  refine ⟨{ A := J, U := U', T := T, eval_zero := ?_, carry := ?_, basis := b, basis_apply := ?_ }⟩
  · change aeval ((IsScalarTower.toAlgHom F A J) (U : A)) Q = 0
    rw [aeval_algHom_apply, hU, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · apply Units.ext
    change (T : J) ^ h = algebraMap F J (π : F) * ↑(U' ^ a)
    rw [hT, hcarry, IsScalarTower.algebraMap_apply F A J]
    change algebraMap A J ((algebraMap F A (π : F)) * ↑(U ^ a)) = _
    rw [map_mul]
    apply congrArg (fun x : J => algebraMap A J (algebraMap F A (π : F)) * x)
    exact congrArg (fun x : Jˣ => (x : J)) (map_zpow (Units.map (algebraMap A J).toMonoidHom) U a)
  · rintro ⟨m, l⟩
    change b (m, l) = (T : J) ^ (m : ℕ) * (U' : J) ^ (l : ℕ)
    rw [show b (m, l) = (bU.smulTower bT) (l, m) by
      simp only [b, Module.Basis.reindex_apply]; rfl, Module.Basis.smulTower_apply]
    simp only [bU, bT, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, Algebra.smul_def]
    change algebraMap A J (AdjoinRoot.root Q ^ (l : ℕ)) * AdjoinRoot.root H ^ (m : ℕ) = _
    rw [← hU, ← hT, map_pow, mul_comm]
    rfl

end Langlands.BushnellKutzko.CriticalDerived
