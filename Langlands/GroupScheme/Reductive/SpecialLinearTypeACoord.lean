import Langlands.GroupScheme.Reductive.SpecialLinearCoroots
import Langlands.LinearAlgebra.RootPairingTypeACoord

/-! # Type `A` weight coordinates for the diagonal torus of `SL_{n+1}`

Any root datum of the diagonal torus of `SL_{n+1}` carries the type `A_n` weight
coordinates `ε p = w(p)`, the characters reading off the `p`-th diagonal entry.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RootPairingTypeA

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : ℕ} {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

variable (n k) in
/-- The character `w(p)` of the diagonal torus: the `p`-th diagonal entry. -/
def weightChar (p : Fin (n + 1)) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv (Fin n) k).symm (weightCoord n p)

theorem rootChar_eq_weightChar_sub (p q : Fin (n + 1)) :
    rootChar n k p q = weightChar n k p - weightChar n k q := by
  rw [rootChar, weightChar, weightChar, map_sub]

theorem characterCoordEquiv_sum_smul_weightChar (c : Fin (n + 1) → ℤ) (a : Fin n) :
    GeneralLinear.characterCoordEquiv (Fin n) k (∑ y, c y • weightChar n k y) a =
      c a.castSucc - c (Fin.last n) := by
  simp only [map_sum, map_zsmul, weightChar, LinearEquiv.apply_symm_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, weightCoord_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem latticePairing_weightChar_cochar (x : Fin (n + 1)) {h : Fin (n + 1) → ℤ}
    (hh : ∑ z, h z = 0) :
    latticePairing 𝔻 (weightChar n k x) (cochar n k h) = h x := by
  rw [GeneralLinear.latticePairing_coord, weightChar, LinearEquiv.apply_symm_apply,
    cocharacterCoordEquiv_cochar]
  exact sum_weightCoord_mul_of_sum_eq_zero hh x

/-- **Type `A` coordinates.** Every root datum of the diagonal torus of `SL_{n+1}` carries the
type `A_n` weight coordinates `w(0), …, w(n)`. -/
def typeACoord {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) :
    TypeACoord P n where
  ε := weightChar n k
  exists_eq_sum x := by
    refine ⟨Fin.lastCases 0 (fun a => GeneralLinear.characterCoordEquiv (Fin n) k x a), ?_⟩
    apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
    funext a
    rw [characterCoordEquiv_sum_smul_weightChar, Fin.lastCases_castSucc, Fin.lastCases_last,
      sub_zero]
  sum_eq_zero := by
    rw [show ∑ y, weightChar n k y =
        (GeneralLinear.characterCoordEquiv (Fin n) k).symm (∑ y, weightCoord n y) from
        (map_sum _ _ _).symm, sum_weightCoord_eq_zero, map_zero]
  eq_of_sum_eq_zero c hc := by
    have hlast : ∀ y, c y = c (Fin.last n) := by
      intro y
      induction y using Fin.lastCases with
      | last => rfl
      | cast a =>
        have := characterCoordEquiv_sum_smul_weightChar (k := k) c a
        rw [hc, map_zero, Pi.zero_apply] at this
        omega
    intro y z
    rw [hlast y, hlast z]
  exists_root_eq j := by
    obtain ⟨p, q, hpq, h⟩ := (mem_range_root_iff hP (P.root j)).mp ⟨j, rfl⟩
    exact ⟨p, q, hpq, h.trans (rootChar_eq_weightChar_sub p q)⟩
  exists_eq_root a b hab := by
    obtain ⟨j, hj⟩ := (mem_range_root_iff hP (rootChar n k a b)).mpr ⟨a, b, hab, rfl⟩
    exact ⟨j, hj.trans (rootChar_eq_weightChar_sub a b)⟩
  coroot'_apply j a b h y := by
    have hj : P.root j = rootChar n k a b := h.trans (rootChar_eq_weightChar_sub a b).symm
    change P.toLinearMap (weightChar n k y) (P.coroot j) = _
    rw [hP.1, coroot_eq_corootChar hP hj, corootChar,
      latticePairing_weightChar_cochar y (sum_delta a b)]
    rfl

@[simp] theorem typeACoord_ε {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) (p : Fin (n + 1)) :
    (typeACoord hP).ε p = weightChar n k p :=
  rfl

end Langlands.GroupScheme.SpecialLinear.FinSucc
