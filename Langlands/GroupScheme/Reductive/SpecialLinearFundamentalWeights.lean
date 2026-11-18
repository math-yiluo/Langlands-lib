import Langlands.GroupScheme.Reductive.SpecialLinearTypeACoord
import Langlands.GroupScheme.Reductive.SpecialLinearPinningProof
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation

/-! # Fundamental weights of the actual special-linear diagonal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : ℕ} {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

variable (n k) in
/-- The sum of the first `a + 1` diagonal characters of `SL_{n+1}`. -/
def coordinateFundamentalChar (a : Fin n) : characterLattice 𝔻 :=
  ∑ y : Fin (n + 1), (if y.val ≤ a.val then (1 : ℤ) else 0) • weightChar n k y

section NumberedBase

variable {J : Type u} [Finite J]
    {P : RootDatum J
      (characterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n))))
      (cocharacterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin n))))}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    (B : P.Base) (e : B.support ≃ Fin n)
    (hnumber : ∀ a : B.support,
      P.root a.val = rootChar n k (e a).castSucc (e a).succ)

include hP hnumber

theorem coordinateFundamentalChar_pairing (a : Fin n) (j : B.support) :
    P.toLinearMap (coordinateFundamentalChar n k a) (P.coroot j) =
      if a = e j then 1 else 0 := by
  change P.coroot' j (coordinateFundamentalChar n k a) = _
  have h := (typeACoord hP).coroot'_sum
    ((hnumber j).trans (rootChar_eq_weightChar_sub _ _))
    (fun y => if y.val ≤ a.val then (1 : ℤ) else 0)
  change P.coroot' j (coordinateFundamentalChar n k a) =
    (if (e j).castSucc.val ≤ a.val then 1 else 0) -
      (if (e j).succ.val ≤ a.val then 1 else 0) at h
  rw [h]
  simp only [Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all only [Fin.ext_iff] <;> omega

/-- The integral dual basis agrees with the usual type-A partial sums. -/
theorem fundamentalWeightBasis_eq_coordinate (hspan : P.corootSpan ℤ = ⊤)
    (i : B.support) :
    Langlands.RootDatum.fundamentalWeightBasis P B hspan i =
      coordinateFundamentalChar n k (e i) := by
  classical
  apply (Langlands.RootDatum.fundamentalWeightBasis P B hspan).repr.injective
  ext j
  rw [Langlands.RootDatum.fundamentalWeightBasis_repr,
    Langlands.RootDatum.fundamentalWeightBasis_pairing,
    Langlands.RootDatum.fundamentalWeightBasis_repr,
    coordinateFundamentalChar_pairing hP B e hnumber]
  simp only [Equiv.apply_eq_iff_eq, eq_comm]

end NumberedBase

@[simp] theorem coordinateFundamentalChar_first (n : ℕ) :
    coordinateFundamentalChar (n + 1) k 0 = weightChar (n + 1) k 0 := by
  have h : ∀ y : Fin (n + 1 + 1), y.val ≤ (0 : Fin (n + 1)).val ↔ y = 0 := by
    intro y
    change y.val ≤ 0 ↔ y = 0
    rw [Nat.le_zero]
    constructor
    · intro hy
      exact Fin.ext hy
    · intro hy
      exact congrArg Fin.val hy
  simp only [coordinateFundamentalChar, h, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The last partial sum is the negative of the last diagonal character. -/
theorem coordinateFundamentalChar_last (n : ℕ) :
    coordinateFundamentalChar (n + 1) k (Fin.last n) =
      -weightChar (n + 1) k (Fin.last (n + 1)) := by
  have hpartial :
      coordinateFundamentalChar (n + 1) k (Fin.last n) =
        ∑ y : Fin (n + 1), weightChar (n + 1) k y.castSucc := by
    rw [coordinateFundamentalChar, Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc, Nat.not_succ_le_self, ite_false, zero_smul,
      add_zero]
    apply Finset.sum_congr rfl
    intro y _
    rw [ite_eq_left (Nat.le_of_lt_succ y.isLt), one_smul]
  rw [hpartial, eq_neg_iff_add_eq_zero, ← Fin.sum_univ_castSucc]
  apply (GeneralLinear.characterCoordEquiv (Fin (n + 1)) k).injective
  simp only [map_sum, weightChar, LinearEquiv.apply_symm_apply, map_zero]
  exact sum_weightCoord_eq_zero

section Endpoints

variable {J : Type u} [Finite J]
    {P : RootDatum J
      (characterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin (n + 1)))))
      (cocharacterLattice (splitTorus.commGroupScheme
        (Spec (CommRingCat.of k)) (ULift (Fin (n + 1)))))}
    (hP : IsRootDatumOf (diagonalTorus (n + 1) (CommRingCat.of k)) P)
    (B : P.Base) (e : B.support ≃ Fin (n + 1))
    (hnumber : ∀ a : B.support,
      P.root a.val = rootChar (n + 1) k (e a).castSucc (e a).succ)
    (hspan : P.corootSpan ℤ = ⊤)

include hP hnumber

/-- Under adjacent-root numbering the first fundamental weight reads the first diagonal entry. -/
theorem first_fundamentalWeightBasis :
    Langlands.RootDatum.fundamentalWeightBasis P B hspan (e.symm 0) =
      weightChar (n + 1) k 0 := by
  rw [fundamentalWeightBasis_eq_coordinate hP B e hnumber hspan,
    e.apply_symm_apply, coordinateFundamentalChar_first]

/-- The highest diagonal character of the dual column representation is the last weight. -/
theorem last_fundamentalWeightBasis :
    Langlands.RootDatum.fundamentalWeightBasis P B hspan (e.symm (Fin.last n)) =
      -weightChar (n + 1) k (Fin.last (n + 1)) := by
  rw [fundamentalWeightBasis_eq_coordinate hP B e hnumber hspan,
    e.apply_symm_apply, coordinateFundamentalChar_last]

end Endpoints

end Langlands.GroupScheme.SpecialLinear.FinSucc

namespace Langlands.GroupScheme

/-- Actual coordinate-numbered integral fundamental weights exist for every special-linear group. -/
def SpecialLinearCoordinateFundamentalWeightsStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    let T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (_ : IsRootDatumOf (SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of k)) P)
      (_ : P.IsReduced) (B : P.Base) (e : B.support ≃ Fin n)
      (hspan : P.corootSpan ℤ = ⊤),
      (∀ a : B.support, P.root a.val =
        SpecialLinear.FinSucc.rootChar n k (e a).castSucc (e a).succ) ∧
      ∀ a : B.support,
        Langlands.RootDatum.fundamentalWeightBasis P B hspan a =
          SpecialLinear.FinSucc.coordinateFundamentalChar n k (e a)

theorem specialLinearCoordinateFundamentalWeights :
    SpecialLinearCoordinateFundamentalWeightsStatement.{u} := by
  intro k _ n
  obtain ⟨J, hJ, P, hP, hred, B, e, hspan, hnumber, _⟩ :=
    SpecialLinear.FinSucc.exists_coordinateRootDatum n k
  have : Finite J := hJ
  exact ⟨J, hJ, P, hP, hred, B, e, hspan, hnumber,
    SpecialLinear.FinSucc.fundamentalWeightBasis_eq_coordinate hP B e hnumber hspan⟩

end Langlands.GroupScheme
