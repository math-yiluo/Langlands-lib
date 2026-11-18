import Langlands.GroupScheme.OddOrthogonalMatrix.SignedCoroots
import Langlands.LinearAlgebra.TypeBNumberedVectors

/-! # Numbered type-B base on the actual split odd torus -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering

open Langlands.TypeBNumberedVectors

variable {n : ℕ} {K : Type u} [Field K]

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n))

/-- Each numbered simple coordinate vector is an actual odd root. -/
theorem simple_mem_roots (i : Fin n) :
    (GeneralLinear.characterCoordEquiv (Fin n) K).symm (simple i) ∈
      roots (identityTorus (Fin n) K) := by
  rw [roots_identityTorus, mem_roots_iff]
  by_cases hi : i.val + 1 < n
  · refine Or.inr ⟨Sum.inl i, Sum.inl ⟨i.val + 1, hi⟩, ?_, ?_⟩
    · simp only [OrthogonalMatrix.index_inl, ne_eq, Fin.ext_iff]; omega
    · simp [simpleWithLast_chain 1 i hi]
  · refine Or.inl ⟨Sum.inl i, ?_⟩
    simp [simpleWithLast_last 1 i hi]

variable {J : Type u}
  (P : RootDatum J
    (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n))))
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin n)))))
  (hP : IsRootDatumOf (identityTorus (Fin n) K) P)

include hP

/-- The actual root index with the specified simple coordinates. -/
def simpleIndex (i : Fin n) : J :=
  Classical.choose (show ∃ r : J,
    P.root r = (GeneralLinear.characterCoordEquiv (Fin n) K).symm (simple i) from
      Set.mem_range.mp (hP.2.1.symm ▸ simple_mem_roots i))

@[simp] theorem root_simpleIndex (i : Fin n) :
    P.root (simpleIndex P hP i) =
      (GeneralLinear.characterCoordEquiv (Fin n) K).symm (simple i) :=
  Classical.choose_spec (show ∃ r : J,
    P.root r = (GeneralLinear.characterCoordEquiv (Fin n) K).symm (simple i) from
      Set.mem_range.mp (hP.2.1.symm ▸ simple_mem_roots i))

@[simp] theorem rootCoord_simpleIndex (i : Fin n) :
    GeneralLinear.characterCoordEquiv (Fin n) K (P.root (simpleIndex P hP i)) = simple i := by
  rw [root_simpleIndex, LinearEquiv.apply_symm_apply]

/-- The final short simple root has doubled coroot; the chain coroots are differences. -/
@[simp] theorem corootCoord_simpleIndex (i : Fin n) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) K (P.coroot (simpleIndex P hP i)) =
      simpleCoroot i := by
  by_cases hi : i.val + 1 < n
  · have hab : i ≠ (⟨i.val + 1, hi⟩ : Fin n) := by
      simp only [ne_eq, Fin.ext_iff]; omega
    have hr : P.root (simpleIndex P hP i) = basisCharacter (Fin n) K i -
        basisCharacter (Fin n) K ⟨i.val + 1, hi⟩ := by
      apply (GeneralLinear.characterCoordEquiv (Fin n) K).injective
      simp [simpleWithLast_chain 1 i hi]
    rw [coroot_of_basisCharacter_sub hP hab hr, map_sub, cocharacterCoord_basisCocharacter,
      cocharacterCoord_basisCocharacter]
    exact (simpleWithLast_chain 2 i hi).symm
  · have hr : P.root (simpleIndex P hP i) = basisCharacter (Fin n) K i := by
      apply (GeneralLinear.characterCoordEquiv (Fin n) K).injective
      simp [simpleWithLast_last 1 i hi]
    rw [coroot_of_basisCharacter hP hr, map_nsmul, cocharacterCoord_basisCocharacter]
    exact (simpleWithLast_last 2 i hi).symm

omit hP in
private theorem signedWeight_mem_or_neg_mem (d : ℕ) (hd : d = 1 ∨ d = 2)
    (a b : Fin n ⊕ Fin n) :
    SymplecticMatrix.weightCoord (Fin n) a - SymplecticMatrix.weightCoord (Fin n) b ∈
        positiveCone d ∨
      -(SymplecticMatrix.weightCoord (Fin n) a - SymplecticMatrix.weightCoord (Fin n) b) ∈
        positiveCone d := by
  rcases a with a | a <;> rcases b with b | b
  · simpa [← Pi.single_neg, sub_eq_add_neg] using
      signed_pair_mem_or_neg_mem d hd a b 1 (-1) (Or.inl rfl) (Or.inr rfl)
  · simpa [← Pi.single_neg, sub_eq_add_neg] using signed_pair_mem_or_neg_mem d hd a b 1 1 (Or.inl rfl) (Or.inl rfl)
  · simpa [← Pi.single_neg, sub_eq_add_neg] using
      signed_pair_mem_or_neg_mem d hd a b (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  · simpa [← Pi.single_neg, sub_eq_add_neg] using
      signed_pair_mem_or_neg_mem d hd a b (-1) 1 (Or.inr rfl) (Or.inl rfl)

/-- Every actual root lies in the simple-root cone or its negative. -/
theorem rootCoord_mem_or_neg_mem (r : J) :
    GeneralLinear.characterCoordEquiv (Fin n) K (P.root r) ∈ positiveCone 1 ∨
      -(GeneralLinear.characterCoordEquiv (Fin n) K (P.root r)) ∈ positiveCone 1 := by
  rcases root_coroot_coordinates hP r with ⟨a, hr, _⟩ | ⟨a, b, _, hr, _⟩
  · rw [hr, characterCoord_signedCharacter]
    rcases a with a | a
    · exact Or.inl (single_mem_positiveCone a)
    · exact Or.inr (by simpa [← Pi.single_neg] using single_mem_positiveCone a)
  · rw [hr, map_sub, characterCoord_signedCharacter, characterCoord_signedCharacter]
    exact signedWeight_mem_or_neg_mem 1 (Or.inl rfl) a b

/-- Every actual coroot lies in the simple-coroot cone or its negative. -/
theorem corootCoord_mem_or_neg_mem (r : J) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) K (P.coroot r) ∈ positiveCone 2 ∨
      -(GeneralLinear.cocharacterCoordEquiv (Fin n) K (P.coroot r)) ∈ positiveCone 2 := by
  rcases root_coroot_coordinates hP r with ⟨a, _, hr⟩ | ⟨a, b, _, _, hr⟩
  · rw [hr, map_nsmul, cocharacterCoord_signedCocharacter]
    rcases a with a | a
    · exact Or.inl (nsmul_single_mem_positiveCone 2 a)
    · right
      change -(2 • Pi.single a (-1 : ℤ)) ∈ positiveCone 2
      rw [Pi.single_neg, smul_neg, neg_neg]
      exact nsmul_single_mem_positiveCone 2 a
  · rw [hr, map_sub, cocharacterCoord_signedCocharacter, cocharacterCoord_signedCocharacter]
    exact signedWeight_mem_or_neg_mem 2 (Or.inr rfl) a b

/-- Independence of the numbered actual roots over the integers. -/
theorem linearIndependent_root_simpleIndex :
    LinearIndependent ℤ (fun i => P.root (simpleIndex P hP i)) := by
  apply LinearIndependent.of_comp (GeneralLinear.characterCoordEquiv (Fin n) K).toLinearMap
  simpa only [Function.comp_def, LinearEquiv.coe_coe, rootCoord_simpleIndex] using
    linearIndependent_simple (n := n)

/-- Independence of the numbered actual coroots over the integers. -/
theorem linearIndependent_coroot_simpleIndex :
    LinearIndependent ℤ (fun i => P.coroot (simpleIndex P hP i)) := by
  apply LinearIndependent.of_comp (GeneralLinear.cocharacterCoordEquiv (Fin n) K).toLinearMap
  simpa only [Function.comp_def, LinearEquiv.coe_coe, corootCoord_simpleIndex] using
    linearIndependent_simpleCoroot (n := n)

/-- Distinct numbered simple vectors give distinct actual root indices. -/
theorem simpleIndex_injective : Function.Injective (simpleIndex P hP) := by
  intro i j hij
  apply (linearIndependent_root_simpleIndex P hP).injective
  exact congrArg P.root hij

/-- The finite support of the prescribed simple roots. -/
def simpleSupport : Finset J := by
  classical
  exact Finset.univ.image (simpleIndex P hP)

@[simp] theorem coe_simpleSupport :
    (simpleSupport P hP : Set J) = Set.range (simpleIndex P hP) := by
  classical
  ext r
  simp [simpleSupport]

omit hP in
private theorem mem_closure_of_coord_mem
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (E : M ≃ₗ[ℤ] (Fin n → ℤ)) (d : ℕ) (f : Fin n → M)
    (hf : ∀ i, E (f i) = simpleWithLast d i) {x : M} (hx : E x ∈ positiveCone d) :
    x ∈ AddSubmonoid.closure (Set.range f) := by
  have hle : positiveCone d ≤
      (AddSubmonoid.closure (Set.range f)).comap E.symm.toAddMonoidHom := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    change E.symm (simpleWithLast d i) ∈ AddSubmonoid.closure (Set.range f)
    rw [← hf i, LinearEquiv.symm_apply_apply]
    exact AddSubmonoid.subset_closure (Set.mem_range_self i)
  have hy := hle hx
  change E.symm (E x) ∈ AddSubmonoid.closure (Set.range f) at hy
  simpa only [LinearEquiv.symm_apply_apply] using hy

/-- The prescribed support is an integral root-datum base. -/
def base : P.Base where
  support := simpleSupport P hP
  linearIndepOn_root := by
    rw [coe_simpleSupport, linearIndepOn_range_iff (simpleIndex_injective P hP)]
    exact linearIndependent_root_simpleIndex P hP
  linearIndepOn_coroot := by
    rw [coe_simpleSupport, linearIndepOn_range_iff (simpleIndex_injective P hP)]
    exact linearIndependent_coroot_simpleIndex P hP
  root_mem_or_neg_mem r := by
    have hset : P.root '' (simpleSupport P hP : Set J) =
        Set.range (fun i => P.root (simpleIndex P hP i)) := by
      rw [coe_simpleSupport]
      ext x
      simp
    rw [hset]
    rcases rootCoord_mem_or_neg_mem P hP r with h | h
    · exact Or.inl (mem_closure_of_coord_mem _ 1 _ (rootCoord_simpleIndex P hP) h)
    · apply Or.inr
      apply mem_closure_of_coord_mem _ 1 _ (rootCoord_simpleIndex P hP)
      simpa only [map_neg] using h
  coroot_mem_or_neg_mem r := by
    have hset : P.coroot '' (simpleSupport P hP : Set J) =
        Set.range (fun i => P.coroot (simpleIndex P hP i)) := by
      rw [coe_simpleSupport]
      ext x
      simp
    rw [hset]
    rcases corootCoord_mem_or_neg_mem P hP r with h | h
    · exact Or.inl (mem_closure_of_coord_mem _ 2 _ (corootCoord_simpleIndex P hP) h)
    · apply Or.inr
      apply mem_closure_of_coord_mem _ 2 _ (corootCoord_simpleIndex P hP)
      simpa only [map_neg] using h

/-- The support carries the specified numbering. -/
def numbering : (base P hP).support ≃ Fin n := by
  classical
  let f : Fin n → (base P hP).support := fun i =>
    ⟨simpleIndex P hP i, by simp [base, simpleSupport]⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro i j hij
    exact simpleIndex_injective P hP (congrArg Subtype.val hij)
  · intro r
    have hr : r.val ∈ Set.range (simpleIndex P hP) := by
      rw [← coe_simpleSupport]
      exact r.property
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, Subtype.ext hi⟩

@[simp] theorem simpleIndex_numbering (a : (base P hP).support) :
    simpleIndex P hP (numbering P hP a) = a.val :=
  congrArg Subtype.val ((numbering P hP).symm_apply_apply a)

/-- Integral coordinates of each numbered simple root. -/
theorem rootCoord_numbering (a : (base P hP).support) :
    GeneralLinear.characterCoordEquiv (Fin n) K (P.root a.val) = simple (numbering P hP a) := by
  rw [← simpleIndex_numbering P hP a, rootCoord_simpleIndex]

/-- Integral coordinates of each numbered simple coroot. -/
theorem corootCoord_numbering (a : (base P hP).support) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) K (P.coroot a.val) =
      simpleCoroot (numbering P hP a) := by
  rw [← simpleIndex_numbering P hP a, corootCoord_simpleIndex]

/-- The exact Cartan pairings in the numbered simple family. -/
theorem pairing_simpleIndex (hn : 2 ≤ n) (i j : Fin n) :
    P.pairing (simpleIndex P hP i) (simpleIndex P hP j) = CartanMatrix.B n i j := by
  change P.toLinearMap _ _ = _
  rw [hP.1, GeneralLinear.latticePairing_coord, rootCoord_simpleIndex, corootCoord_simpleIndex]
  exact dotProduct_simple hn i j

/-- The actual base has precisely Mathlib's type-B Cartan matrix in this numbering. -/
theorem pairing_numbering (hn : 2 ≤ n) (a b : (base P hP).support) :
    P.pairing a.val b.val = CartanMatrix.B n (numbering P hP a) (numbering P hP b) := by
  rw [← simpleIndex_numbering P hP a, ← simpleIndex_numbering P hP b]
  exact pairing_simpleIndex P hP hn _ _

omit hP in
/-- Existence of an actual reduced root datum with a numbered integral type-B base. -/
theorem exists_numberedRootDatum (hn : 2 ≤ n) :
    ∃ (J : Type u) (_ : Finite J)
      (Q : RootDatum J (characterLattice 𝔗) (cocharacterLattice 𝔗)),
      IsRootDatumOf (identityTorus (Fin n) K) Q ∧ Q.IsReduced ∧
      ∃ (B : Q.Base) (e : B.support ≃ Fin n),
        (∀ a b : B.support, Q.pairing a.val b.val = CartanMatrix.B n (e a) (e b)) ∧
        (∀ a : B.support, GeneralLinear.characterCoordEquiv (Fin n) K (Q.root a.val) =
          simple (e a)) ∧
        ∀ a : B.support, GeneralLinear.cocharacterCoordEquiv (Fin n) K (Q.coroot a.val) =
          simpleCoroot (e a) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨J, hJ, Q, hQ, hred⟩ := rootDatumExistence K _ (identityReductive (Fin n) K) 𝔗
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) K) (identityTorus (Fin n) K)
    (isMaximalTorus_identityTorus (Fin n) K)
  exact ⟨J, hJ, Q, hQ, hred, base Q hQ, numbering Q hQ,
    pairing_numbering Q hQ hn, rootCoord_numbering Q hQ, corootCoord_numbering Q hQ⟩

end Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering
