import Langlands.GroupScheme.OrthogonalMatrix.TypeD
import Langlands.GroupScheme.OrthogonalMatrix.Reductive
import Langlands.LinearAlgebra.TypeDNumberedLinear

/-! # Numbered type-D base on the actual split orthogonal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

namespace TypeDNumbering

open Langlands.TypeDNumberedVectors
open SymplecticMatrix (weightCoord weightCoord_inl weightCoord_inr)

variable {n : ℕ} {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- Each numbered simple coordinate vector is an actual orthogonal root. -/
theorem simple_mem_roots (hn : 2 ≤ n) (i : Fin n) :
    (GeneralLinear.characterCoordEquiv (Fin n) k).symm (simple hn i) ∈
      roots (identityTorus (Fin n) k) := by
  rw [roots_identityTorus, mem_roots_iff]
  by_cases hi : i.val + 1 < n
  · refine ⟨Sum.inl i, Sum.inl ⟨i.val + 1, hi⟩, ?_, ?_⟩
    · simp only [index_inl, ne_eq, Fin.ext_iff]
      omega
    · simp [simple_chain hn i hi]
  · refine ⟨Sum.inl (⟨n - 2, by omega⟩ : Fin n),
      Sum.inr (⟨n - 1, by omega⟩ : Fin n), ?_, ?_⟩
    · simp only [index_inl, index_inr, ne_eq, Fin.ext_iff]
      omega
    · simp [simple, hi, Pi.single_neg, sub_neg_eq_add]

variable {J : Type u}
  (P : RootDatum J
    (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))))
    (cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n)))))
  (hP : IsRootDatumOf (identityTorus (Fin n) k) P)

include hP

/-- The index of the actual root with the prescribed simple coordinates. -/
def simpleIndex (hn : 2 ≤ n) (i : Fin n) : J :=
  Classical.choose (show ∃ r : J,
    P.root r = (GeneralLinear.characterCoordEquiv (Fin n) k).symm (simple hn i) from
      Set.mem_range.mp (hP.2.1.symm ▸ simple_mem_roots hn i))

@[simp] theorem root_simpleIndex (hn : 2 ≤ n) (i : Fin n) :
    P.root (simpleIndex P hP hn i) =
      (GeneralLinear.characterCoordEquiv (Fin n) k).symm (simple hn i) :=
  Classical.choose_spec (show ∃ r : J,
    P.root r = (GeneralLinear.characterCoordEquiv (Fin n) k).symm (simple hn i) from
      Set.mem_range.mp (hP.2.1.symm ▸ simple_mem_roots hn i))

@[simp] theorem rootCoord_simpleIndex (hn : 2 ≤ n) (i : Fin n) :
    GeneralLinear.characterCoordEquiv (Fin n) k (P.root (simpleIndex P hP hn i)) =
      simple hn i := by
  rw [root_simpleIndex, LinearEquiv.apply_symm_apply]

/-- In the actual orthogonal root datum, corresponding roots and coroots have the same
 integral coordinate vector. -/
theorem corootCoord_eq_rootCoord (hn : 3 ≤ n) (r : J) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) k (P.coroot r) =
      GeneralLinear.characterCoordEquiv (Fin n) k (P.root r) := by
  have hr : P.root r ∈ roots (diagonalTorus (Fin n) (CommRingCat.of k)) := by
    rw [← roots_identityTorus, ← hP.2.1]
    exact Set.mem_range_self r
  obtain ⟨x, y, hxy, hxys, hroot⟩ := exists_eq_weightChar_add_of_mem_roots hr
  rw [coroot_eq_weightCochar_add hP (by simpa using hn) hxy hxys hroot, hroot,
    map_add, map_add, cocharacterCoordEquiv_weightCochar, cocharacterCoordEquiv_weightCochar,
    characterCoordEquiv_weightChar, characterCoordEquiv_weightChar]

@[simp] theorem corootCoord_simpleIndex (hn : 3 ≤ n) (i : Fin n) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) k
      (P.coroot (simpleIndex P hP (by omega : 2 ≤ n) i)) = simple (by omega : 2 ≤ n) i := by
  rw [corootCoord_eq_rootCoord P hP hn, rootCoord_simpleIndex]

/-- All actual roots have positive or negative coordinates in the numbered simple cone. -/
theorem rootCoord_mem_or_neg_mem (hn : 2 ≤ n) (r : J) :
    GeneralLinear.characterCoordEquiv (Fin n) k (P.root r) ∈ positiveCone hn ∨
      -(GeneralLinear.characterCoordEquiv (Fin n) k (P.root r)) ∈ positiveCone hn := by
  have hr : P.root r ∈ roots (diagonalTorus (Fin n) (CommRingCat.of k)) := by
    rw [← roots_identityTorus, ← hP.2.1]
    exact Set.mem_range_self r
  obtain ⟨x, y, hxy, hxys, hroot⟩ := exists_eq_weightChar_add_of_mem_roots hr
  have hidx : index x ≠ index y := by
    intro h
    rcases eq_or_eq_swap_of_index_eq h with h | h
    · exact hxy h
    · exact hxys h
  rw [hroot, map_add, characterCoordEquiv_weightChar, characterCoordEquiv_weightChar]
  have hweight (z : Fin n ⊕ Fin n) :
      weightCoord (Fin n) z = sgn z • Pi.single (index z) 1 := by
    rw [weightCoord_eq_single]
    ext a
    simp [Pi.single_apply]
  rw [hweight, hweight]
  exact signed_pair_mem_or_neg_mem hn _ _ hidx _ _ (sgn_eq x) (sgn_eq y)


/-- Independence of the numbered actual roots over the integers. -/
theorem linearIndependent_root_simpleIndex (hn : 2 ≤ n) :
    LinearIndependent ℤ (fun i => P.root (simpleIndex P hP hn i)) := by
  apply LinearIndependent.of_comp (GeneralLinear.characterCoordEquiv (Fin n) k).toLinearMap
  simpa only [Function.comp_def, LinearEquiv.coe_coe, rootCoord_simpleIndex] using
    linearIndependent_simple hn

/-- Independence of the numbered actual coroots over the integers. -/
theorem linearIndependent_coroot_simpleIndex (hn : 3 ≤ n) :
    LinearIndependent ℤ (fun i => P.coroot (simpleIndex P hP (by omega : 2 ≤ n) i)) := by
  apply LinearIndependent.of_comp (GeneralLinear.cocharacterCoordEquiv (Fin n) k).toLinearMap
  simpa only [Function.comp_def, LinearEquiv.coe_coe, corootCoord_simpleIndex P hP hn] using
    linearIndependent_simple (by omega : 2 ≤ n)

/-- Distinct numbered simple vectors give distinct root indices. -/
theorem simpleIndex_injective (hn : 2 ≤ n) : Function.Injective (simpleIndex P hP hn) := by
  intro i j hij
  apply (linearIndependent_root_simpleIndex P hP hn).injective
  exact congrArg P.root hij

/-- The finite support of the specified simple roots. -/
def simpleSupport (hn : 2 ≤ n) : Finset J := by
  classical
  exact Finset.univ.image (simpleIndex P hP hn)

@[simp] theorem coe_simpleSupport (hn : 2 ≤ n) :
    (simpleSupport P hP hn : Set J) = Set.range (simpleIndex P hP hn) := by
  classical
  ext r
  simp [simpleSupport]

omit hP in
private theorem mem_closure_of_coord_mem
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (E : M ≃ₗ[ℤ] (Fin n → ℤ)) (hn : 2 ≤ n) (f : Fin n → M)
    (hf : ∀ i, E (f i) = simple hn i) {x : M} (hx : E x ∈ positiveCone hn) :
    x ∈ AddSubmonoid.closure (Set.range f) := by
  have hle : positiveCone hn ≤
      (AddSubmonoid.closure (Set.range f)).comap E.symm.toAddMonoidHom := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    change E.symm (simple hn i) ∈ AddSubmonoid.closure (Set.range f)
    rw [← hf i, LinearEquiv.symm_apply_apply]
    exact AddSubmonoid.subset_closure (Set.mem_range_self i)
  have hy := hle hx
  change E.symm (E x) ∈ AddSubmonoid.closure (Set.range f) at hy
  simpa only [LinearEquiv.symm_apply_apply] using hy

/-- The prescribed support is an integral root-datum base. -/
def base (hn : 3 ≤ n) : P.Base where
  support := simpleSupport P hP (by omega)
  linearIndepOn_root := by
    rw [coe_simpleSupport, linearIndepOn_range_iff (simpleIndex_injective P hP _)]
    exact linearIndependent_root_simpleIndex P hP _
  linearIndepOn_coroot := by
    rw [coe_simpleSupport, linearIndepOn_range_iff (simpleIndex_injective P hP _)]
    exact linearIndependent_coroot_simpleIndex P hP hn
  root_mem_or_neg_mem r := by
    have hset : P.root '' (simpleSupport P hP (by omega : 2 ≤ n) : Set J) =
        Set.range (fun i => P.root (simpleIndex P hP (by omega : 2 ≤ n) i)) := by
      rw [coe_simpleSupport]
      ext x
      simp
    rw [hset]
    rcases rootCoord_mem_or_neg_mem P hP (by omega : 2 ≤ n) r with h | h
    · exact Or.inl (mem_closure_of_coord_mem _ _ _ (rootCoord_simpleIndex P hP _) h)
    · apply Or.inr
      apply mem_closure_of_coord_mem _ _ _ (rootCoord_simpleIndex P hP _)
      simpa only [map_neg] using h
  coroot_mem_or_neg_mem r := by
    have hset : P.coroot '' (simpleSupport P hP (by omega : 2 ≤ n) : Set J) =
        Set.range (fun i => P.coroot (simpleIndex P hP (by omega : 2 ≤ n) i)) := by
      rw [coe_simpleSupport]
      ext x
      simp
    rw [hset]
    have hc := rootCoord_mem_or_neg_mem P hP (by omega : 2 ≤ n) r
    rw [← corootCoord_eq_rootCoord P hP hn r] at hc
    rcases hc with h | h
    · exact Or.inl (mem_closure_of_coord_mem _ _ _ (corootCoord_simpleIndex P hP hn) h)
    · apply Or.inr
      apply mem_closure_of_coord_mem _ _ _ (corootCoord_simpleIndex P hP hn)
      simpa only [map_neg] using h


/-- The simple support carries the specified numbering. -/
def numbering (hn : 3 ≤ n) : (base P hP hn).support ≃ Fin n := by
  classical
  let f : Fin n → (base P hP hn).support := fun i =>
    ⟨simpleIndex P hP (by omega : 2 ≤ n) i, by simp [base, simpleSupport]⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro i j hij
    exact simpleIndex_injective P hP _ (congrArg Subtype.val hij)
  · intro r
    have hr : r.val ∈ Set.range (simpleIndex P hP (by omega : 2 ≤ n)) := by
      rw [← coe_simpleSupport]
      exact r.property
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, Subtype.ext hi⟩

@[simp] theorem simpleIndex_numbering (hn : 3 ≤ n) (a : (base P hP hn).support) :
    simpleIndex P hP (by omega : 2 ≤ n) (numbering P hP hn a) = a.val :=
  congrArg Subtype.val ((numbering P hP hn).symm_apply_apply a)

/-- Coordinate formula for every simple root in the numbered base. -/
theorem rootCoord_numbering (hn : 3 ≤ n) (a : (base P hP hn).support) :
    GeneralLinear.characterCoordEquiv (Fin n) k (P.root a.val) =
      simple (by omega : 2 ≤ n) (numbering P hP hn a) := by
  rw [← simpleIndex_numbering P hP hn a, rootCoord_simpleIndex]

/-- Coordinate formula for every simple coroot in the numbered base. -/
theorem corootCoord_numbering (hn : 3 ≤ n) (a : (base P hP hn).support) :
    GeneralLinear.cocharacterCoordEquiv (Fin n) k (P.coroot a.val) =
      simple (by omega : 2 ≤ n) (numbering P hP hn a) := by
  rw [← simpleIndex_numbering P hP hn a, corootCoord_simpleIndex P hP hn]

/-- Actual simple-root/coroot pairings have exactly the prescribed type-D numbering. -/
theorem pairing_simpleIndex (hn : 4 ≤ n) (i j : Fin n) :
    P.pairing (simpleIndex P hP (by omega : 2 ≤ n) i)
      (simpleIndex P hP (by omega : 2 ≤ n) j) = CartanMatrix.D n i j := by
  change P.toLinearMap _ _ = _
  rw [hP.1, GeneralLinear.latticePairing_coord, rootCoord_simpleIndex,
    corootCoord_simpleIndex P hP (by omega : 3 ≤ n)]
  exact dotProduct_simple hn i j

/-- The Cartan matrix of the actual integral base, in the chosen order. -/
theorem pairing_numbering (hn : 4 ≤ n)
    (a b : (base P hP (by omega : 3 ≤ n)).support) :
    P.pairing a.val b.val = CartanMatrix.D n
      (numbering P hP (by omega : 3 ≤ n) a)
      (numbering P hP (by omega : 3 ≤ n) b) := by
  rw [← simpleIndex_numbering P hP (by omega : 3 ≤ n) a,
    ← simpleIndex_numbering P hP (by omega : 3 ≤ n) b]
  exact pairing_simpleIndex P hP hn _ _


omit hP in
/-- Existence of a reduced actual split-orthogonal root datum with its numbered integral
 type-D base, over every field. -/
theorem exists_numberedRootDatum (hn : 4 ≤ n) :
    ∃ (J : Type u) (_ : Finite J)
      (Q : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)),
      IsRootDatumOf (identityTorus (Fin n) k) Q ∧ Q.IsReduced ∧
      ∃ (B : Q.Base) (e : B.support ≃ Fin n),
        (∀ a b : B.support, Q.pairing a.val b.val = CartanMatrix.D n (e a) (e b)) ∧
        (∀ a : B.support, GeneralLinear.characterCoordEquiv (Fin n) k (Q.root a.val) =
          simple (by omega : 2 ≤ n) (e a)) ∧
        ∀ a : B.support, GeneralLinear.cocharacterCoordEquiv (Fin n) k (Q.coroot a.val) =
          simple (by omega : 2 ≤ n) (e a) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨J, hJ, Q, hQ, hred⟩ := rootDatumExistence k _
    (isConnectedReductive_identityComponent (Fin n) k) 𝔻
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k) (identityTorus (Fin n) k)
    (isMaximalTorus_identityTorus (Fin n) k)
  exact ⟨J, hJ, Q, hQ, hred, base Q hQ (by omega), numbering Q hQ (by omega),
    pairing_numbering Q hQ hn, rootCoord_numbering Q hQ (by omega),
    corootCoord_numbering Q hQ (by omega)⟩

end TypeDNumbering

end Langlands.GroupScheme.OrthogonalMatrix
