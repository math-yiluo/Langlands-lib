import Langlands.GroupScheme.Reductive.SpecialLinearTorus
import Langlands.GroupScheme.Torus.SelfCentralizingFromLie
import Langlands.GroupScheme.Lie.SplitTorusCoordinates

/-! # Maximality of the diagonal torus of `SL_{n+1}` and its roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : ℕ}

/-! ### Maximality over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- The zero weight space consists of the Lie algebra elements with diagonal matrix. -/
theorem mem_weightSpace_zero_iff
    (X : Additive (lieKernel (groupScheme (Fin (n + 1)) (CommRingCat.of k)) k)) :
    X ∈ weightSpace (diagonalTorus n (CommRingCat.of k)) 0 ↔
      ∀ x y : Fin (n + 1), x ≠ y → lieMatrix X x y = 0 := by
  rw [mem_weightSpace_diagonalTorus_iff_support, map_zero]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  have hw : (0 : Fin n → ℤ) = weightCoord n x - weightCoord n y ↔ x = y := by
    rw [eq_comm, sub_eq_zero]
    exact weightCoord_injective.eq_iff
  rw [hw]
  exact not_imp_comm

variable (n k) in
/-- The first `n` diagonal entries of an element of the zero weight space. -/
def zeroWeightCoord :
    weightSpace (diagonalTorus n (CommRingCat.of k)) 0 →ₗ[k] (Fin n → k) where
  toFun X a := lieMatrix (X : Additive (lieKernel (groupScheme (Fin (n + 1))
    (CommRingCat.of k)) k)) a.castSucc a.castSucc
  map_add' X Y := by
    funext a
    simp only [Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext a
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      RingHom.id_apply]

theorem zeroWeightCoord_apply (X : weightSpace (diagonalTorus n (CommRingCat.of k)) 0)
    (a : Fin n) :
    zeroWeightCoord n k X a =
      lieMatrix (X : Additive (lieKernel (groupScheme (Fin (n + 1)) (CommRingCat.of k)) k))
        a.castSucc a.castSucc :=
  rfl

/-- An element of the zero weight space is determined by its first `n` diagonal entries: the
last one is minus their sum, because the trace vanishes. -/
theorem lieMatrix_eq_zero_of_zeroWeightCoord
    (X : weightSpace (diagonalTorus n (CommRingCat.of k)) 0) (hX : zeroWeightCoord n k X = 0) :
    lieMatrix (X : Additive (lieKernel (groupScheme (Fin (n + 1)) (CommRingCat.of k)) k)) =
      0 := by
  obtain ⟨Xv, hXv⟩ := X
  have hd : ∀ x y : Fin (n + 1), x ≠ y → lieMatrix Xv x y = 0 :=
    (mem_weightSpace_zero_iff Xv).mp hXv
  have h0 : ∀ a : Fin n, lieMatrix Xv a.castSucc a.castSucc = 0 := fun a => by
    have h := congrFun hX a
    rw [zeroWeightCoord_apply, Pi.zero_apply] at h
    exact h
  have htr := trace_lieMatrix Xv
  rw [Matrix.trace, Fin.sum_univ_castSucc] at htr
  simp only [Matrix.diag_apply, h0, Finset.sum_const_zero, zero_add] at htr
  change lieMatrix Xv = 0
  ext x y
  rw [Matrix.zero_apply]
  by_cases hxy : x = y
  · subst hxy
    induction x using Fin.lastCases with
    | last => exact htr
    | cast a => exact h0 a
  · exact hd x y hxy

/-- The diagonal entries `(d, -∑ d)` of a trace-zero diagonal matrix. -/
def diagonalEntries (d : Fin n → k) : Fin (n + 1) → k :=
  Fin.snoc d (-∑ a, d a)

theorem trace_diagonal_diagonalEntries (d : Fin n → k) :
    (Matrix.diagonal (diagonalEntries d)).trace = 0 := by
  rw [Matrix.trace_diagonal, Fin.sum_univ_castSucc]
  simp only [diagonalEntries, Fin.snoc_castSucc, Fin.snoc_last, add_neg_cancel]

theorem zeroWeightCoord_bijective : Function.Bijective (zeroWeightCoord n k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [lieMatrix_eq_zero_of_zeroWeightCoord X hX, Submodule.coe_zero, map_zero]
  · intro d
    obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _
      (trace_diagonal_diagonalEntries d)
    have hmem : X ∈ weightSpace (diagonalTorus n (CommRingCat.of k)) 0 := by
      rw [mem_weightSpace_zero_iff, hX]
      intro x y hxy
      exact Matrix.diagonal_apply_ne _ hxy
    refine ⟨⟨X, hmem⟩, ?_⟩
    funext a
    rw [zeroWeightCoord_apply]
    change lieMatrix X a.castSucc a.castSucc = d a
    rw [hX, Matrix.diagonal_apply_eq]
    exact Fin.snoc_castSucc _ _ _

/-- The zero weight space of the diagonal torus has dimension `n`. -/
theorem finrank_weightSpace_zero :
    Module.finrank k (weightSpace (diagonalTorus n (CommRingCat.of k)) 0) = n := by
  rw [(LinearEquiv.ofBijective (zeroWeightCoord n k) zeroWeightCoord_bijective).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

variable (n k) in
/-- **Maximality.** The diagonal torus of `SL_{n+1}` over a field is a maximal torus. -/
theorem isMaximalTorus_diagonalTorus :
    IsMaximalTorus (diagonalTorus n (CommRingCat.of k)) := by
  have : IsAffineHom (𝔻).toGrp.X.hom := isAffineHom_splitTorus _ _
  refine isMaximalTorus_of_finrank_zeroWeight _ (isSplitTorus_diagonalTorus n k)
    (isClosedSubgroup_diagonalTorus n k) ?_
  rw [finrank_weightSpace_zero]
  have h := splitTorus.finrank_lieKernel (ULift.{u} (Fin n)) k
  rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h.symm

/-! ### Roots -/

/-- Every root of the diagonal torus is a weight difference `w(p) - w(q)`. -/
theorem exists_coord_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus n (CommRingCat.of k))) :
    ∃ p q : Fin (n + 1), p ≠ q ∧
      GeneralLinear.characterCoordEquiv (Fin n) k χ = weightCoord n p - weightCoord n q := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
  obtain ⟨p, q, hpq⟩ : ∃ p q, lieMatrix X p q ≠ 0 := by
    by_contra h
    apply hX0
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [map_zero]
    refine Matrix.ext fun x y => ?_
    rw [Matrix.zero_apply]
    by_contra hne
    exact h ⟨x, y, hne⟩
  have hc := (mem_weightSpace_diagonalTorus_iff_support X χ).mp hX p q hpq
  refine ⟨p, q, fun e => hχ.1 ?_, hc⟩
  subst e
  rw [sub_self] at hc
  exact (GeneralLinear.characterCoordEquiv (Fin n) k).injective (hc.trans (map_zero _).symm)

variable (n k) in
/-- The character with coordinates `w(p) - w(q)`. -/
def rootChar (p q : Fin (n + 1)) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv (Fin n) k).symm (weightCoord n p - weightCoord n q)

theorem characterCoordEquiv_rootChar (p q : Fin (n + 1)) :
    GeneralLinear.characterCoordEquiv (Fin n) k (rootChar n k p q) =
      weightCoord n p - weightCoord n q :=
  LinearEquiv.apply_symm_apply _ _

/-- For `p ≠ q` the character `w(p) - w(q)` is a root, with root vector the matrix unit at
`(p, q)`. -/
theorem rootChar_mem_roots {p q : Fin (n + 1)} (hpq : p ≠ q) :
    rootChar n k p q ∈ roots (diagonalTorus n (CommRingCat.of k)) := by
  refine ⟨fun h0 => hpq ?_, ?_⟩
  · have h1 := characterCoordEquiv_rootChar (k := k) p q
    rw [h0, map_zero, eq_comm, sub_eq_zero] at h1
    exact weightCoord_injective h1
  · obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _
      (Matrix.trace_single_eq_of_ne p q (1 : k) hpq)
    rw [Submodule.ne_bot_iff]
    refine ⟨X, ?_, fun h0 => ?_⟩
    · rw [mem_weightSpace_diagonalTorus_iff_support, hX, characterCoordEquiv_rootChar]
      intro x y hxy
      obtain ⟨rfl, rfl⟩ : x = p ∧ y = q := by
        by_contra h
        exact hxy (Matrix.single_apply_of_ne _ _ _ _ _ fun e => h ⟨e.1.symm, e.2.symm⟩)
      rfl
    · have h1 := congrArg (fun Y => lieMatrix Y p q) h0
      simp only [hX, map_zero, Matrix.single_apply_same, Matrix.zero_apply] at h1
      exact one_ne_zero h1

/-- **Roots of `SL_{n+1}`.** A character of the diagonal torus is a root exactly when its
coordinates are `w(p) - w(q)` for distinct `p, q`. -/
theorem mem_roots_iff (χ : characterLattice 𝔻) :
    χ ∈ roots (diagonalTorus n (CommRingCat.of k)) ↔
      ∃ p q : Fin (n + 1), p ≠ q ∧
        GeneralLinear.characterCoordEquiv (Fin n) k χ = weightCoord n p - weightCoord n q := by
  refine ⟨exists_coord_of_mem_roots, ?_⟩
  rintro ⟨p, q, hpq, hχ⟩
  have : χ = rootChar n k p q :=
    (GeneralLinear.characterCoordEquiv (Fin n) k).injective
      (hχ.trans (characterCoordEquiv_rootChar p q).symm)
  rw [this]
  exact rootChar_mem_roots hpq

end Field

end Langlands.GroupScheme.SpecialLinear.FinSucc
