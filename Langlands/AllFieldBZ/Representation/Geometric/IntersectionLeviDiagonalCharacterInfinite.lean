-- MANUAL
import Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof

/-!
# Diagonal determination of intersection-Levi characters over infinite fields

The Library proves `Langlands.Geometric.intersectionLeviDiagonalCharacterTheorem` for fields of
characteristic zero, conjugating a transvection by the diagonal scalar `2`. This module proves
the same conclusion for every infinite field, which includes every nonarchimedean local field of
positive characteristic: conjugation by a diagonal scalar `c ∉ {0, 1}` turns the transvection
with entry `x` into the one with entry `c * x`, so every character kills the transvection with
entry `(c - 1) * x`, hence every transvection.
-/

noncomputable section

namespace Langlands.AllFieldBZ.Geometric

open Langlands.Geometric Langlands.GeneralLinear

universe uF

namespace DiagonalCharacter

open Langlands.Geometric.DiagonalCharacter

variable {F : Type uF} [Field F]

/-- Scaling row `i` by `c` conjugates the transvection with entry `x` to the one with entry
`c * x`. -/
theorem scale_transvection_by {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : F) (hc : c ≠ 0)
    (x : F) :
    diagonalUnit (fun a => if a = i then Units.mk0 c hc else 1) * transvectionUnit i j hij x =
      transvectionUnit i j hij (c * x) *
        diagonalUnit (fun a => if a = i then Units.mk0 c hc else 1) := by
  apply Units.ext
  change Matrix.diagonal _ * Matrix.transvection i j x =
    Matrix.transvection i j (c * x) * Matrix.diagonal _
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      simp [Matrix.transvection, Matrix.single, hij, hij.symm]
    · by_cases hbi : b = i
      · subst b
        simp [Matrix.transvection, Matrix.single, hij.symm]
      · simp [Matrix.transvection, Matrix.single, Ne.symm hbj, hbi, Ne.symm hbi]
  · by_cases hab : a = b
    · subst b
      simp [Matrix.transvection, Matrix.single, hai, Ne.symm hai]
    · simp [Matrix.transvection, Matrix.single, hai, Ne.symm hai, hab]

/-- Over an infinite field, every character into complex units kills every transvection. -/
theorem character_transvection [Infinite F] {k : ℕ}
    (χ : GeneralLinear k F →* ℂˣ) (i j : Fin k) (hij : i ≠ j) (y : F) :
    χ (transvectionUnit i j hij y) = 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset F)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hc1 : c - 1 ≠ 0 := fun h => hc (by simp [sub_eq_zero.mp h])
  let d : GeneralLinear k F := diagonalUnit (fun a => if a = i then Units.mk0 c hc0 else 1)
  set x : F := y / (c - 1) with hx
  have hmul : transvectionUnit i j hij (c * x) =
      transvectionUnit i j hij x * transvectionUnit i j hij y := by
    apply Units.ext
    change Matrix.transvection i j (c * x) =
      Matrix.transvection i j x * Matrix.transvection i j y
    rw [Matrix.transvection_mul_transvection_same _ _ hij]
    congr 1
    rw [hx]
    field_simp
    ring
  have h := congrArg χ (scale_transvection_by i j hij c hc0 x)
  rw [hmul] at h
  simp only [map_mul] at h
  set u := χ (transvectionUnit i j hij x)
  set v := χ (transvectionUnit i j hij y)
  set w := χ (diagonalUnit (fun a => if a = i then Units.mk0 c hc0 else 1))
  have h2 : u * w * v = u * w * 1 :=
    calc u * w * v = u * v * w := mul_right_comm _ _ _
      _ = w * u := h.symm
      _ = u * w * 1 := by rw [mul_one, mul_comm]
  exact mul_left_cancel h2

/-- Over an infinite field, a character of `GL_k` trivial on all unit diagonals is trivial. -/
theorem character_GL [Infinite F] {k : ℕ} (χ : GeneralLinear k F →* ℂˣ)
    (hdiag : ∀ t : Fin k → Fˣ, χ (diagonalUnit t) = 1) :
    ∀ g, χ g = 1 := by
  intro g
  let P : Matrix (Fin k) (Fin k) F → Prop :=
    fun A => ∀ h : GeneralLinear k F, h.val = A → χ h = 1
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero P g.val
    (Matrix.GeneralLinearGroup.det_ne_zero g) ?_ ?_ ?_ g rfl
  · intro D hD h hh
    have hn (i : Fin k) : D i ≠ 0 := by
      have hp : ∏ i, D i ≠ 0 := by simpa only [Matrix.det_diagonal] using hD
      exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
    have he : h = diagonalUnit (fun i => Units.mk0 (D i) (hn i)) :=
      Units.ext hh
    rw [he]
    exact hdiag _
  · intro t h hh
    have he : h = transvectionUnit t.i t.j t.hij t.c := Units.ext hh
    rw [he]
    exact character_transvection χ _ _ _ _
  · intro A B hA hB PA PB h hh
    let a := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
    let b := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
    have he : h = a * b := Units.ext hh
    rw [he, map_mul, PA a rfl, PB b rfl, one_mul]

/-- Over an infinite field, simultaneous unit diagonals determine characters of a finite
product of general linear groups. -/
theorem character_pi_GL [Infinite F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) (χ : (∀ i, GeneralLinear (d i) F) →* ℂˣ)
    (hdiag : ∀ t : ∀ i, Fin (d i) → Fˣ,
      χ (fun i => diagonalUnit (t i)) = 1) :
    ∀ g, χ g = 1 := by
  apply character_pi χ
  intro i g
  apply character_GL
    (χ.comp (MonoidHom.mulSingle (fun j => GeneralLinear (d j) F) i)) ?_ g
  intro t
  have he : Pi.mulSingle i (diagonalUnit t) =
      fun j => diagonalUnit ((Pi.mulSingle (M := fun j => Fin (d j) → Fˣ) i t) j) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Pi.mulSingle_eq_of_ne hj, diagonalUnit_one]
  change χ (Pi.mulSingle i (diagonalUnit t)) = 1
  rw [he]
  exact hdiag _

end DiagonalCharacter

/-- The diagonal-determination statement for the actual intersection Levi over an infinite
field: a complex character of the intersection Levi that is trivial on every actual diagonal
matrix is trivial. This is `IntersectionLeviDiagonalCharacterStatement` with `[CharZero F]`
replaced by `[Infinite F]`. -/
theorem intersectionLeviDiagonalCharacter_of_infinite (F : Type uF) [Field F] [Infinite F]
    (n : ℕ) (B C : GeneralLinear.BlockShape n) (w : MinimalRepresentatives B C) :
    let I := General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F)
      (GeneralLinear.permutation n F w.val)
    ∀ χ : I →* ℂˣ,
      (∀ (t : Fin n → Fˣ) (m : I),
        (m.val.val : Matrix (Fin n) (Fin n) F) =
          Matrix.diagonal (fun i => (t i : F)) → χ m = 1) →
      ∀ m : I, χ m = 1 := by
  classical
  dsimp only
  intro χ hdiag m
  obtain ⟨S, _, hS, _⟩ :=
    exists_standardIntersections F B C w.val w.property.1
  let e := ((refinedLeviEquiv F B S).trans
    (MulEquiv.subgroupCongr hS.symm)).trans
      (Langlands.Geometric.DiagonalCharacter.sourceActualEquiv B C w.val)
  let ψ := χ.comp e.toMonoidHom
  have hd (t : ∀ i, ∀ j : Fin (S i).length, Fin ((S i).size j) → Fˣ) :
      ψ (fun i j => Langlands.Geometric.DiagonalCharacter.diagonalUnit (t i j)) = 1 := by
    let r : ∀ i, Fin (B.size i) → Fˣ := fun i a =>
      t i ((S i).indexEquiv.symm a).1 ((S i).indexEquiv.symm a).2
    let a : Fin n → Fˣ := fun x =>
      r (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2
    apply hdiag a (e _)
    change (B.leviEmbedding F (fun i =>
      (S i).leviEmbedding F (fun j =>
        Langlands.Geometric.DiagonalCharacter.diagonalUnit (t i j)))).val =
        Matrix.diagonal (fun x => (a x : F))
    have he : (fun i =>
        (S i).leviEmbedding F (fun j =>
          Langlands.Geometric.DiagonalCharacter.diagonalUnit (t i j))) =
        fun i => Langlands.Geometric.DiagonalCharacter.diagonalUnit (r i) := by
      funext i
      apply Units.ext
      exact Langlands.Geometric.DiagonalCharacter.leviEmbedding_diagonalUnit (S i) (t i)
    rw [he]
    exact Langlands.Geometric.DiagonalCharacter.leviEmbedding_diagonalUnit B r
  have hp : ∀ g, ψ g = 1 := by
    apply Langlands.Geometric.DiagonalCharacter.character_pi ψ
    intro i g
    let φ := ψ.comp (MonoidHom.mulSingle (fun i => (S i).Levi F) i)
    apply DiagonalCharacter.character_pi_GL (S i).size φ ?_ g
    intro t
    let T := Pi.mulSingle
      (M := fun k => ∀ j : Fin (S k).length, Fin ((S k).size j) → Fˣ) i t
    have he : Pi.mulSingle i (fun j => Langlands.Geometric.DiagonalCharacter.diagonalUnit (t j)) =
        fun k j => Langlands.Geometric.DiagonalCharacter.diagonalUnit (T k j) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [T]
      · funext j
        simp [T, Pi.mulSingle_eq_of_ne hk,
          Langlands.Geometric.DiagonalCharacter.diagonalUnit_one]
    change ψ (Pi.mulSingle i
      (fun j => Langlands.Geometric.DiagonalCharacter.diagonalUnit (t j))) = 1
    rw [he]
    exact hd T
  have h := hp (e.symm m)
  change χ (e (e.symm m)) = 1 at h
  rw [e.apply_symm_apply] at h
  exact h

end Langlands.AllFieldBZ.Geometric
