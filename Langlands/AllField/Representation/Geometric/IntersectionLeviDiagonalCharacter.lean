import Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof
import Mathlib.NumberTheory.LocalField.Basic

/-! Character determination by actual diagonal matrices on the intersection Levi,
over every field containing an element other than `0` and `1`; in particular over
every nonarchimedean local field, of any characteristic. -/

noncomputable section

namespace Langlands.AllField.Geometric

open Langlands.GeneralLinear Langlands.Geometric

universe uF

namespace DiagonalCharacter

open Langlands.Geometric.DiagonalCharacter

variable {F : Type uF} [Field F]

/-- Scaling one row by a unit `s` conjugates the transvection with entry `c`
to the transvection with entry `s * c`. -/
theorem scale_transvection {k : ℕ} (i j : Fin k) (hij : i ≠ j) (s : Fˣ) (c : F) :
    diagonalUnit (fun a => if a = i then s else 1) * transvectionUnit i j hij c =
      transvectionUnit i j hij (s * c) *
        diagonalUnit (fun a => if a = i then s else 1) := by
  apply Units.ext
  change Matrix.diagonal _ * Matrix.transvection i j c =
    Matrix.transvection i j (s * c) * Matrix.diagonal _
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

/-- Every character into complex units kills every transvection, as soon as the
field has an element other than `0` and `1`. -/
theorem character_transvection (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1) {k : ℕ}
    (χ : GeneralLinear k F →* ℂˣ) (i j : Fin k) (hij : i ≠ j) (c : F) :
    χ (transvectionUnit i j hij c) = 1 := by
  obtain ⟨s, hs0, hs1⟩ := hF
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  let u : Fˣ := Units.mk0 s hs0
  let d := diagonalUnit (fun a => if a = i then u else 1)
  -- conjugation invariance of `χ` gives `χ (t (s b)) = χ (t b)`
  have hconj (b : F) :
      χ (transvectionUnit i j hij (s * b)) = χ (transvectionUnit i j hij b) := by
    have h := congrArg χ (scale_transvection i j hij u b)
    simp only [map_mul] at h
    have h' : χ d * χ (transvectionUnit i j hij b) =
        χ d * χ (transvectionUnit i j hij (s * b)) := by
      rw [mul_comm (χ d) (χ (transvectionUnit i j hij (s * b)))]
      exact h
    exact (mul_left_cancel h').symm
  -- additivity of transvections in the entry
  have hadd (a b : F) : transvectionUnit i j hij (a + b) =
      transvectionUnit i j hij a * transvectionUnit i j hij b := by
    apply Units.ext
    change Matrix.transvection i j (a + b) =
      Matrix.transvection i j a * Matrix.transvection i j b
    rw [Matrix.transvection_mul_transvection_same _ _ hij]
  let b := c / (s - 1)
  have hsb : s * b = b + c := by
    simp only [b]
    field_simp
    ring
  have h := hconj b
  rw [hsb, hadd, map_mul] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- In every rank, a character of GL trivial on all unit diagonals is trivial. -/
theorem character_GL (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1) {k : ℕ}
    (χ : GeneralLinear k F →* ℂˣ)
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
    exact character_transvection hF χ _ _ _ _
  · intro A B hA hB PA PB h hh
    let a := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
    let b := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
    have he : h = a * b := Units.ext hh
    rw [he, map_mul, PA a rfl, PB b rfl, one_mul]

/-- Simultaneous unit diagonals determine characters of a finite product of GLs. -/
theorem character_pi_GL (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) (χ : (∀ i, GeneralLinear (d i) F) →* ℂˣ)
    (hdiag : ∀ t : ∀ i, Fin (d i) → Fˣ,
      χ (fun i => diagonalUnit (t i)) = 1) :
    ∀ g, χ g = 1 := by
  apply character_pi χ
  intro i g
  apply character_GL hF
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

/-- A nonarchimedean local field has an element other than `0` and `1`. -/
theorem exists_ne_zero_ne_one (F : Type uF) [Field F] [ValuativeRel F]
    [ValuativeRel.IsNontrivial F] : ∃ s : F, s ≠ 0 ∧ s ≠ 1 := by
  obtain ⟨s, h0, h1⟩ :=
    Valuation.IsNontrivial.exists_val_nontrivial (v := ValuativeRel.valuation F)
  exact ⟨s, fun h => h0 (by simp [h]), fun h => h1 (by simp [h])⟩

/-- Character determination on the actual intersection Levi: the statement
`Langlands.Geometric.IntersectionLeviDiagonalCharacterStatement` with its
`CharZero F` hypothesis replaced by the existence of an element of `F` other
than `0` and `1`.  A complex-valued character of the actual intersection Levi
that is trivial on every actual diagonal matrix is trivial. -/
theorem intersectionLeviDiagonalCharacter (F : Type uF) [Field F]
    (hF : ∃ s : F, s ≠ 0 ∧ s ≠ 1) (n : ℕ)
    (B C : GeneralLinear.BlockShape n) (w : MinimalRepresentatives B C) :
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
    apply DiagonalCharacter.character_pi_GL hF (S i).size φ ?_ g
    intro t
    let T := Pi.mulSingle
      (M := fun k => ∀ j : Fin (S k).length, Fin ((S k).size j) → Fˣ) i t
    have he : Pi.mulSingle i (fun j =>
        Langlands.Geometric.DiagonalCharacter.diagonalUnit (t j)) =
        fun k j => Langlands.Geometric.DiagonalCharacter.diagonalUnit (T k j) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [T]
      · funext j
        simp [T, Pi.mulSingle_eq_of_ne hk,
          Langlands.Geometric.DiagonalCharacter.diagonalUnit_one]
    change ψ (Pi.mulSingle i (fun j =>
      Langlands.Geometric.DiagonalCharacter.diagonalUnit (t j))) = 1
    rw [he]
    exact hd T
  have h := hp (e.symm m)
  change χ (e (e.symm m)) = 1 at h
  rw [e.apply_symm_apply] at h
  exact h

end Langlands.AllField.Geometric
