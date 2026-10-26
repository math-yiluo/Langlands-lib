import Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.RefinementDefinitions
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.Group.Pi.Lemmas

/-! Algebraic determination of characters by literal diagonal matrices. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uF

namespace DiagonalCharacter

variable {F : Type uF} [Field F]

/-- The unit matrix with the prescribed diagonal unit entries. -/
def diagonalUnit {k : ℕ} (t : Fin k → Fˣ) : GeneralLinear k F where
  val := Matrix.diagonal (fun i => (t i : F))
  inv := Matrix.diagonal (fun i => ((t i)⁻¹ : Fˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

@[simp] theorem diagonalUnit_one {k : ℕ} :
    diagonalUnit (1 : Fin k → Fˣ) = 1 := by
  apply Units.ext
  simp [diagonalUnit]

/-- A transvection, including its explicit inverse. -/
def transvectionUnit {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : F) :
    GeneralLinear k F where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

/-- Scaling one row by two conjugates a transvection to its square. -/
theorem scale_transvection [CharZero F] {k : ℕ} (i j : Fin k)
    (hij : i ≠ j) (c : F) :
    let d := diagonalUnit (fun a => if a = i then Units.mk0 (2 : F) (by norm_num) else 1)
    let t := transvectionUnit i j hij c
    d * t = (t * t) * d := by
  dsimp
  apply Units.ext
  change Matrix.diagonal _ * Matrix.transvection i j c =
    (Matrix.transvection i j c * Matrix.transvection i j c) * Matrix.diagonal _
  rw [Matrix.transvection_mul_transvection_same _ _ hij]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      simp [Matrix.transvection, Matrix.single, hij, hij.symm]
      ring
    · by_cases hbi : b = i
      · subst b
        simp [Matrix.transvection, Matrix.single, hij.symm]
      · simp [Matrix.transvection, Matrix.single, Ne.symm hbj, hbi, Ne.symm hbi]
  · by_cases hab : a = b
    · subst b
      simp [Matrix.transvection, Matrix.single, hai, Ne.symm hai]
    · simp [Matrix.transvection, Matrix.single, hai, Ne.symm hai, hab]

/-- Every character into complex units kills every transvection. -/
theorem character_transvection [CharZero F] {k : ℕ}
    (χ : GeneralLinear k F →* ℂˣ) (i j : Fin k) (hij : i ≠ j) (c : F) :
    χ (transvectionUnit i j hij c) = 1 := by
  let d := diagonalUnit (fun a => if a = i then Units.mk0 (2 : F) (by norm_num) else 1)
  let t := transvectionUnit i j hij c
  have h := congrArg χ (scale_transvection i j hij c)
  change χ (d * t) = χ ((t * t) * d) at h
  simp only [map_mul] at h
  have ht : χ t = χ t * χ t := by
    apply mul_right_cancel (b := χ d)
    simpa only [mul_comm (χ d) (χ t)] using h
  exact mul_left_cancel (ht.symm.trans (mul_one (χ t)).symm)

/-- In every rank, a character of GL trivial on all unit diagonals is trivial. -/
theorem character_GL [CharZero F] {k : ℕ} (χ : GeneralLinear k F →* ℂˣ)
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

/-- A homomorphism on a finite dependent product is determined by its factors. -/
theorem character_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, Group (G i)] (χ : (∀ i, G i) →* ℂˣ)
    (h : ∀ i (g : G i), χ (Pi.mulSingle i g) = 1) :
    ∀ g, χ g = 1 := by
  have aux (s : Finset ι) :
      ∀ g : ∀ i, G i, (∀ i, i ∉ s → g i = 1) → χ g = 1 := by
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have he : g = 1 := funext fun i => hg i (by simp)
      rw [he, map_one]
    | @insert i s hi ih =>
      intro g hg
      let g' := Function.update g i 1
      have he : g = Pi.mulSingle i (g i) * g' := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [g']
        · simp [g', hj]
      have hg' : χ g' = 1 := by
        apply ih g'
        intro j hj
        by_cases hji : j = i
        · subst j
          simp [g']
        · simpa [g', hji] using hg j (by simp [hji, hj])
      rw [he, map_mul, h, hg', one_mul]
  exact fun g => aux Finset.univ g (by simp)

/-- Simultaneous unit diagonals determine characters of a finite product of GLs. -/
theorem character_pi_GL [CharZero F] {ι : Type*} [Fintype ι] [DecidableEq ι]
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

/-- The product of coordinate diagonals embeds as the literal ambient diagonal. -/
theorem leviEmbedding_diagonalUnit {n : ℕ} (B : BlockShape n)
    (t : ∀ i, Fin (B.size i) → Fˣ) :
    (B.leviEmbedding F (fun i => diagonalUnit (t i))).val =
      Matrix.diagonal (fun x =>
        (t (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2 : F)) := by
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding F _ (B.index i a) (B.index j b) = _
  by_cases hij : i = j
  · subst j
    rw [B.leviEmbedding_apply_same]
    simp [diagonalUnit, Matrix.diagonal_apply, B.indexEquiv.injective.eq_iff]
    rw [B.indexEquiv.symm_apply_apply]
  · rw [B.leviEmbedding_apply_ne F _ a b hij]
    simp [B.indexEquiv.injective.eq_iff, hij]

/-- The coordinate source Levi is the actual intersection in the embedded Levi. -/
def sourceActualEquiv {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    sourceLevi F B C w ≃*
      General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F)
        (permutation n F w) where
  toFun m := ⟨B.leviEquiv F m.val, m.property⟩
  invFun m := ⟨(B.leviEquiv F).symm m.val, by
    change permutation n F w *
      (B.leviEquiv F ((B.leviEquiv F).symm m.val)).val *
      (permutation n F w)⁻¹ ∈ C.leviSubgroup F
    rw [MulEquiv.apply_symm_apply]
    exact m.property⟩
  left_inv m := Subtype.ext ((B.leviEquiv F).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((B.leviEquiv F).apply_symm_apply m.val)
  map_mul' a b := Subtype.ext ((B.leviEquiv F).map_mul a.val b.val)

end DiagonalCharacter

/-- The exact diagonal-determination statement for the actual intersection Levi. -/
theorem intersectionLeviDiagonalCharacterTheorem :
    IntersectionLeviDiagonalCharacterStatement.{uF} := by
  classical
  intro F _ _ n B C w
  dsimp only
  intro χ hdiag m
  obtain ⟨S, _, hS, _⟩ :=
    exists_standardIntersections F B C w.val w.property.1
  let e := ((refinedLeviEquiv F B S).trans
    (MulEquiv.subgroupCongr hS.symm)).trans
      (DiagonalCharacter.sourceActualEquiv B C w.val)
  let ψ := χ.comp e.toMonoidHom
  have hd (t : ∀ i, ∀ j : Fin (S i).length, Fin ((S i).size j) → Fˣ) :
      ψ (fun i j => DiagonalCharacter.diagonalUnit (t i j)) = 1 := by
    let r : ∀ i, Fin (B.size i) → Fˣ := fun i a =>
      t i ((S i).indexEquiv.symm a).1 ((S i).indexEquiv.symm a).2
    let a : Fin n → Fˣ := fun x =>
      r (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2
    apply hdiag a (e _)
    change (B.leviEmbedding F (fun i =>
      (S i).leviEmbedding F (fun j => DiagonalCharacter.diagonalUnit (t i j)))).val =
        Matrix.diagonal (fun x => (a x : F))
    have he : (fun i =>
        (S i).leviEmbedding F (fun j => DiagonalCharacter.diagonalUnit (t i j))) =
        fun i => DiagonalCharacter.diagonalUnit (r i) := by
      funext i
      apply Units.ext
      exact DiagonalCharacter.leviEmbedding_diagonalUnit (S i) (t i)
    rw [he]
    exact DiagonalCharacter.leviEmbedding_diagonalUnit B r
  have hp : ∀ g, ψ g = 1 := by
    apply DiagonalCharacter.character_pi ψ
    intro i g
    let φ := ψ.comp (MonoidHom.mulSingle (fun i => (S i).Levi F) i)
    apply DiagonalCharacter.character_pi_GL (S i).size φ ?_ g
    intro t
    let T := Pi.mulSingle
      (M := fun k => ∀ j : Fin (S k).length, Fin ((S k).size j) → Fˣ) i t
    have he : Pi.mulSingle i (fun j => DiagonalCharacter.diagonalUnit (t j)) =
        fun k j => DiagonalCharacter.diagonalUnit (T k j) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [T]
      · funext j
        simp [T, Pi.mulSingle_eq_of_ne hk, DiagonalCharacter.diagonalUnit_one]
    change ψ (Pi.mulSingle i (fun j => DiagonalCharacter.diagonalUnit (t j))) = 1
    rw [he]
    exact hd T
  have h := hp (e.symm m)
  change χ (e (e.symm m)) = 1 at h
  rw [e.apply_symm_apply] at h
  exact h

end Langlands.Geometric
