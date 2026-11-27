import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpen

/-! # The Levi Whittaker coefficient on the open cell

The block Weyl element `w` conjugates the block diagonal matrix `diag(A, B)` of the exchanged
blocks `(t + 1, r + 1)` to `diag(B, A) = leviPair B A`, and the generic character of `diag(A, B)` is
the product of the generic characters of `A` and `B`. The module also shows that `leviPair` is
multiplicative and maps rational pairs into `P(F)`. These identities turn the open-cell integrand
into the integrand of the Levi Whittaker coefficient `leviWhittaker`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Matrix Set

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon PrimitiveAdelicHeight LeftCosetSpace

section LeviBlocks

variable (r t : ℕ)

/-- The coordinates of the blocks `(r + 1, t + 1)` of `Fin (r + t + 2)`. -/
def leviBlocks : Fin (r + 1) ⊕ Fin (t + 1) ≃ Fin (r + t + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem leviBlocks_inl_val (i : Fin (r + 1)) : (leviBlocks r t (Sum.inl i) : ℕ) = i := by
  simp [leviBlocks]

theorem leviBlocks_inr_val (i : Fin (t + 1)) : (leviBlocks r t (Sum.inr i) : ℕ) = r + 1 + i := by
  simp [leviBlocks]

theorem openCellPermutation_swapBlocks (u : Fin (t + 1) ⊕ Fin (r + 1)) :
    openCellPermutation r t (swapBlocks r t u) = leviBlocks r t u.swap := by
  apply Fin.ext
  rw [openCellPermutation_val]
  rcases u with j | j
  · rw [swapBlocks_inl_val, ite_eq_left j.2, Sum.swap_inl, leviBlocks_inr_val]
  · rw [swapBlocks_inr_val, ite_eq_right (by omega), Sum.swap_inr, leviBlocks_inl_val]
    omega

theorem openCellPermutation_symm_leviBlocks (s : Fin (r + 1) ⊕ Fin (t + 1)) :
    (openCellPermutation r t)⁻¹ (leviBlocks r t s) = swapBlocks r t s.swap := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, openCellPermutation_swapBlocks, Sum.swap_swap]

end LeviBlocks

section LeviEmbedding

variable {R : Type*} [CommRing R] (r t : ℕ)

/-- The Levi embedding of the two-block parabolic in block coordinates. -/
theorem blockShape_leviEmbedding_apply (x : Langlands.GeneralLinear (r + 1) R)
    (y : Langlands.GeneralLinear (t + 1) R) (s s' : Fin (r + 1) ⊕ Fin (t + 1)) :
    ((blockShape r t).leviEmbedding R
        ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) R).symm (x, y)) :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) R) (leviBlocks r t s) (leviBlocks r t s') =
      fromBlocks (x : Matrix (Fin (r + 1)) (Fin (r + 1)) R) 0 0
        (y : Matrix (Fin (t + 1)) (Fin (t + 1)) R) s s' := by
  let i0 : Fin (blockShape r t).length := ⟨0, by change 0 < 2; omega⟩
  let i1 : Fin (blockShape r t).length := ⟨1, by change 1 < 2; omega⟩
  have h0 : ∀ a : Fin (r + 1), leviBlocks r t (Sum.inl a) =
      (blockShape r t).index i0 a := fun a => Fin.ext (by
    rw [blockShape_index_val, leviBlocks_inl_val]
    simp [i0])
  have h1 : ∀ a : Fin (t + 1), leviBlocks r t (Sum.inr a) =
      (blockShape r t).index i1 a := fun a => Fin.ext (by
    rw [blockShape_index_val, leviBlocks_inr_val]
    simp [i1])
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  rcases s with a | a <;> rcases s' with b | b
  · rw [h0, h0]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_same _ _ _ _ _ _
  · rw [h0, h1]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hne
  · rw [h1, h0]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hne.symm
  · rw [h1, h1]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_same _ _ _ _ _ _

end LeviEmbedding

section LeviPair

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

theorem leviPair_apply (x : AdelicGL F (r + 1)) (y : AdelicGL F (t + 1))
    (s s' : Fin (r + 1) ⊕ Fin (t + 1)) :
    (leviPair F r t x y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
      (leviBlocks r t s) (leviBlocks r t s') =
      fromBlocks (x : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) 0 0
        (y : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) s s' := by
  let i0 : Fin (blockShape r t).length := ⟨0, by change 0 < 2; omega⟩
  let i1 : Fin (blockShape r t).length := ⟨1, by change 1 < 2; omega⟩
  have h0 : ∀ a : Fin (r + 1), leviBlocks r t (Sum.inl a) =
      (blockShape r t).index i0 a := fun a => Fin.ext (by
    rw [blockShape_index_val, leviBlocks_inl_val]
    simp [i0])
  have h1 : ∀ a : Fin (t + 1), leviBlocks r t (Sum.inr a) =
      (blockShape r t).index i1 a := fun a => Fin.ext (by
    rw [blockShape_index_val, leviBlocks_inr_val]
    simp [i1])
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  rcases s with a | a <;> rcases s' with b | b
  · rw [h0, h0]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_same _ _ _ _ _ _
  · rw [h0, h1]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hne
  · rw [h1, h0]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hne.symm
  · rw [h1, h1]
    exact GeneralLinear.BlockShape.leviEmbedding_apply_same _ _ _ _ _ _

/-- **Conjugation of the exchanged Levi by the block Weyl element.** -/
theorem openCellWeyl_mul_leviHom (m : LeviPart F r t) :
    openCellWeyl F r t * toMat F _ (leviHom F r t m) =
      leviPair F r t (toMat F _ m.2) (toMat F _ m.1) * openCellWeyl F r t := by
  suffices h : openCellWeyl F r t * toMat F _ (leviHom F r t m) * (openCellWeyl F r t)⁻¹ =
      leviPair F r t (toMat F _ m.2) (toMat F _ m.1) by
    rw [← h, inv_mul_cancel_right]
  rw [openCellWeyl_eq_permutation]
  apply Units.ext
  ext i j
  obtain ⟨s, rfl⟩ := (leviBlocks r t).surjective i
  obtain ⟨s', rfl⟩ := (leviBlocks r t).surjective j
  rw [GeneralLinear.permutation_conjugate_entry, openCellPermutation_symm_leviBlocks,
    openCellPermutation_symm_leviBlocks, leviPair_apply]
  have hD := toMat_leviHom F r t m
  change toSum (toMat F _ (leviHom F r t m) :
    Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) s.swap s'.swap = _
  rw [hD]
  rcases s with a | a <;> rcases s' with b | b <;> rfl

theorem toMat_leviHom_apply (m : LeviPart F r t) (u v : Fin (t + 1) ⊕ Fin (r + 1)) :
    (toMat F _ (leviHom F r t m) : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
      (swapBlocks r t u) (swapBlocks r t v) =
      fromBlocks (toMat F _ m.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) 0 0
        (toMat F _ m.2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) u v := by
  have hD := toMat_leviHom F r t m
  change toSum (toMat F _ (leviHom F r t m) :
    Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) u v = _
  rw [hD]

/-- The superdiagonal of `diag(A, B)` is that of `A` followed by that of `B`. -/
theorem sum_superdiag_leviHom (m : LeviPart F r t) :
    ∑ i : Fin (r + t + 1), (toMat F _ (leviHom F r t m) :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) i.castSucc i.succ =
      (∑ i : Fin t, (toMat F _ m.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F))
        i.castSucc i.succ) +
      ∑ i : Fin r, (toMat F _ m.2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F))
        i.castSucc i.succ := by
  set D := (toMat F _ (leviHom F r t m) :
    Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
  rw [← (finCongr (by omega : t + (r + 1) = r + t + 1)).sum_comp, Fin.sum_univ_add,
    Fin.sum_univ_succ]
  have hA : ∀ i : Fin t, D ((finCongr (by omega : t + (r + 1) = r + t + 1))
      (Fin.castAdd (r + 1) i)).castSucc ((finCongr (by omega : t + (r + 1) = r + t + 1))
      (Fin.castAdd (r + 1) i)).succ =
      (toMat F _ m.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) i.castSucc i.succ := by
    intro i
    have e1 : ((finCongr (by omega : t + (r + 1) = r + t + 1)) (Fin.castAdd (r + 1) i)).castSucc =
        swapBlocks r t (Sum.inl i.castSucc) := Fin.ext (by simp [swapBlocks])
    have e2 : ((finCongr (by omega : t + (r + 1) = r + t + 1)) (Fin.castAdd (r + 1) i)).succ =
        swapBlocks r t (Sum.inl i.succ) := Fin.ext (by simp [swapBlocks])
    rw [e1, e2]
    exact toMat_leviHom_apply F r t m _ _
  have h0 : D ((finCongr (by omega : t + (r + 1) = r + t + 1))
      (Fin.natAdd t (0 : Fin (r + 1)))).castSucc ((finCongr (by omega : t + (r + 1) = r + t + 1))
      (Fin.natAdd t (0 : Fin (r + 1)))).succ = 0 := by
    have e1 : ((finCongr (by omega : t + (r + 1) = r + t + 1)) (Fin.natAdd t (0 : Fin (r + 1)))).castSucc =
        swapBlocks r t (Sum.inl (Fin.last t)) := Fin.ext (by simp [swapBlocks])
    have e2 : ((finCongr (by omega : t + (r + 1) = r + t + 1)) (Fin.natAdd t (0 : Fin (r + 1)))).succ =
        swapBlocks r t (Sum.inr 0) := Fin.ext (by simp [swapBlocks])
    rw [e1, e2]
    exact toMat_leviHom_apply F r t m _ _
  have hB : ∀ i : Fin r, D ((finCongr (by omega : t + (r + 1) = r + t + 1))
      (Fin.natAdd t i.succ)).castSucc ((finCongr (by omega : t + (r + 1) = r + t + 1))
      (Fin.natAdd t i.succ)).succ =
      (toMat F _ m.2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ := by
    intro i
    have e1 : ((finCongr (by omega : t + (r + 1) = r + t + 1)) (Fin.natAdd t i.succ)).castSucc =
        swapBlocks r t (Sum.inr i.castSucc) := Fin.ext (by simp [swapBlocks]; omega)
    have e2 : ((finCongr (by omega : t + (r + 1) = r + t + 1)) (Fin.natAdd t i.succ)).succ =
        swapBlocks r t (Sum.inr i.succ) := Fin.ext (by simp [swapBlocks]; omega)
    rw [e1, e2]
    exact toMat_leviHom_apply F r t m _ _
  simp only [hA, h0, hB, zero_add]

theorem leviPair_mul (x x' : AdelicGL F (r + 1)) (y y' : AdelicGL F (t + 1)) :
    leviPair F r t (x * x') (y * y') = leviPair F r t x y * leviPair F r t x' y' := by
  rw [leviPair, leviPair, leviPair, ← map_mul]
  congr 1
  exact (Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm.map_mul
    (x, y) (x', y')

/-- `diag(γ, δ)` for rational `γ`, `δ` is a rational point of the parabolic. -/
theorem leviPair_rational (a : RationalGL F (r + 1)) (b : RationalGL F (t + 1)) :
    ∃ c0 ∈ (blockShape r t).parabolic F,
      leviPair F r t (AdelicGL.rational F _ a) (AdelicGL.rational F _ b) =
        AdelicGL.rational F _ c0 := by
  refine ⟨(blockShape r t).leviEmbedding F
    ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) F).symm (a, b)),
    ((blockShape r t).leviInParabolic F _).2, ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨s, rfl⟩ := (leviBlocks r t).surjective i
  obtain ⟨s', rfl⟩ := (leviBlocks r t).surjective j
  rw [AdelicGL.rational_apply, leviPair, blockShape_leviEmbedding_apply,
    blockShape_leviEmbedding_apply]
  rcases s with c | c <;> rcases s' with d | d <;> simp

/-- The generic character of `diag(A, B)`. -/
theorem genericChar_leviHom (ψ : AddChar (Adeles F) ℂ) (m : LeviPart F r t) :
    genericChar ψ (leviHom F r t m) =
      genericCharacter F t ψ (fun _ => 1) m.1 * genericCharacter F r ψ (fun _ => 1) m.2 := by
  rw [genericChar, sum_superdiag_leviHom, AddChar.map_add_eq_mul]
  simp only [genericCharacter, map_one, one_mul]
  rfl

/-- The generic character of `u'(Y)`. -/
theorem genericChar_radicalHom (ψ : AddChar (Adeles F) ℂ) (n : Radical F r t) :
    genericChar ψ (radicalHom F r t n) = ψ (n.toAdd (Fin.last t) 0) := by
  rw [genericChar, toMat_radicalHom, openCellUnipotent_superdiagonal_sum]

end LeviPair

end Langlands.Global.CuspidalPairEisenstein.Unfolding
