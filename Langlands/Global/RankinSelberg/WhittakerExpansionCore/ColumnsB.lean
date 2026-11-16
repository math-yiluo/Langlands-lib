import Langlands.Automorphic.CuspidalWhittaker.WhittakerCoefficient

/-! # Column coefficients at the character `y ↦ ψ₀(b y_c)`

The library column framework (`Automorphic.CuspidalWhittaker.Columns`) takes the column Fourier
coefficient at the character `y ↦ ψ₀(y_c)`. Here the same coefficient is taken at
`y ↦ ψ₀(b y_c)` for a fixed `b ∈ K`, which is what a general standard character
`ψ = ψ₀(b ·)` needs. The continuity, mirabolic invariance and block vanishing steps carry over
unchanged. The nonvanishing step is restated with weaker hypotheses: continuity and periodicity
along the column, invariance under rational block matrices, and vanishing of the zeroth column
Fourier coefficient in place of block vanishing. -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open MeasureTheory Matrix
open scoped ComplexConjugate
set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)] {r : ℕ}

/-- The Fourier coefficient along column `c + 1` at the character `y ↦ ψ₀(b y_c)`. -/
def colCoeffB {c : ℕ} (h : c < r) (b : K) (F : AdelicGL K (r + 1) → ℂ) (g : AdelicGL K (r + 1)) :
    ℂ :=
  fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) (Pi.single (charIdx c h) b)

theorem continuous_colCoeffB {c : ℕ} (h : c < r) (b : K) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) : Continuous (colCoeffB h b F) := by
  change Continuous fun g => torusIntegral (Fin (r + 1)) (fun y => F (colUnit (colIdx c h) y * g) *
    conj (pairingCharacter (Pi.single (charIdx c h) b) y))
  refine continuous_torusIntegral (F := fun g y => F (colUnit (colIdx c h) y * g) *
    conj (pairingCharacter (Pi.single (charIdx c h) b) y)) ?_ ?_
  · exact (continuous_col h hFc).mul (Complex.continuous_conj.comp
      ((continuous_pairingCharacter _).comp continuous_snd))
  · intro g
    exact (isPeriodic_col h hFi g).mul (isPeriodic_conj_pairingCharacter _)

/-- The coefficient of a difference, for functions continuous and periodic along the column. -/
theorem colCoeffB_sub {c : ℕ} (h : c < r) (b : K) {F₁ F₂ : AdelicGL K (r + 1) → ℂ}
    (h₁c : ∀ g, Continuous (fun y : Fin (r + 1) → Adeles K => F₁ (colUnit (colIdx c h) y * g)))
    (h₁p : ∀ g, IsPeriodic (fun y : Fin (r + 1) → Adeles K => F₁ (colUnit (colIdx c h) y * g)))
    (h₂c : ∀ g, Continuous (fun y : Fin (r + 1) → Adeles K => F₂ (colUnit (colIdx c h) y * g)))
    (h₂p : ∀ g, IsPeriodic (fun y : Fin (r + 1) → Adeles K => F₂ (colUnit (colIdx c h) y * g)))
    (g : AdelicGL K (r + 1)) :
    colCoeffB h b (fun x => F₁ x - F₂ x) g = colCoeffB h b F₁ g - colCoeffB h b F₂ g := by
  unfold colCoeffB fourierCoeff
  simp only [sub_mul]
  have hχ := isPeriodic_conj_pairingCharacter (K := K) (Pi.single (charIdx c h) b)
  have hχc := continuous_conj_pairingCharacter (K := K) (Pi.single (charIdx c h) b)
  exact torusIntegral_sub ((h₁p g).mul hχ) ((h₁c g).mul hχc) ((h₂p g).mul hχ) ((h₂c g).mul hχc)

/-- **Invariance step** at the character `ψ₀(b y_c)`. -/
theorem mirInvariant_colCoeffB {c : ℕ} (h : c < r) (b : K) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) : MirInvariant c (colCoeffB h b F) := by
  intro γ hγ g
  set γA := AdelicGL.rational K (r + 1) γ
  have hblk : IsBlk ((colIdx c h : ℕ)) γA.val := by
    rw [colIdx_val, rational_val]
    exact hγ.isBlk_succ.map _
  have hconj : ∀ y, F (colUnit (colIdx c h) y * (γA * g)) =
      F (colUnit (colIdx c h) (ratMulVec (γ⁻¹).val y) * g) := by
    intro y
    rw [← mul_assoc, colUnit_mul_of_isBlk _ _ hblk, mul_assoc, rational_inv_val]
    exact hFi γ (hγ.mono (Nat.le_succ c)) _
  unfold colCoeffB
  simp_rw [hconj]
  have hrow : Matrix.vecMul (Pi.single (charIdx c h) b) γ.val = Pi.single (charIdx c h) b := by
    funext j
    rw [Matrix.single_vecMul, Pi.smul_apply, Matrix.row_apply,
      hγ (charIdx c h) j (Or.inl le_rfl), Matrix.one_apply, Pi.single_apply, smul_eq_mul]
    by_cases hj : j = charIdx c h
    · rw [ite_eq_left hj.symm, ite_eq_left hj, mul_one]
    · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj, mul_zero]
  have := fourierCoeff_ratMulVec (f := fun w => F (colUnit (colIdx c h)
      (ratMulVec (γ⁻¹).val w) * g)) ?_ ?_ γ (Pi.single (charIdx c h) b)
  · rw [hrow] at this
    rw [← this]
    congr 1
    funext w
    rw [ratMulVec_ratMulVec, Units.inv_mul, ratMulVec_one]
  · exact (isPeriodic_col h hFi g).comp (preservesRational_ratMulVec _)
  · exact (continuous_col_apply h hFc g).comp (continuous_ratMulVec _)

/-- **Cuspidality step** at the character `ψ₀(b y_c)`: block vanishing descends to the column
coefficient. -/
theorem blockVanishing_colCoeffB {c : ℕ} (h : c < r) (b : K) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) (hFb : BlockVanishing (c + 1) F) :
    BlockVanishing c (colCoeffB h b F) := by
  intro m hm1 hmc g0
  have hcol : ((colIdx c h : Fin (r + 1)) : ℕ) = c + 1 := colIdx_val c h
  set col := colIdx c h with hcol_def
  set e : Fin (r + 1) → K := Pi.single (charIdx c h) b with he
  set χ : (Fin (r + 1) → Adeles K) → ℂ := fun y => conj (pairingCharacter e y) with hχ
  set Q : (Fin (r + 1) → Adeles K) → (Fin (r + 1) → Adeles K) := fun y => y - truncVec m y
    with hQ
  set Ψ : (Fin (r + 1) × Fin (r + 1) → Adeles K) → (Fin (r + 1) → Adeles K) → ℂ :=
    fun X y => torusIntegral (Fin (r + 1))
      (fun z => F (blkUnit m (c + 1) (updateCol X col z) * (colUnit col (Q y) * g0))) with hΨ
  have hχP : ∀ y z, χ (y + truncVec m z) = χ y := by
    intro y z
    simp only [hχ]
    rw [pairingCharacter_add_right, he, pairingCharacter_single (charIdx c h) b (truncVec m z)]
    have : truncVec m z (charIdx c h) = 0 :=
      ite_eq_right (show ¬(((charIdx c h : Fin (r + 1)) : ℕ) < m) by rw [charIdx_val]; omega)
    rw [this, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  have hχper : IsPeriodic χ := isPeriodic_conj_pairingCharacter e
  have hχc : Continuous χ := continuous_conj_pairingCharacter e
  -- Step A: the column coefficient of a block translate.
  have hA : ∀ X, colCoeffB h b F (blkUnit m c X * g0) =
      torusIntegral (Fin (r + 1)) (fun y => χ y * Ψ X y) := by
    intro X
    unfold colCoeffB fourierCoeff
    set Φ : (Fin (r + 1) → Adeles K) → ℂ :=
      fun y => F (colUnit col y * (blkUnit m c X * g0)) * χ y with hΦ
    have hΦper : IsPeriodic Φ := (isPeriodic_col h hFi _).mul hχper
    have hΦc : Continuous Φ :=
      (continuous_col_apply h hFc _).mul hχc
    change torusIntegral _ Φ = _
    have h1 : torusIntegral (Fin (r + 1)) Φ = torusIntegral (Fin (r + 1))
        (fun z => torusIntegral (Fin (r + 1)) (fun y => Φ (y + truncVec m z))) := by
      symm
      calc torusIntegral (Fin (r + 1))
            (fun z => torusIntegral (Fin (r + 1)) (fun y => Φ (y + truncVec m z)))
          = torusIntegral (Fin (r + 1)) (fun _ => torusIntegral (Fin (r + 1)) Φ) :=
            torusIntegral_congr fun z => torusIntegral_add_right hΦper _
        _ = torusIntegral (Fin (r + 1)) Φ := torusIntegral_const _
    have h2 : torusIntegral (Fin (r + 1))
          (fun z => torusIntegral (Fin (r + 1)) (fun y => Φ (y + truncVec m z))) =
        torusIntegral (Fin (r + 1))
          (fun y => torusIntegral (Fin (r + 1)) (fun z => Φ (y + truncVec m z))) := by
      refine torusIntegral_comm (F := fun z y => Φ (y + truncVec m z)) ?_ ?_
      · exact hΦc.comp (continuous_snd.add ((continuous_truncVec m).comp continuous_fst))
      · intro z y k l
        have e1 : y + ratVec l + truncVec m (z + ratVec k) =
            y + truncVec m z + ratVec (l + truncVec m k) := by
          funext i
          simp only [truncVec, Pi.add_apply, ratVec_apply, map_add]
          split_ifs <;> (try simp only [map_zero, add_zero]) <;> abel
        rw [e1, hΦper]
    have h3 : ∀ y, torusIntegral (Fin (r + 1)) (fun z => Φ (y + truncVec m z)) = χ y * Ψ X y := by
      intro y
      set w := truncVec m y - blkMat m c X *ᵥ Q y with hw
      have hmat : ∀ z, colUnit col (y + truncVec m z) * (blkUnit m c X * g0) =
          colUnit col (truncVec m (z + w)) * blkUnit m c X * (colUnit col (Q y) * g0) := by
        intro z
        have hP : truncVec m (y + truncVec m z) = truncVec m y + truncVec m z := by
          rw [truncVec_add, truncVec_truncVec]
        have hQy : y + truncVec m z - truncVec m (y + truncVec m z) = Q y := by
          rw [hP]
          show y + truncVec m z - (truncVec m y + truncVec m z) = y - truncVec m y
          abel
        have hv : truncVec m (y + truncVec m z) -
            blkMat m c X *ᵥ (y + truncVec m z - truncVec m (y + truncVec m z)) =
            truncVec m (z + w) := by
          rw [hQy, hP, hw, truncVec_add, truncVec_sub, truncVec_truncVec, truncVec_blkMat_mulVec]
          abel
        rw [← mul_assoc, colUnit_mul_blkUnit_split col hmc hcol, hv, hQy, mul_assoc]
      set G : (Fin (r + 1) → Adeles K) → ℂ :=
        fun z => F (colUnit col (truncVec m z) * blkUnit m c X * (colUnit col (Q y) * g0)) with hG
      have hGper : IsPeriodic G := by
        intro z k
        simp only [hG]
        rw [truncVec_add, show truncVec m (ratVec k) = ratVec (truncVec m k) by
          funext i; simp only [truncVec, ratVec_apply]; split_ifs <;> simp,
          show truncVec m z + ratVec (truncVec m k) = ratVec (truncVec m k) + truncVec m z from
            add_comm _ _, ← colUnit_mul, mul_assoc, mul_assoc, mul_assoc]
        rw [hFi.colUnit col hcol.le _ _]
      have hGeq : ∀ z, G z =
          F (blkUnit m (c + 1) (updateCol X col z) * (colUnit col (Q y) * g0)) := by
        intro z
        simp only [hG]
        rw [colUnit_truncVec_mul_blkUnit col hmc hcol]
      calc torusIntegral (Fin (r + 1)) (fun z => Φ (y + truncVec m z))
          = torusIntegral (Fin (r + 1)) (fun z => G (z + w) * χ y) := by
            refine torusIntegral_congr fun z => ?_
            simp only [hΦ, hG]
            rw [hχP, hmat]
        _ = torusIntegral (Fin (r + 1)) G * χ y := by
            rw [torusIntegral_mul_const, torusIntegral_add_right hGper]
        _ = χ y * Ψ X y := by
            rw [mul_comm, hΨ]
            congr 1
            exact torusIntegral_congr hGeq
    rw [h1, h2]
    exact torusIntegral_congr h3
  -- Step B: Fubini in `(X, y)`.
  have hΨc : Continuous (Function.uncurry Ψ) := by
    refine continuous_torusIntegral
      (F := fun (p : (Fin (r + 1) × Fin (r + 1) → Adeles K) × (Fin (r + 1) → Adeles K)) z =>
        F (blkUnit m (c + 1) (updateCol p.1 col z) * (colUnit col (Q p.2) * g0))) ?_ ?_
    · refine hFc.comp (((continuous_blkUnit m (c + 1)).comp ((continuous_updateCol col).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).mul
        (((continuous_colUnit col).comp ?_).mul continuous_const))
      exact (continuous_snd.comp continuous_fst).sub
        ((continuous_truncVec m).comp (continuous_snd.comp continuous_fst))
    · intro p
      exact isPeriodic_blk_updateCol hFi (by omega) col p.1 _
  have hΨX : ∀ X y k, Ψ (X + ratVec k) y = Ψ X y := by
    intro X y k
    simp only [hΨ]
    refine torusIntegral_congr fun z => ?_
    have e1 : updateCol (X + ratVec k) col z =
        ratVec (updateCol k col 0) + updateCol X col z := by
      funext q
      simp only [updateCol, Pi.add_apply, ratVec_apply, Pi.zero_apply]
      split_ifs <;> simp [add_comm]
    rw [e1, ← blkUnit_mul, mul_assoc]
    exact hFi.blkUnit (by omega) le_rfl _ _
  have hΨy : ∀ X y l, Ψ X (y + ratVec l) = Ψ X y := by
    intro X y l
    set q : Fin (r + 1) → K := l - truncVec m l with hq
    have eQ : Q (y + ratVec l) = ratVec q + Q y := by
      funext i
      simp only [hQ, hq, truncVec, Pi.add_apply, Pi.sub_apply, ratVec_apply]
      split_ifs
      · rw [sub_self, sub_self, sub_self, map_zero, add_zero]
      · rw [sub_zero, sub_zero, sub_zero, add_comm]
    simp only [hΨ]
    rw [eQ]
    have hper := isPeriodic_blk_updateCol hFi (by omega : m ≤ c + 1) col X
      (colUnit col (Q y) * g0)
    rw [← torusIntegral_add_right hper (blkMat m c X *ᵥ ratVec q)]
    refine torusIntegral_congr fun z => ?_
    rw [← colUnit_mul, mul_assoc (colUnit col (ratVec q)),
      ← mul_assoc (blkUnit m (c + 1) (updateCol X col z)),
      blkUnit_updateCol_mul_colUnit col hmc hcol, mul_assoc, hFi.colUnit col hcol.le _ _]
  have hB : torusIntegral (Fin (r + 1) × Fin (r + 1))
        (fun X => torusIntegral (Fin (r + 1)) (fun y => χ y * Ψ X y)) =
      torusIntegral (Fin (r + 1))
        (fun y => torusIntegral (Fin (r + 1) × Fin (r + 1)) (fun X => χ y * Ψ X y)) := by
    refine torusIntegral_comm (F := fun X y => χ y * Ψ X y) ?_ ?_
    · exact (hχc.comp continuous_snd).mul hΨc
    · intro X y k l
      rw [hχper, hΨX, hΨy]
  -- Step C: the inner integral vanishes by block vanishing at level `c + 1`.
  have hC : ∀ y, torusIntegral (Fin (r + 1) × Fin (r + 1)) (fun X => χ y * Ψ X y) = 0 := by
    intro y
    rw [torusIntegral_const_mul]
    simp only [hΨ]
    rw [torusIntegral_updateCol (G := fun X => F (blkUnit m (c + 1) X * (colUnit col (Q y) * g0)))
      (isPeriodic_blk hFi (by omega) le_rfl _)
      (hFc.comp ((continuous_blkUnit m (c + 1)).mul continuous_const)),
      hFb m hm1 (by omega) _, mul_zero]
  simp_rw [hA]
  rw [hB]
  simp_rw [hC]
  exact torusIntegral_const 0

/-- The three properties carried at level `c`: continuity, `Mir(c)`-invariance and block
vanishing. -/
structure LevelPropsB (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) : Prop where
  continuous : Continuous F
  invariant : MirInvariant c F
  vanishing : BlockVanishing c F

theorem LevelPropsB.step {c : ℕ} (h : c < r) (b : K) {F : AdelicGL K (r + 1) → ℂ}
    (hF : LevelPropsB (c + 1) F) : LevelPropsB c (colCoeffB h b F) :=
  ⟨continuous_colCoeffB h b hF.continuous hF.invariant,
    mirInvariant_colCoeffB h b hF.continuous hF.invariant,
    blockVanishing_colCoeffB h b hF.continuous hF.invariant hF.vanishing⟩

theorem LevelProps.levelPropsB {c : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hF : LevelProps c F) :
    LevelPropsB c F :=
  ⟨hF.continuous, hF.invariant, hF.vanishing⟩

/-- The trivial column character: block vanishing at level `c + 1` kills the zeroth Fourier
coefficient along column `c + 1`. -/
theorem fourierCoeff_zero_of_blockVanishing {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) (hFb : BlockVanishing (c + 1) F)
    (g : AdelicGL K (r + 1)) :
    fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) 0 = 0 := by
  have hcol : ((colIdx c h : Fin (r + 1)) : ℕ) = c + 1 := colIdx_val c h
  have hb := hFb (c + 1) (by omega) le_rfl g
  simp_rw [blkUnit_eq_colUnit (colIdx c h) hcol] at hb
  unfold fourierCoeff
  simp only [pairingCharacter_zero, map_one, mul_one]
  exact (torusIntegral_comp (f := fun y => F (colUnit (colIdx c h) y * g))
    (isPeriodic_col h hFi g) (continuous_col_apply h hFc g)
    (preservesRational_colProj (colIdx c h)) (continuous_colProj (colIdx c h))
    (surjective_colProj (colIdx c h))).symm.trans hb

/-- Fourier coefficients along a column under a rational block matrix, assuming only
continuity and periodicity along the column and invariance under rational block matrices. -/
theorem fourierCoeff_col_transform_of {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hfc : ∀ g, Continuous (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)))
    (hper : ∀ g, IsPeriodic (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)))
    (hblk : ∀ β : RationalGL K (r + 1), IsBlk (c + 1) β.val →
      ∀ g, F (AdelicGL.rational K (r + 1) β * g) = F g)
    (β : RationalGL K (r + 1)) (hβ : IsBlk (c + 1) β.val) (g : AdelicGL K (r + 1))
    (a : Fin (r + 1) → K) :
    fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a =
      fourierCoeff (fun y => F (colUnit (colIdx c h) y * (AdelicGL.rational K (r + 1) β⁻¹ * g)))
        (Matrix.vecMul a β.val) := by
  have hblk' : IsBlk (((colIdx c h : Fin (r + 1)) : ℕ))
      (AdelicGL.rational K (r + 1) β).val := by
    rw [colIdx_val, rational_val]
    exact hβ.map _
  have hconj : ∀ y : Fin (r + 1) → Adeles K, F (colUnit (colIdx c h) y * g) =
      F (colUnit (colIdx c h) (ratMulVec (β⁻¹).val y) *
        (AdelicGL.rational K (r + 1) β⁻¹ * g)) := by
    intro y
    have e1 : AdelicGL.rational K (r + 1) β * colUnit (colIdx c h) (ratMulVec (β⁻¹).val y) =
        colUnit (colIdx c h) y * AdelicGL.rational K (r + 1) β := by
      rw [colUnit_mul_of_isBlk _ _ hblk', rational_inv_val, ratMulVec_apply]
    have e : colUnit (colIdx c h) y * g = AdelicGL.rational K (r + 1) β *
        (colUnit (colIdx c h) (ratMulVec (β⁻¹).val y) *
          (AdelicGL.rational K (r + 1) β⁻¹ * g)) := by
      rw [← mul_assoc, e1, mul_assoc, ← mul_assoc (AdelicGL.rational K (r + 1) β),
        ← map_mul (AdelicGL.rational K (r + 1)) β β⁻¹, mul_inv_cancel, map_one, one_mul]
    rw [e]
    exact hblk β hβ _
  have hrw : (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)) =
      fun y : Fin (r + 1) → Adeles K =>
        (fun w : Fin (r + 1) → Adeles K =>
          F (colUnit (colIdx c h) w * (AdelicGL.rational K (r + 1) β⁻¹ * g)))
        (ratMulVec (β⁻¹).val y) := funext hconj
  rw [hrw]
  have hvec : a = Matrix.vecMul (Matrix.vecMul a β.val) (β⁻¹).val := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  conv_lhs => rw [hvec]
  exact fourierCoeff_ratMulVec (hper (AdelicGL.rational K (r + 1) β⁻¹ * g))
    (hfc (AdelicGL.rational K (r + 1) β⁻¹ * g)) β⁻¹ (Matrix.vecMul a β.val)

/-- **Nonvanishing step** at the character `ψ₀(b y_c)`, `b ≠ 0`: let `F` be continuous and
periodic along column `c + 1`, invariant under rational block matrices of size `c + 1`, with
vanishing zeroth Fourier coefficient along column `c + 1`. If its column coefficient at
`ψ₀(b y_c)` vanishes identically, then `F = 0`. -/
theorem eq_zero_of_colCoeffB_eq_zero {c : ℕ} (h : c < r) {b : K} (hb : b ≠ 0)
    {F : AdelicGL K (r + 1) → ℂ}
    (hfc : ∀ g, Continuous (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)))
    (hper : ∀ g, IsPeriodic (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)))
    (hblk : ∀ β : RationalGL K (r + 1), IsBlk (c + 1) β.val →
      ∀ g, F (AdelicGL.rational K (r + 1) β * g) = F g)
    (h00 : ∀ g, fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) 0 = 0)
    (h0 : ∀ g, colCoeffB h b F g = 0) (g : AdelicGL K (r + 1)) : F g = 0 := by
  have hcol : ((colIdx c h : Fin (r + 1)) : ℕ) = c + 1 := colIdx_val c h
  -- Characters supported in rows `≤ c` with nonzero last entry.
  have caseB : ∀ (g : AdelicGL K (r + 1)) (a : Fin (r + 1) → K),
      (∀ i : Fin (r + 1), c + 1 ≤ (i : ℕ) → a i = 0) →
      a (charIdx c h) ≠ 0 → fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a = 0 := by
    intro g a hsupp hac
    set δM : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
      Matrix.updateRow 1 (charIdx c h) (b⁻¹ • a) with hδM
    have hlow : δM.IsLowerTriangular := by
      intro i j hij
      change i < j at hij
      rw [hδM, Matrix.updateRow_apply]
      split_ifs with hi
      · subst hi
        rw [Pi.smul_apply, hsupp j (by rw [Fin.lt_def, charIdx_val] at hij; omega), smul_zero]
      · exact Matrix.one_apply_ne (ne_of_lt hij)
    have hdet : δM.det ≠ 0 := by
      rw [Matrix.det_of_isLowerTriangular δM hlow, Finset.prod_eq_single (charIdx c h)]
      · rw [hδM, Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul]
        exact mul_ne_zero (inv_ne_zero hb) hac
      · intro i _ hi
        rw [hδM, Matrix.updateRow_ne hi, Matrix.one_apply_eq]
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    set δ : RationalGL K (r + 1) := Matrix.GeneralLinearGroup.mkOfDetNeZero δM hdet with hδ
    have hδblk : IsBlk (c + 1) δ.val := by
      intro i j hij
      change δM i j = _
      rw [hδM, Matrix.updateRow_apply]
      split_ifs with hi
      · subst hi
        rw [charIdx_val] at hij
        rcases hij with hij | hij
        · omega
        · rw [Pi.smul_apply, hsupp j hij, smul_zero, Matrix.one_apply_ne]
          intro e
          rw [← e, charIdx_val] at hij
          omega
      · rfl
    rw [fourierCoeff_col_transform_of h hfc hper hblk δ⁻¹ hδblk.inv g a]
    have hvec : Matrix.vecMul a (δ⁻¹).val = Pi.single (charIdx c h) b := by
      have ha : a = Matrix.vecMul (Pi.single (charIdx c h) b) δ.val := by
        rw [Matrix.single_vecMul]
        funext j
        change a j = b • δM (charIdx c h) j
        rw [hδM, Matrix.updateRow_self, Pi.smul_apply, smul_smul, mul_inv_cancel₀ hb, one_smul]
      rw [ha, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    rw [hvec, inv_inv]
    exact h0 _
  have hall : ∀ (g : AdelicGL K (r + 1)) (a : Fin (r + 1) → K),
      fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a = 0 := by
    intro g a
    by_cases hbig : ∃ i : Fin (r + 1), c + 1 ≤ (i : ℕ) ∧ a i ≠ 0
    · obtain ⟨i, hi, hai⟩ := hbig
      obtain ⟨x0, hx0⟩ := exists_adelicCharacter_ne_one K
      set t : Fin (r + 1) → Adeles K := Pi.single i (algebraMap K (Adeles K) (a i)⁻¹ * x0)
        with ht
      have hft : ∀ y : Fin (r + 1) → Adeles K,
          F (colUnit (colIdx c h) (y + t) * g) = F (colUnit (colIdx c h) y * g) := by
        intro y
        rw [colUnit_congr (colIdx c h) (v := y + t) (w := y) (fun j hj => ?_)]
        have hji : j ≠ i := fun e => by rw [e, hcol] at hj; omega
        rw [Pi.add_apply, ht, Pi.single_eq_of_ne hji, add_zero]
      have hpt : pairingCharacter a t = (adelicCharacter K x0 : ℂ) := by
        unfold pairingCharacter
        congr 2
        rw [Finset.sum_eq_single i]
        · rw [ht, Pi.single_eq_same, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hai, map_one,
            one_mul]
        · intro j _ hj
          rw [ht, Pi.single_eq_of_ne hj, mul_zero]
        · intro hh
          exact absurd (Finset.mem_univ i) hh
      have key := torusIntegral_add_right
        (f := fun y => F (colUnit (colIdx c h) y * g) * conj (pairingCharacter a y))
        ((hper g).mul (isPeriodic_conj_pairingCharacter a)) t
      have hmul : fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a *
          conj (adelicCharacter K x0 : ℂ) =
            fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a := by
        unfold fourierCoeff
        rw [← torusIntegral_mul_const, ← key]
        refine torusIntegral_congr fun y => ?_
        rw [hft, pairingCharacter_add_right, hpt, map_mul, mul_assoc]
      have hne : conj (adelicCharacter K x0 : ℂ) - 1 ≠ 0 := by
        intro h1
        apply hx0
        have h2 : conj (adelicCharacter K x0 : ℂ) = 1 := sub_eq_zero.mp h1
        have h3 : (adelicCharacter K x0 : ℂ) = 1 := by
          rw [← Complex.conj_conj (adelicCharacter K x0 : ℂ), h2, map_one]
        exact Circle.coe_inj.mp (h3.trans Circle.coe_one.symm)
      have h4 : fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a *
          (conj (adelicCharacter K x0 : ℂ) - 1) = 0 := by
        rw [mul_sub, mul_one, hmul, sub_self]
      exact (mul_eq_zero.mp h4).resolve_right hne
    · push Not at hbig
      by_cases hac : a (charIdx c h) ≠ 0
      · exact caseB g a hbig hac
      · push Not at hac
        by_cases ha0 : a = 0
        · subst ha0
          exact h00 g
        · obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
            by_contra! hh
            exact ha0 (funext hh)
          have hkc : (k : ℕ) < c := by
            have h1 : (k : ℕ) < c + 1 := by
              by_contra hh
              exact hk (hbig k (by omega))
            have h2 : k ≠ charIdx c h := fun e => hk (e ▸ hac)
            have h3 : (k : ℕ) ≠ c := fun e => h2 (Fin.ext (by rw [e, charIdx_val]))
            omega
          have hkne : k ≠ charIdx c h := fun e => by rw [e, charIdx_val] at hkc; omega
          set τ : RationalGL K (r + 1) :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection k (charIdx c h) (1 : K))
              (by rw [Matrix.det_transvection_of_ne _ _ hkne]; exact one_ne_zero) with hτ
          have hτblk : IsBlk (c + 1) τ.val := by
            intro i j hij
            change Matrix.transvection k (charIdx c h) (1 : K) i j = _
            rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, ite_eq_right, add_zero]
            rintro ⟨rfl, rfl⟩
            rw [charIdx_val] at hij
            omega
          rw [fourierCoeff_col_transform_of h hfc hper hblk τ hτblk g a]
          refine caseB _ _ (fun i hi => ?_) ?_
          · change Matrix.vecMul a (Matrix.transvection k (charIdx c h) (1 : K)) i = 0
            rw [vecMul_transvection_apply, hbig i hi,
              ite_eq_right (fun e => by rw [e, charIdx_val] at hi; omega), add_zero]
          · change Matrix.vecMul a (Matrix.transvection k (charIdx c h) (1 : K)) (charIdx c h) ≠ 0
            rw [vecMul_transvection_apply, hac, ite_eq_left rfl, zero_add]
            exact hk
  have h1 := eq_zero_of_fourierCoeff_eq_zero (hper g) (hfc g) (hall g) 0
  simpa only [colUnit_zero, one_mul] using h1

end Langlands.Automorphic.CuspidalWhittaker
