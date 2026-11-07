import Langlands.Automorphic.CuspidalWhittaker.Fourier
import Langlands.Automorphic.CuspidalWhittaker.Unipotent

/-!
# Column Fourier coefficients of automorphic functions

For a function `F` on `GL_{r+1}(𝔸_K)` and `c < r`, the column coefficient is the Fourier
coefficient along the abelian group of column `c + 1` (rows `≤ c`) at the character
`y ↦ ψ(y_c)`:
`colCoeff c F (g) = ∫_{(𝔸_K/K)^{r+1}} F(u_{c+1}(y) g) ψ(y_c)⁻¹ dy`.
Iterating from the top column down gives the global Whittaker coefficient.

At level `c` we track: continuity, left invariance under the rational points of the group
`Mir(c)` (identity in rows `≥ c` and columns `> c`), vanishing of the block integrals over
`i < m ≤ j ≤ c` for `1 ≤ m ≤ c` (from cuspidality), and the transformation law under upper
unipotent matrices whose columns `≤ c` are trivial. Each column step preserves these, and if a
column coefficient vanishes identically then so does the function.
-/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

variable {K : Type u} [Field K] [NumberField K]

/-! ### Rational linear changes of variables -/

section Linear

variable {ι : Type*} [Fintype ι]

/-- Multiplication of adelic vectors by a rational matrix. -/
def ratMulVec (B : Matrix ι ι K) : (ι → Adeles K) →+ (ι → Adeles K) where
  toFun v := (B.map (algebraMap K (Adeles K))) *ᵥ v
  map_zero' := Matrix.mulVec_zero _
  map_add' v w := Matrix.mulVec_add _ v w

theorem ratMulVec_apply (B : Matrix ι ι K) (v : ι → Adeles K) :
    ratMulVec B v = (B.map (algebraMap K (Adeles K))) *ᵥ v := rfl

theorem ratMulVec_ratVec (B : Matrix ι ι K) (k : ι → K) :
    ratMulVec B (ratVec k) = ratVec (B *ᵥ k) := by
  funext i
  simp [ratMulVec_apply, ratVec, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem preservesRational_ratMulVec (B : Matrix ι ι K) :
    PreservesRational (ratMulVec (K := K) B) :=
  fun k => ⟨B *ᵥ k, ratMulVec_ratVec B k⟩

theorem continuous_ratMulVec (B : Matrix ι ι K) : Continuous (ratMulVec (K := K) B) :=
  show Continuous fun v => (B.map (algebraMap K (Adeles K))) *ᵥ v from
    continuous_const.matrix_mulVec continuous_id

theorem ratMulVec_ratMulVec (B C : Matrix ι ι K) (v : ι → Adeles K) :
    ratMulVec B (ratMulVec C v) = ratMulVec (B * C) v := by
  simp only [ratMulVec_apply, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem ratMulVec_one [DecidableEq ι] (v : ι → Adeles K) : ratMulVec (1 : Matrix ι ι K) v = v := by
  simp [ratMulVec_apply]

theorem surjective_ratMulVec [DecidableEq ι] (g : GL ι K) :
    Function.Surjective (ratMulVec (K := K) g.val) := fun v =>
  ⟨ratMulVec (g⁻¹).val v, by rw [ratMulVec_ratMulVec, Units.mul_inv, ratMulVec_one]⟩

theorem pairingCharacter_ratMulVec (a : ι → K) (B : Matrix ι ι K) (w : ι → Adeles K) :
    pairingCharacter a (ratMulVec B w) = pairingCharacter (Matrix.vecMul a B) w := by
  unfold pairingCharacter
  congr 2
  simp only [ratMulVec_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.vecMul,
    Finset.mul_sum, map_sum, map_mul, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

variable [CompactSpace (AdeleQuotient K)]

/-- Fourier coefficients under a rational linear change of variables. -/
theorem fourierCoeff_ratMulVec [DecidableEq ι] {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f)
    (hc : Continuous f) (g : GL ι K) (b : ι → K) :
    fourierCoeff (fun w => f (ratMulVec g.val w)) (Matrix.vecMul b g.val) = fourierCoeff f b := by
  unfold fourierCoeff
  have h := torusIntegral_comp (f := fun y => f y * conj (pairingCharacter b y))
    (hf.mul (fun y k => by rw [isPeriodic_pairingCharacter b y k]))
    (hc.mul (Complex.continuous_conj.comp (continuous_pairingCharacter b)))
    (preservesRational_ratMulVec g.val) (continuous_ratMulVec g.val) (surjective_ratMulVec g)
  rw [← h]
  refine torusIntegral_congr fun w => ?_
  rw [pairingCharacter_ratMulVec]

theorem pairingCharacter_add_right (a : ι → K) (y z : ι → Adeles K) :
    pairingCharacter a (y + z) = pairingCharacter a y * pairingCharacter a z := by
  simp only [pairingCharacter, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    AddChar.map_add_eq_mul, Circle.coe_mul]

theorem pairingCharacter_neg_right (a : ι → K) (y : ι → Adeles K) :
    pairingCharacter a (-y) = conj (pairingCharacter a y) := by
  simp only [pairingCharacter, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem isPeriodic_conj_pairingCharacter (a : ι → K) :
    IsPeriodic (fun y : ι → Adeles K => conj (pairingCharacter a y)) := fun y k => by
  beta_reduce
  rw [isPeriodic_pairingCharacter a y k]

theorem continuous_conj_pairingCharacter (a : ι → K) :
    Continuous (fun y : ι → Adeles K => conj (pairingCharacter a y)) :=
  Complex.continuous_conj.comp (continuous_pairingCharacter a)

end Linear

/-! ### Mirabolic invariance -/

variable [CompactSpace (AdeleQuotient K)] {r : ℕ}

omit [CompactSpace (AdeleQuotient K)] in
theorem rational_colUnit (c : Fin (r + 1)) (k : Fin (r + 1) → K) :
    AdelicGL.rational K (r + 1) (colUnit c k) = colUnit c (ratVec k) :=
  map_colUnit _ c k

omit [CompactSpace (AdeleQuotient K)] in
theorem rational_blkUnit (m c : ℕ) (k : Fin (r + 1) × Fin (r + 1) → K) :
    AdelicGL.rational K (r + 1) (blkUnit m c k) = blkUnit m c (ratVec k) :=
  map_blkUnit _ m c k

omit [CompactSpace (AdeleQuotient K)] in
theorem rational_val (γ : RationalGL K (r + 1)) :
    (AdelicGL.rational K (r + 1) γ).val = γ.val.map (algebraMap K (Adeles K)) := rfl

omit [CompactSpace (AdeleQuotient K)] in
theorem rational_inv_val (γ : RationalGL K (r + 1)) :
    ((AdelicGL.rational K (r + 1) γ)⁻¹).val = (γ⁻¹).val.map (algebraMap K (Adeles K)) := by
  rw [← map_inv]
  rfl

theorem IsMir.mono {R : Type*} [CommRing R] {n c c' : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (h : IsMir c M) (hc : c ≤ c') : IsMir c' M :=
  fun i j hij => h i j (hij.imp (fun h => le_trans hc h) (fun h => lt_of_le_of_lt hc h))

/-- Left invariance under the rational points of `Mir(c)`. -/
def MirInvariant (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) : Prop :=
  ∀ γ : RationalGL K (r + 1), IsMir c γ.val → ∀ g, F (AdelicGL.rational K (r + 1) γ * g) = F g

theorem MirInvariant.mono {c c' : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hF : MirInvariant c' F)
    (hc : c ≤ c') : MirInvariant c F :=
  fun γ hγ g => hF γ (hγ.mono hc) g

theorem MirInvariant.colUnit {c : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hF : MirInvariant c F)
    (col : Fin (r + 1)) (hcol : (col : ℕ) ≤ c) (k : Fin (r + 1) → K) (g : AdelicGL K (r + 1)) :
    F (colUnit col (ratVec k) * g) = F g := by
  rw [← rational_colUnit]
  exact hF _ ((isMir_colUnit col k).mono hcol) g

theorem MirInvariant.blkUnit {c : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hF : MirInvariant c F)
    {m c₀ : ℕ} (hm : m ≤ c) (hc₀ : c₀ ≤ c) (k : Fin (r + 1) × Fin (r + 1) → K)
    (g : AdelicGL K (r + 1)) :
    F (blkUnit m c₀ (ratVec k) * g) = F g := by
  rw [← rational_blkUnit]
  exact hF _ (isMir_blkUnit hm hc₀ k) g

/-! ### The column coefficient -/

/-- The column `c + 1`. -/
def colIdx (c : ℕ) (h : c < r) : Fin (r + 1) := ⟨c + 1, by omega⟩

/-- The row `c`. -/
def charIdx (c : ℕ) (h : c < r) : Fin (r + 1) := ⟨c, by omega⟩

@[simp] theorem colIdx_val (c : ℕ) (h : c < r) : (colIdx c h : ℕ) = c + 1 := rfl
@[simp] theorem charIdx_val (c : ℕ) (h : c < r) : (charIdx c h : ℕ) = c := rfl

/-- The Fourier coefficient along column `c + 1` at the character `y ↦ ψ(y_c)`. -/
def colCoeff (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) (g : AdelicGL K (r + 1)) : ℂ :=
  if h : c < r then
    fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) (Pi.single (charIdx c h) 1)
  else F g

theorem colCoeff_eq {c : ℕ} (h : c < r) (F : AdelicGL K (r + 1) → ℂ) (g : AdelicGL K (r + 1)) :
    colCoeff c F g =
      fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) (Pi.single (charIdx c h) 1) := by
  rw [colCoeff, dite_eq_left h]

theorem isPeriodic_col {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hF : MirInvariant (c + 1) F) (g : AdelicGL K (r + 1)) :
    IsPeriodic (fun y => F (colUnit (colIdx c h) y * g)) := by
  intro y k
  beta_reduce
  rw [show y + ratVec k = ratVec k + y from add_comm _ _, ← colUnit_mul, mul_assoc]
  exact hF.colUnit _ le_rfl k _

theorem continuous_col {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ} (hF : Continuous F) :
    Continuous (fun p : AdelicGL K (r + 1) × (Fin (r + 1) → Adeles K) =>
      F (colUnit (colIdx c h) p.2 * p.1)) :=
  hF.comp (((continuous_colUnit (colIdx c h)).comp continuous_snd).mul continuous_fst)

theorem continuous_col_apply {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ} (hF : Continuous F)
    (x : AdelicGL K (r + 1)) :
    Continuous (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * x)) := by
  have := (continuous_col h hF).comp
    (Continuous.prodMk_right (X := AdelicGL K (r + 1)) (Y := Fin (r + 1) → Adeles K) x)
  exact this

theorem continuous_colCoeff {c : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hFc : Continuous F)
    (hFi : MirInvariant (c + 1) F) : Continuous (colCoeff c F) := by
  by_cases h : c < r
  · have : colCoeff c F = fun g =>
        torusIntegral (Fin (r + 1)) (fun y => F (colUnit (colIdx c h) y * g) *
          conj (pairingCharacter (Pi.single (charIdx c h) 1) y)) :=
      funext fun g => colCoeff_eq h F g
    rw [this]
    refine continuous_torusIntegral (F := fun g y => F (colUnit (colIdx c h) y * g) *
      conj (pairingCharacter (Pi.single (charIdx c h) 1) y)) ?_ ?_
    · exact (continuous_col h hFc).mul (Complex.continuous_conj.comp
        ((continuous_pairingCharacter _).comp continuous_snd))
    · intro g
      exact (isPeriodic_col h hFi g).mul (isPeriodic_conj_pairingCharacter _)
  · have : colCoeff c F = F := funext fun g => by rw [colCoeff, dite_eq_right h]
    rwa [this]

theorem colCoeff_add {c : ℕ} {F₁ F₂ : AdelicGL K (r + 1) → ℂ} (h₁c : Continuous F₁)
    (h₁i : MirInvariant (c + 1) F₁) (h₂c : Continuous F₂) (h₂i : MirInvariant (c + 1) F₂)
    (g : AdelicGL K (r + 1)) :
    colCoeff c (fun x => F₁ x + F₂ x) g = colCoeff c F₁ g + colCoeff c F₂ g := by
  by_cases h : c < r
  · simp only [colCoeff_eq h, fourierCoeff, add_mul]
    have hχ := isPeriodic_conj_pairingCharacter (K := K) (Pi.single (charIdx c h) (1 : K))
    have hχc := continuous_conj_pairingCharacter (K := K) (Pi.single (charIdx c h) (1 : K))
    exact torusIntegral_add ((isPeriodic_col h h₁i g).mul hχ)
      ((continuous_col_apply h h₁c g).mul hχc)
      ((isPeriodic_col h h₂i g).mul hχ)
      ((continuous_col_apply h h₂c g).mul hχc)
  · simp only [colCoeff, dite_eq_right h]

theorem colCoeff_const_mul (c : ℕ) (a : ℂ) (F : AdelicGL K (r + 1) → ℂ) (g : AdelicGL K (r + 1)) :
    colCoeff c (fun x => a * F x) g = a * colCoeff c F g := by
  by_cases h : c < r
  · simp only [colCoeff_eq h, fourierCoeff, mul_assoc]
    exact torusIntegral_const_mul a _
  · simp only [colCoeff, dite_eq_right h]

theorem colCoeff_mul_right (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) (x g : AdelicGL K (r + 1)) :
    colCoeff c (fun g' => F (g' * x)) g = colCoeff c F (g * x) := by
  by_cases h : c < r
  · simp only [colCoeff_eq h, mul_assoc]
  · simp only [colCoeff, dite_eq_right h]

/-- **Invariance step**: the column coefficient of a `Mir(c+1)`-invariant function is
`Mir(c)`-invariant. -/
theorem mirInvariant_colCoeff {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) : MirInvariant c (colCoeff c F) := by
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
  rw [colCoeff_eq h, colCoeff_eq h]
  simp_rw [hconj]
  have hrow : Matrix.vecMul (Pi.single (charIdx c h) (1 : K)) γ.val =
      Pi.single (charIdx c h) 1 := by
    funext j
    rw [Matrix.single_one_vecMul]
    change γ.val (charIdx c h) j = _
    rw [hγ (charIdx c h) j (Or.inl le_rfl), Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]
  have := fourierCoeff_ratMulVec (f := fun w => F (colUnit (colIdx c h)
      (ratMulVec (γ⁻¹).val w) * g)) ?_ ?_ γ (Pi.single (charIdx c h) 1)
  · rw [hrow] at this
    rw [← this]
    congr 1
    funext w
    rw [ratMulVec_ratMulVec, Units.inv_mul, ratMulVec_one]
  · exact (isPeriodic_col h hFi g).comp (preservesRational_ratMulVec _)
  · exact (continuous_col_apply h hFc g).comp
      (continuous_ratMulVec _)

/-! ### Equivariance under upper unipotent matrices -/

/-- The sum of the first-superdiagonal entries in rows `≥ c`. -/
def superSum (c : ℕ) (u : AdelicGL K (r + 1)) : Adeles K :=
  ∑ i : Fin r, if c ≤ (i : ℕ) then u.val i.castSucc i.succ else 0

theorem superSum_congr {c : ℕ} {u v : AdelicGL K (r + 1)}
    (h : ∀ i j : Fin (r + 1), c ≤ (i : ℕ) → u.val i j = v.val i j) :
    superSum c u = superSum c v := by
  unfold superSum
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · exact h _ _ hi
  · rfl

theorem superSum_succ {c : ℕ} (h : c < r) (u : AdelicGL K (r + 1)) :
    superSum c u = superSum (c + 1) u + u.val (charIdx c h) (colIdx c h) := by
  unfold superSum
  have hterm : ∀ i : Fin r, (if c ≤ (i : ℕ) then u.val i.castSucc i.succ else 0) =
      (if c + 1 ≤ (i : ℕ) then u.val i.castSucc i.succ else 0) +
        (if i = ⟨c, h⟩ then u.val i.castSucc i.succ else 0) := by
    intro i
    by_cases h1 : c + 1 ≤ (i : ℕ)
    · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_right (fun e => by subst e; simp at h1),
        add_zero]
    · by_cases h2 : (i : ℕ) = c
      · have hi : i = ⟨c, h⟩ := Fin.ext h2
        subst hi
        rw [ite_eq_left le_rfl, ite_eq_right h1, ite_eq_left rfl, zero_add]
      · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right (fun e => h2 (by rw [e])),
          add_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rfl

/-- The transformation law under upper unitriangular matrices with trivial columns `≤ c`. -/
def Equivariant (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) : Prop :=
  ∀ u g : AdelicGL K (r + 1), IsUpperColId c u.val →
    F (u * g) = (adelicCharacter K (superSum c u) : ℂ) * F g

/-- **Equivariance step**. -/
theorem equivariant_colCoeff {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hFi : MirInvariant (c + 1) F) (hFe : Equivariant (c + 1) F) :
    Equivariant c (colCoeff c F) := by
  intro u g hu
  rw [colCoeff_eq h, colCoeff_eq h]
  unfold fourierCoeff
  set col := colIdx c h with hcol_def
  set e : Fin (r + 1) → K := Pi.single (charIdx c h) 1 with he
  set y0 : Fin (r + 1) → Adeles K := fun i => u.val i col with hy0
  set u' : AdelicGL K (r + 1) := colUnit col (-y0) * u with hu'_def
  obtain ⟨hu', hrow'⟩ := isUpperColId_peel col (colIdx_val c h) hu
  have hu_eq : u = colUnit col y0 * u' := by
    rw [hu'_def, ← mul_assoc, colUnit_mul, add_neg_cancel, colUnit_zero, one_mul]
  have hSS' : superSum (c + 1) u' = superSum (c + 1) u := superSum_congr hrow'
  have key : ∀ y, F (colUnit col y * (u * g)) =
      (adelicCharacter K (superSum (c + 1) u) : ℂ) * F (colUnit col (y + y0) * g) := by
    intro y
    obtain ⟨hu'', hrow''⟩ := isUpperColId_conj col (colIdx_val c h) hu' (y + y0)
    have e2 : (colUnit col (y + y0) * u' * colUnit col (-(y + y0))) * (colUnit col (y + y0) * g) =
        colUnit col (y + y0) * u' * g := by
      rw [mul_assoc _ (colUnit col (-(y + y0))), ← mul_assoc (colUnit col (-(y + y0))),
        colUnit_mul, neg_add_cancel, colUnit_zero, one_mul]
    have e1 : colUnit col y * (u * g) =
        (colUnit col (y + y0) * u' * colUnit col (-(y + y0))) * (colUnit col (y + y0) * g) := by
      rw [e2, hu_eq, ← colUnit_mul]
      simp only [mul_assoc]
    rw [e1, hFe _ _ hu'', superSum_congr (v := u') (fun i j hi => hrow'' i j hi), hSS']
  simp_rw [key, mul_assoc]
  rw [torusIntegral_const_mul]
  have htr := torusIntegral_add_right
    (f := fun y => F (colUnit col y * g) * conj (pairingCharacter e (y + -y0)))
    ((isPeriodic_col h hFi g).mul ((isPeriodic_conj_pairingCharacter e).comp_add (-y0))) y0
  simp only [add_neg_cancel_right] at htr
  rw [htr]
  have hsplit : ∀ y, F (colUnit col y * g) * conj (pairingCharacter e (y + -y0)) =
      F (colUnit col y * g) * conj (pairingCharacter e y) * pairingCharacter e y0 := by
    intro y
    rw [pairingCharacter_add_right, pairingCharacter_neg_right, map_mul, Complex.conj_conj,
      mul_assoc]
  simp_rw [hsplit]
  rw [torusIntegral_mul_const, superSum_succ h u, AddChar.map_add_eq_mul, Circle.coe_mul, he,
    pairingCharacter_single, map_one, one_mul]
  ring

/-! ### Column replacement -/

section ColumnReplacement

variable {n : ℕ}

/-- Integrating out a column: `∫_X ∫_z G(X with column c replaced by z) = ∫_X G(X)`. -/
theorem torusIntegral_updateCol {G : (Fin n × Fin n → Adeles K) → ℂ} (hG : IsPeriodic G)
    (hGc : Continuous G) (c : Fin n) :
    torusIntegral (Fin n × Fin n) (fun X => torusIntegral (Fin n) (fun z => G (updateCol X c z))) =
      torusIntegral (Fin n × Fin n) G := by
  have hstep : ∀ X, torusIntegral (Fin n) (fun z => G (updateCol X c z)) =
      torusIntegral (Fin n) (fun z => G (X + updateCol 0 c z)) := by
    intro X
    have hper : IsPeriodic (fun z => G (updateCol X c z)) := by
      intro z k
      beta_reduce
      have e : updateCol X c (z + ratVec k) = updateCol X c z + ratVec (updateCol 0 c k) := by
        funext q
        simp only [updateCol, Pi.add_apply, ratVec_apply, Pi.zero_apply]
        split_ifs <;> simp
      rw [e, hG]
    rw [← torusIntegral_add_right hper (fun i => X (i, c))]
    refine torusIntegral_congr fun z => ?_
    rw [updateCol_self_add]
  simp_rw [hstep]
  have hcont : Continuous (Function.uncurry fun (X : Fin n × Fin n → Adeles K)
      (z : Fin n → Adeles K) => G (X + updateCol 0 c z)) :=
    hGc.comp (continuous_fst.add ((continuous_updateCol c).comp
      (continuous_const.prodMk continuous_snd)))
  rw [torusIntegral_comm hcont]
  · have hinner : ∀ z : Fin n → Adeles K, torusIntegral (Fin n × Fin n)
        (fun X => G (X + updateCol 0 c z)) = torusIntegral (Fin n × Fin n) G :=
      fun z => torusIntegral_add_right hG _
    simp_rw [hinner]
    exact torusIntegral_const _
  · intro X z k l
    have e : X + ratVec k + updateCol 0 c (z + ratVec l) =
        X + updateCol 0 c z + ratVec (k + updateCol 0 c l) := by
      funext q
      simp only [updateCol, Pi.add_apply, ratVec_apply, Pi.zero_apply, map_add]
      split_ifs <;> (try simp only [map_zero, add_zero]) <;> abel
    rw [e, hG]

end ColumnReplacement

/-! ### Vanishing of block integrals -/

/-- The block integrals over `i < m ≤ j ≤ c` vanish for `1 ≤ m ≤ c`. -/
def BlockVanishing (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) : Prop :=
  ∀ m, 1 ≤ m → m ≤ c → ∀ g : AdelicGL K (r + 1),
    torusIntegral (Fin (r + 1) × Fin (r + 1)) (fun X => F (blkUnit m c X * g)) = 0

theorem isPeriodic_blk {c' : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hF : MirInvariant c' F) {m c : ℕ}
    (hm : m ≤ c') (hc : c ≤ c') (g : AdelicGL K (r + 1)) :
    IsPeriodic (fun X => F (blkUnit m c X * g)) := by
  intro X k
  beta_reduce
  rw [show X + ratVec k = ratVec k + X from add_comm _ _, ← blkUnit_mul, mul_assoc]
  exact hF.blkUnit hm hc k _

theorem isPeriodic_blk_updateCol {c : ℕ} {F : AdelicGL K (r + 1) → ℂ} (hF : MirInvariant (c + 1) F)
    {m : ℕ} (hm : m ≤ c + 1) (col : Fin (r + 1)) (X : Fin (r + 1) × Fin (r + 1) → Adeles K)
    (g : AdelicGL K (r + 1)) :
    IsPeriodic (fun z => F (blkUnit m (c + 1) (updateCol X col z) * g)) := by
  intro z k
  beta_reduce
  have e : updateCol X col (z + ratVec k) = ratVec (updateCol 0 col k) + updateCol X col z := by
    funext q
    simp only [updateCol, Pi.add_apply, ratVec_apply, Pi.zero_apply]
    split_ifs <;> simp [add_comm]
  rw [e, ← blkUnit_mul, mul_assoc]
  exact hF.blkUnit hm le_rfl _ _

/-- **Cuspidality step**: block vanishing descends to the column coefficient. -/
theorem blockVanishing_colCoeff {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) (hFb : BlockVanishing (c + 1) F) :
    BlockVanishing c (colCoeff c F) := by
  intro m hm1 hmc g0
  have hcol : ((colIdx c h : Fin (r + 1)) : ℕ) = c + 1 := colIdx_val c h
  set col := colIdx c h with hcol_def
  set e : Fin (r + 1) → K := Pi.single (charIdx c h) 1 with he
  set χ : (Fin (r + 1) → Adeles K) → ℂ := fun y => conj (pairingCharacter e y) with hχ
  set Q : (Fin (r + 1) → Adeles K) → (Fin (r + 1) → Adeles K) := fun y => y - truncVec m y
    with hQ
  set Ψ : (Fin (r + 1) × Fin (r + 1) → Adeles K) → (Fin (r + 1) → Adeles K) → ℂ :=
    fun X y => torusIntegral (Fin (r + 1))
      (fun z => F (blkUnit m (c + 1) (updateCol X col z) * (colUnit col (Q y) * g0))) with hΨ
  have hχP : ∀ y z, χ (y + truncVec m z) = χ y := by
    intro y z
    simp only [hχ]
    rw [pairingCharacter_add_right, he, pairingCharacter_single (charIdx c h) 1 (truncVec m z)]
    have : truncVec m z (charIdx c h) = 0 :=
      ite_eq_right (show ¬(((charIdx c h : Fin (r + 1)) : ℕ) < m) by rw [charIdx_val]; omega)
    rw [this, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  have hχper : IsPeriodic χ := isPeriodic_conj_pairingCharacter e
  have hχc : Continuous χ := continuous_conj_pairingCharacter e
  -- Step A: the column coefficient of a block translate.
  have hA : ∀ X, colCoeff c F (blkUnit m c X * g0) =
      torusIntegral (Fin (r + 1)) (fun y => χ y * Ψ X y) := by
    intro X
    rw [colCoeff_eq h]
    unfold fourierCoeff
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
      have hGeq : ∀ z, G z = F (blkUnit m (c + 1) (updateCol X col z) * (colUnit col (Q y) * g0)) := by
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
    have e1 : updateCol (X + ratVec k) col z = ratVec (updateCol k col 0) + updateCol X col z := by
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
    have hper := isPeriodic_blk_updateCol hFi (by omega : m ≤ c + 1) col X (colUnit col (Q y) * g0)
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

/-! ### Nonvanishing -/

section Projection

variable {n : ℕ}

/-- The projection of matrix coordinates to column `c`. -/
def colProj (c : Fin n) : (Fin n × Fin n → Adeles K) →+ (Fin n → Adeles K) where
  toFun X := fun i => X (i, c)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem preservesRational_colProj (c : Fin n) : PreservesRational (colProj (K := K) c) :=
  fun k => ⟨fun i => k (i, c), rfl⟩

theorem continuous_colProj (c : Fin n) : Continuous (colProj (K := K) c) :=
  continuous_pi fun i => continuous_apply (i, c)

theorem surjective_colProj (c : Fin n) : Function.Surjective (colProj (K := K) c) := fun y =>
  ⟨updateCol 0 c y, funext fun i => by simp [colProj, updateCol]⟩

theorem blkUnit_eq_colUnit (col : Fin n) {c : ℕ} (hcol : (col : ℕ) = c + 1)
    (X : Fin n × Fin n → Adeles K) :
    blkUnit (c + 1) (c + 1) X = colUnit col (colProj col X) := by
  apply Units.ext
  rw [blkUnit_val, colUnit_val]
  congr 1
  ext i j
  rw [blkMat_apply, colMat_apply]
  by_cases hj : (j : ℕ) = c + 1
  · have hjc : j = col := Fin.ext (by omega)
    subst hjc
    by_cases hi : (i : ℕ) < c + 1
    · rw [ite_eq_left ⟨hi, le_of_eq hj.symm, le_of_eq hj⟩, ite_eq_left ⟨by omega, rfl⟩]
      rfl
    · rw [ite_eq_right (fun h => hi h.1), ite_eq_right (fun h => by omega)]
  · rw [ite_eq_right (fun h => hj (le_antisymm h.2.2 h.2.1)), ite_eq_right (fun h => by omega)]

end Projection

theorem vecMul_transvection_apply {n : ℕ} (a : Fin n → K) (k l j : Fin n) :
    Matrix.vecMul a (Matrix.transvection k l (1 : K)) j = a j + (if j = l then a k else 0) := by
  rw [Matrix.transvection, Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply]
  congr 1
  rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single k]
  · by_cases hj : j = l
    · subst hj
      simp [Matrix.single_apply]
    · simp [Matrix.single_apply, hj, Ne.symm hj]
  · intro i _ hi
    simp [Matrix.single_apply, Ne.symm hi]
  · simp

/-- Fourier coefficients along a column under a rational block matrix. -/
theorem fourierCoeff_col_transform {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) (β : RationalGL K (r + 1))
    (hβ : IsBlk (c + 1) β.val) (g : AdelicGL K (r + 1)) (a : Fin (r + 1) → K) :
    fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a =
      fourierCoeff (fun y => F (colUnit (colIdx c h) y * (AdelicGL.rational K (r + 1) β⁻¹ * g)))
        (Matrix.vecMul a β.val) := by
  have hblk : IsBlk (((colIdx c h : Fin (r + 1)) : ℕ))
      (AdelicGL.rational K (r + 1) β).val := by
    rw [colIdx_val, rational_val]
    exact hβ.map _
  have hconj : ∀ y : Fin (r + 1) → Adeles K, F (colUnit (colIdx c h) y * g) =
      F (colUnit (colIdx c h) (ratMulVec (β⁻¹).val y) * (AdelicGL.rational K (r + 1) β⁻¹ * g)) := by
    intro y
    have e1 : AdelicGL.rational K (r + 1) β * colUnit (colIdx c h) (ratMulVec (β⁻¹).val y) =
        colUnit (colIdx c h) y * AdelicGL.rational K (r + 1) β := by
      rw [colUnit_mul_of_isBlk _ _ hblk, rational_inv_val, ratMulVec_apply]
    have e : colUnit (colIdx c h) y * g = AdelicGL.rational K (r + 1) β *
        (colUnit (colIdx c h) (ratMulVec (β⁻¹).val y) * (AdelicGL.rational K (r + 1) β⁻¹ * g)) := by
      rw [← mul_assoc, e1, mul_assoc, ← mul_assoc (AdelicGL.rational K (r + 1) β),
        ← map_mul (AdelicGL.rational K (r + 1)) β β⁻¹, mul_inv_cancel, map_one, one_mul]
    rw [e]
    exact hFi β hβ.isMir _
  have hrw : (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)) =
      fun y : Fin (r + 1) → Adeles K =>
        (fun w : Fin (r + 1) → Adeles K =>
          F (colUnit (colIdx c h) w * (AdelicGL.rational K (r + 1) β⁻¹ * g)))
        (ratMulVec (β⁻¹).val y) := funext hconj
  rw [hrw]
  have hvec : a = Matrix.vecMul (Matrix.vecMul a β.val) (β⁻¹).val := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  conv_lhs => rw [hvec]
  have hper := isPeriodic_col h hFi (AdelicGL.rational K (r + 1) β⁻¹ * g)
  have hcont := continuous_col_apply h hFc (AdelicGL.rational K (r + 1) β⁻¹ * g)
  exact fourierCoeff_ratMulVec hper hcont β⁻¹ (Matrix.vecMul a β.val)

/-- **Nonvanishing step**: if a column coefficient vanishes identically, so does the function. -/
theorem eq_zero_of_colCoeff_eq_zero {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hFc : Continuous F) (hFi : MirInvariant (c + 1) F) (hFb : BlockVanishing (c + 1) F)
    (h0 : ∀ g, colCoeff c F g = 0) (g : AdelicGL K (r + 1)) : F g = 0 := by
  have hcol : ((colIdx c h : Fin (r + 1)) : ℕ) = c + 1 := colIdx_val c h
  have hfc : ∀ g : AdelicGL K (r + 1),
      Continuous (fun y : Fin (r + 1) → Adeles K => F (colUnit (colIdx c h) y * g)) :=
    continuous_col_apply h hFc
  -- Characters supported in rows `≤ c` with nonzero last entry.
  have caseB : ∀ (g : AdelicGL K (r + 1)) (a : Fin (r + 1) → K),
      (∀ i : Fin (r + 1), c + 1 ≤ (i : ℕ) → a i = 0) →
      a (charIdx c h) ≠ 0 → fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a = 0 := by
    intro g a hsupp hac
    set δM : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.updateRow 1 (charIdx c h) a with hδM
    have hlow : δM.IsLowerTriangular := by
      intro i j hij
      change i < j at hij
      rw [hδM, Matrix.updateRow_apply]
      split_ifs with hi
      · subst hi
        exact hsupp j (by rw [Fin.lt_def, charIdx_val] at hij; omega)
      · exact Matrix.one_apply_ne (ne_of_lt hij)
    have hdet : δM.det ≠ 0 := by
      rw [Matrix.det_of_isLowerTriangular δM hlow, Finset.prod_eq_single (charIdx c h)]
      · rw [hδM, Matrix.updateRow_self]
        exact hac
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
        · rw [hsupp j hij, Matrix.one_apply_ne]
          intro e
          rw [← e, charIdx_val] at hij
          omega
      · rfl
    rw [fourierCoeff_col_transform h hFc hFi δ⁻¹ hδblk.inv g a]
    have hvec : Matrix.vecMul a (δ⁻¹).val = Pi.single (charIdx c h) 1 := by
      have ha : a = Matrix.vecMul (Pi.single (charIdx c h) 1) δ.val := by
        rw [Matrix.single_one_vecMul]
        funext j
        change a j = δM (charIdx c h) j
        rw [hδM, Matrix.updateRow_self]
      rw [ha, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    rw [hvec, inv_inv, ← colCoeff_eq h]
    exact h0 _
  -- The trivial character: block vanishing at level `c + 1`.
  have case0 : ∀ g : AdelicGL K (r + 1),
      fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) 0 = 0 := by
    intro g
    have hb := hFb (c + 1) (by omega) le_rfl g
    simp_rw [blkUnit_eq_colUnit (colIdx c h) hcol] at hb
    unfold fourierCoeff
    simp only [pairingCharacter_zero, map_one, mul_one]
    exact (torusIntegral_comp (f := fun y => F (colUnit (colIdx c h) y * g))
      (isPeriodic_col h hFi g) (hfc g) (preservesRational_colProj (colIdx c h))
      (continuous_colProj (colIdx c h)) (surjective_colProj (colIdx c h))).symm.trans hb
  have hall : ∀ (g : AdelicGL K (r + 1)) (a : Fin (r + 1) → K),
      fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a = 0 := by
    intro g a
    by_cases hbig : ∃ i : Fin (r + 1), c + 1 ≤ (i : ℕ) ∧ a i ≠ 0
    · obtain ⟨i, hi, hai⟩ := hbig
      obtain ⟨x0, hx0⟩ := exists_adelicCharacter_ne_one K
      set t : Fin (r + 1) → Adeles K := Pi.single i (algebraMap K (Adeles K) (a i)⁻¹ * x0) with ht
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
        ((isPeriodic_col h hFi g).mul (isPeriodic_conj_pairingCharacter a)) t
      have hmul : fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a *
          conj (adelicCharacter K x0 : ℂ) = fourierCoeff (fun y => F (colUnit (colIdx c h) y * g)) a := by
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
          exact case0 g
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
          rw [fourierCoeff_col_transform h hFc hFi τ hτblk g a]
          refine caseB _ _ (fun i hi => ?_) ?_
          · change Matrix.vecMul a (Matrix.transvection k (charIdx c h) (1 : K)) i = 0
            rw [vecMul_transvection_apply, hbig i hi,
              ite_eq_right (fun e => by rw [e, charIdx_val] at hi; omega), add_zero]
          · change Matrix.vecMul a (Matrix.transvection k (charIdx c h) (1 : K)) (charIdx c h) ≠ 0
            rw [vecMul_transvection_apply, hac, ite_eq_left rfl, zero_add]
            exact hk
  have h1 := eq_zero_of_fourierCoeff_eq_zero (isPeriodic_col h hFi g) (hfc g) (hall g) 0
  simpa only [colUnit_zero, one_mul] using h1



end Langlands.Automorphic.CuspidalWhittaker
