import Langlands.Representation.Archimedean.RealInductionStagesSlice
import Langlands.Representation.Archimedean.RealInductionStagesFourier

/-!
# Induction in stages of `O(r)`-equivariant maps

Let `L' = pre ++ ds' ++ post` and `L = pre ++ ds ++ post` be lists of real blocks of rank `n`,
with `realRank pre = a` and `realRank ds = realRank ds' = r`. A linear map
`T : KFin r ds' → KFin r ds` commuting exactly with right translation by `O(r)` induces a
linear map `ind T : KFin n L' → KFin n L`: `(ind T F)(κ) = (T σ_κ F)(1)` for `κ ∈ O(n)`, where
`σ_κ` is the slice of `RealInductionStagesSlice`, extended to `GL_n(ℝ)` by the Library's
`PrincipalSeriesExtension.extension`.

`ind T` commutes exactly with right translation by `O(n)`, and `σ_κ (ind T F) = T (σ_κ F)` for
`κ ∈ O(n)`.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean GramFormula
  PrincipalSeriesExtension

set_option backward.isDefEq.respectTransparency false

/-! ## Orthogonal matrices -/

section Unitary

variable {n : ℕ}

/-- The orthogonal matrices as the subgroup `O(n)` of `GL_n(ℝ)`. -/
def ofUnitary (n : ℕ) : Matrix.unitaryGroup (Fin n) ℝ →* unitaryCompact ℝ n :=
  (Unitary.toUnits (R := Matrix (Fin n) (Fin n) ℝ)).codRestrict (unitaryCompact ℝ n)
    fun κ => κ.2

theorem coe_ofUnitary (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    ((ofUnitary n κ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) = Unitary.toUnits κ :=
  rfl

theorem toUnitary_ofUnitary (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    toUnitary n (ofUnitary n κ) = κ :=
  rfl

theorem ofUnitary_toUnitary (k : unitaryCompact ℝ n) : ofUnitary n (toUnitary n k) = k :=
  Subtype.ext (Units.ext rfl)

theorem continuous_toUnits' :
    Continuous (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ → Langlands.GeneralLinear n ℝ) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩

theorem toUnits_signDiagonal (d : Fin n → ℝˣ) :
    (Unitary.toUnits (signDiagonal (fun i => (d i : ℝ))) : Langlands.GeneralLinear n ℝ) =
      Iwasawa.diagonalUnits (fun i => signUnit (d i)) := by
  apply Units.ext
  rw [Iwasawa.diagonalUnits_val]
  change Matrix.diagonal (fun i => signReal (d i : ℝ)) = _
  congr 1
  funext i
  rw [signUnit_val]

end Unitary

/-! ## Positions outside and inside the middle -/

section Positions

theorem append_outside {β : Type*} (f : List RealBlock → ℕ → β)
    (hl : ∀ pre M k, f (pre ++ M) (realRank pre + k) = f M k)
    (hr : ∀ ds post k, k < realRank ds → f (ds ++ post) k = f ds k)
    {pre ds ds' post : List RealBlock} (hds : realRank ds = realRank ds') {i : ℕ}
    (hi : i < realRank pre ∨ realRank pre + realRank ds ≤ i) :
    f (pre ++ ds ++ post) i = f (pre ++ ds' ++ post) i := by
  rcases hi with hi | hi
  · rw [hr (pre ++ ds) post i (by rw [realRank_append']; omega), hr pre ds i hi,
      hr (pre ++ ds') post i (by rw [realRank_append']; omega), hr pre ds' i hi]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    calc f (pre ++ ds ++ post) (realRank pre + realRank ds + k)
        = f (pre ++ ds ++ post) (realRank (pre ++ ds) + k) := by rw [realRank_append']
      _ = f post k := hl _ _ _
      _ = f (pre ++ ds' ++ post) (realRank (pre ++ ds') + k) := (hl _ _ _).symm
      _ = _ := by rw [realRank_append', hds]

theorem append_mid {β : Type*} (f : List RealBlock → ℕ → β)
    (hl : ∀ pre M k, f (pre ++ M) (realRank pre + k) = f M k)
    (hr : ∀ ds post k, k < realRank ds → f (ds ++ post) k = f ds k)
    {pre ds post : List RealBlock} {j : ℕ} (hj : j < realRank ds) :
    f (pre ++ ds ++ post) (realRank pre + j) = f ds j := by
  rw [hr _ _ _ (by rw [realRank_append']; omega), hl]

end Positions

/-! ## Diagonal matrices and the middle block -/

section Torus

variable {n a r : ℕ}

/-- `t` outside the middle coordinates and `1` on them. -/
def outUnits (a r : ℕ) (t : Fin n → ℝˣ) : Fin n → ℝˣ := fun i => if IsMid a r i then 1 else t i

/-- The middle coordinates of `t`. -/
def midUnits (h : a + r ≤ n) (t : Fin n → ℝˣ) : Fin r → ℝˣ := fun j => t (idx h j)

theorem outUnits_mul_extUnits (h : a + r ≤ n) (t : Fin n → ℝˣ) :
    outUnits a r t * extUnits h (midUnits h t) = t := by
  funext i
  by_cases hi : IsMid a r i
  · obtain ⟨j, rfl⟩ := exists_idx_of_isMid h hi
    simp only [Pi.mul_apply, outUnits, ite_eq_left hi, extUnits_idx, midUnits, one_mul]
  · simp only [Pi.mul_apply, outUnits, ite_eq_right hi, extUnits_of_not_isMid h _ hi, mul_one]

theorem diagonalUnits_outUnits_mul_blockEmb (h : a + r ≤ n) (t : Fin n → ℝˣ)
    (g : Langlands.GeneralLinear r ℝ) :
    (Iwasawa.diagonalUnits (outUnits a r t) : Langlands.GeneralLinear n ℝ) * blockEmb h g =
      blockEmb h g * Iwasawa.diagonalUnits (outUnits a r t) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul, Matrix.mul_diagonal,
    blockEmb_val]
  by_cases hi : IsMid a r i
  · by_cases hj : IsMid a r j
    · simp [outUnits, hi, hj]
    · rw [blockMat_apply_of_not_isMid_right _ _ hj,
        Matrix.one_apply_ne (fun e => hj (by rw [← e]; exact hi))]
      simp
  · rw [blockMat_apply_of_not_isMid_left _ hi, Matrix.one_apply]
    split_ifs with hij
    · subst hij
      ring
    · simp

theorem diagonalUnits_eq_mul (h : a + r ≤ n) (t : Fin n → ℝˣ) :
    (Iwasawa.diagonalUnits t : Langlands.GeneralLinear n ℝ) =
      Iwasawa.diagonalUnits (outUnits a r t) * blockEmb h (Iwasawa.diagonalUnits (midUnits h t)) := by
  rw [blockEmb_diagonalUnits, ← map_mul, outUnits_mul_extUnits]

theorem principalSeriesCharacter_outUnits_mul (h : a + r ≤ n) {χ : ℕ → ℝˣ → ℂ}
    (h1 : ∀ i, χ i 1 = 1) (t : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n χ (outUnits a r t) *
        principalSeriesCharacter ℝ n χ (extUnits h (midUnits h t)) =
      principalSeriesCharacter ℝ n χ t := by
  unfold principalSeriesCharacter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : IsMid a r i
  · obtain ⟨j, rfl⟩ := exists_idx_of_isMid h hi
    simp [outUnits, hi, extUnits_idx, midUnits, h1]
  · simp [outUnits, hi, extUnits_of_not_isMid h _ hi, h1]

theorem principalSeriesCharacter_outUnits_congr {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ : ∀ i : Fin n, ¬IsMid a r i → χ i = χ' i) (h1 : ∀ i, χ i 1 = 1) (h1' : ∀ i, χ' i 1 = 1)
    (t : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n χ (outUnits a r t) =
      principalSeriesCharacter ℝ n χ' (outUnits a r t) := by
  unfold principalSeriesCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : IsMid a r i
  · simp [outUnits, hi, h1, h1']
  · rw [hχ i hi]

theorem sliceFactor_diagonalUnits_signUnit (d : Fin r → ℝˣ) :
    sliceFactor n a r (Iwasawa.diagonalUnits (fun j => signUnit (d j))) = 1 := by
  rw [sliceFactor_diagonalUnits]
  simp [abs_signUnit]

/-- `σ_{diag(t) κ} F (g) · ν(diag(t_mid)) = χ(t_out) · σ_κ F (g diag(t_mid))`. -/
theorem slice_diagonalUnits_mul (h : a + r ≤ n) {χ : ℕ → ℝˣ → ℂ}
    {F : Langlands.GeneralLinear n ℝ → ℂ} (hF : F ∈ principalSeries ℝ n χ) (t : Fin n → ℝˣ)
    (κ : Langlands.GeneralLinear n ℝ) (g : Langlands.GeneralLinear r ℝ) :
    slice h (Iwasawa.diagonalUnits t * κ) F g *
        sliceFactor n a r (Iwasawa.diagonalUnits (midUnits h t)) =
      principalSeriesCharacter ℝ n χ (outUnits a r t) *
        slice h κ F (g * Iwasawa.diagonalUnits (midUnits h t)) := by
  have harg : blockEmb h g * ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear n ℝ) * κ) =
      (Iwasawa.diagonalUnits (outUnits a r t) : Langlands.GeneralLinear n ℝ) *
        ((1 : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) *
        (blockEmb h (g * Iwasawa.diagonalUnits (midUnits h t)) * κ) := by
    rw [diagonalUnits_eq_mul h t, map_mul, OneMemClass.coe_one, mul_one]
    simp only [← mul_assoc]
    rw [← diagonalUnits_outUnits_mul_blockEmb]
  rw [slice_apply, slice_apply, harg, hF.2, sliceFactor_mul]
  ring

end Torus

/-! ## The induced map -/

section Induce

variable {n a r : ℕ} {pre ds ds' post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r) (hr' : realRank ds' = r)

include ha hr hr' in
theorem realPositionCharacter_outside {i : ℕ} (hi : i < a ∨ a + r ≤ i) :
    realPositionCharacter (pre ++ ds ++ post) i = realPositionCharacter (pre ++ ds' ++ post) i :=
  append_outside realPositionCharacter realPositionCharacter_append_left
    realPositionCharacter_append_right (hr.trans hr'.symm) (by rw [ha, hr]; exact hi)

include ha hr hr' in
theorem realPositionExponent_outside {i : ℕ} (hi : i < a ∨ a + r ≤ i) :
    realPositionExponent (pre ++ ds ++ post) i = realPositionExponent (pre ++ ds' ++ post) i :=
  append_outside realPositionExponent realPositionExponent_append_left
    realPositionExponent_append_right (hr.trans hr'.symm) (by rw [ha, hr]; exact hi)

include ha hr hr' in
theorem realInducedBlockAt_outside {i : ℕ} (hi : i < a ∨ a + r ≤ i) :
    realInducedBlockAt (pre ++ ds ++ post) i = realInducedBlockAt (pre ++ ds' ++ post) i :=
  append_outside realInducedBlockAt realInducedBlockAt_append_left
    realInducedBlockAt_append_right (hr.trans hr'.symm) (by rw [ha, hr]; exact hi)

include ha hr in
theorem realPositionCharacter_mid (j : Fin r) :
    realPositionCharacter (pre ++ ds ++ post) (a + j) = realPositionCharacter ds j := by
  subst ha hr
  exact append_mid realPositionCharacter realPositionCharacter_append_left
    realPositionCharacter_append_right j.isLt

/-- `F ↦ (κ ↦ (T σ_κ F)(1))`, functions on the orthogonal matrices. -/
def indFun (T : KFin r ds' →ₗ[ℂ] KFin r ds) :
    KFin n (pre ++ ds' ++ post) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) where
  toFun F κ := (T (sliceK h ha hr' (ofUnitary n κ) F) : Langlands.GeneralLinear r ℝ → ℂ) 1
  map_add' F G := by
    funext κ
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c F := by
    funext κ
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

variable (T : KFin r ds' →ₗ[ℂ] KFin r ds)

theorem indFun_apply (F : KFin n (pre ++ ds' ++ post)) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    indFun h ha hr' T F κ =
      (T (sliceK h ha hr' (ofUnitary n κ) F) : Langlands.GeneralLinear r ℝ → ℂ) 1 :=
  rfl

theorem indFun_mul (F : KFin n (pre ++ ds' ++ post)) (κ k : Matrix.unitaryGroup (Fin n) ℝ) :
    indFun h ha hr' T F (κ * k) =
      indFun h ha hr' T (kRep n (pre ++ ds' ++ post) (ofUnitary n k) F) κ := by
  rw [indFun_apply, indFun_apply, sliceK_kRep, map_mul]

theorem continuous_indFun (F : KFin n (pre ++ ds' ++ post)) :
    Continuous (indFun h ha hr' T F) := by
  have heq : indFun h ha hr' T F = fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
      ((T ∘ₗ sliceK h ha hr' 1) (kRep n (pre ++ ds' ++ post) (ofUnitary n κ) F) :
        Langlands.GeneralLinear r ℝ → ℂ) 1 := by
    funext κ
    rw [indFun_apply, LinearMap.comp_apply, sliceK_kRep, one_mul]
  rw [heq]
  refine continuous_map_of_mem (T ∘ₗ sliceK h ha hr' 1)
    (FiniteVectors.orbitSpan (realStandardRep n (pre ++ ds' ++ post)) F)
    (fun κ => kRep_mem_orbitSpan _ F) (fun x => ?_) 1
  simp_rw [kRep_apply_coe, coe_ofUnitary]
  exact (RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions F.2).comp
    (continuous_const.mul continuous_toUnits')

theorem finiteDimensional_indFun (F : KFin n (pre ++ ds' ++ post)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => indFun h ha hr' T F (x * k))) := by
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => indFun h ha hr' T F (x * k)) ≤
      (FiniteVectors.orbitSpan (realStandardRep n (pre ++ ds' ++ post)) F).map
        (indFun h ha hr' T) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨kRep n (pre ++ ds' ++ post) (ofUnitary n k) F, kRep_mem_orbitSpan _ F, ?_⟩
    funext x
    exact (indFun_mul h ha hr' T F x k).symm
  exact Submodule.finiteDimensional_of_le hle

variable {T}

include hr in
theorem indFun_signDiagonal_mul (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))
    (F : KFin n (pre ++ ds' ++ post)) (d : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    indFun h ha hr' T F (signDiagonal (fun i => (d i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n (realPositionCharacter (pre ++ ds ++ post))
        (fun i => signUnit (d i)) * indFun h ha hr' T F κ := by
  set t : Fin n → ℝˣ := fun i => signUnit (d i) with ht
  set km : unitaryCompact ℝ r := ofUnitary r (signDiagonal (fun j => (d (idx h j) : ℝ)))
    with hkm
  have hkmv : (km : Langlands.GeneralLinear r ℝ) = Iwasawa.diagonalUnits (midUnits h t) := by
    rw [hkm, coe_ofUnitary, toUnits_signDiagonal]
    rfl
  set c : ℂ := principalSeriesCharacter ℝ n (realPositionCharacter (pre ++ ds' ++ post))
    (outUnits a r t) with hc
  -- the slice at `diag(t) κ`
  have hslice : sliceK h ha hr' (ofUnitary n (signDiagonal (fun i => (d i : ℝ)) * κ)) F =
      c • kRep r ds' km (sliceK h ha hr' (ofUnitary n κ) F) := by
    apply Subtype.ext
    funext g
    simp only [sliceK_apply_coe, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, kRep_apply_coe]
    have hcoe : ((ofUnitary n (signDiagonal (fun i => (d i : ℝ)) * κ) : unitaryCompact ℝ n) :
        Langlands.GeneralLinear n ℝ) = Iwasawa.diagonalUnits t * Unitary.toUnits κ := by
      rw [coe_ofUnitary, map_mul, toUnits_signDiagonal]
    have key := slice_diagonalUnits_mul h F.2.1.1 t (Unitary.toUnits κ) g
    have hsf : sliceFactor n a r (Iwasawa.diagonalUnits (midUnits h t)) = 1 :=
      sliceFactor_diagonalUnits_signUnit (fun j => d (idx h j))
    rw [hsf, mul_one] at key
    rw [hcoe, hkmv, coe_ofUnitary]
    exact key
  -- the value of `T σ` at `diag(t_mid)`
  have hval : ((T (sliceK h ha hr' (ofUnitary n κ) F) : KFin r ds) :
      Langlands.GeneralLinear r ℝ → ℂ) (Iwasawa.diagonalUnits (midUnits h t)) =
      principalSeriesCharacter ℝ r (realPositionCharacter ds) (midUnits h t) *
        (T (sliceK h ha hr' (ofUnitary n κ) F) : Langlands.GeneralLinear r ℝ → ℂ) 1 := by
    have := (T (sliceK h ha hr' (ofUnitary n κ) F)).2.1.1.2 (midUnits h t) 1 1
    simpa using this
  -- the characters
  have hchar : principalSeriesCharacter ℝ n (realPositionCharacter (pre ++ ds ++ post)) t =
      c * principalSeriesCharacter ℝ r (realPositionCharacter ds) (midUnits h t) := by
    rw [← principalSeriesCharacter_outUnits_mul h
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) t, hc,
      principalSeriesCharacter_outUnits_congr (χ' := realPositionCharacter (pre ++ ds' ++ post))
        (fun i hi => realPositionCharacter_outside ha hr hr' (by unfold IsMid at hi; omega))
        (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _)
        (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _)]
    congr 1
    have hs := sliceFactor_mul_principalSeriesCharacter h
      (χ := realPositionCharacter (pre ++ ds ++ post)) (ψ := realPositionCharacter ds)
      (fun j => realPositionCharacter_mid (post := post) ha hr j)
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) (midUnits h t)
    rwa [show Iwasawa.diagonalUnits (midUnits h t) =
        Iwasawa.diagonalUnits (fun j => signUnit (d (idx h j))) from rfl,
      sliceFactor_diagonalUnits_signUnit, one_mul] at hs
  rw [indFun_apply, indFun_apply, hslice, map_smul, hT, Submodule.coe_smul,
    Pi.smul_apply, kRep_apply_coe, one_mul, hkmv, hval, smul_eq_mul, hchar]
  ring

end Induce

/-! ## Rotations outside the middle block -/

section Rotation

variable {n a r : ℕ}

theorem mul_embMat_eq (h : a + r ≤ n) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i k, IsMid a r k → M i k = (1 : Matrix (Fin n) (Fin n) ℝ) i k) :
    M * embMat n a r = embMat n a r := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (idx h j)]
  · rw [hM i _ (isMid_idx h j), Matrix.one_apply]
    simp only [embMat, Matrix.of_apply, idx_val, ite_true, mul_one, Fin.ext_iff]
  · intro k _ hk
    have : ¬ ((k : ℕ) = a + j) := fun e => hk (Fin.ext (by rw [idx_val]; exact e))
    simp [embMat, this]
  · simp

theorem embMat_transpose_mul_eq (h : a + r ≤ n) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ k j, IsMid a r k → M k j = (1 : Matrix (Fin n) (Fin n) ℝ) k j) :
    (embMat n a r)ᵀ * M = (embMat n a r)ᵀ := by
  have h1 : Mᵀ * embMat n a r = embMat n a r := mul_embMat_eq h fun i k hk => by
    rw [Matrix.transpose_apply, hM k i hk, Matrix.one_apply, Matrix.one_apply]
    simp only [eq_comm]
  have h2 := congrArg Matrix.transpose h1
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h2

/-- A matrix agreeing with the identity on the middle rows and columns commutes with the block
matrices. -/
theorem mul_blockMat_comm (h : a + r ≤ n) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM1 : ∀ i k, IsMid a r k → M i k = (1 : Matrix (Fin n) (Fin n) ℝ) i k)
    (hM2 : ∀ k j, IsMid a r k → M k j = (1 : Matrix (Fin n) (Fin n) ℝ) k j)
    (y : Matrix (Fin r) (Fin r) ℝ) : M * blockMat n a r y = blockMat n a r y * M := by
  simp only [blockMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  rw [← Matrix.mul_assoc M, ← Matrix.mul_assoc M, mul_embMat_eq h hM1,
    Matrix.mul_assoc _ (embMat n a r)ᵀ M, embMat_transpose_mul_eq h hM2]

/-- Rotations in coordinates outside the middle block commute with the block embedding. -/
theorem blockRotation_mul_blockEmb (h : a + r ≤ n) {p : ℕ} (hp : p + 1 < n)
    (hout : p + 1 < a ∨ a + r ≤ p) (θ : ℝ) (g : Langlands.GeneralLinear r ℝ) :
    blockRotation n p θ * blockEmb h g = blockEmb h g * blockRotation n p θ := by
  apply Units.ext
  simp only [Units.val_mul, blockEmb_val]
  refine mul_blockMat_comm h (fun i k hk => ?_) (fun k j hk => ?_) _
  · rw [RealBlockRotation.blockRotation_apply hp, Matrix.one_apply]
    unfold IsMid at hk
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [RealBlockRotation.blockRotation_apply hp, Matrix.one_apply]
    unfold IsMid at hk
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The rotation `r_p(θ)` as an element of `O(n)`. -/
def rotK (n p : ℕ) (θ : ℝ) : unitaryCompact ℝ n :=
  ⟨blockRotation n p θ, blockRotation_mem_unitaryCompact n p θ⟩

theorem coe_rotK (n p : ℕ) (θ : ℝ) :
    ((rotK n p θ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) = blockRotation n p θ :=
  rfl

end Rotation

/-! ## The extension to `GL_n(ℝ)` -/

section Extension

variable {n a r : ℕ} {pre ds ds' post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r) (hr' : realRank ds' = r)
  (hn : realRank (pre ++ ds ++ post) = n) (T : KFin r ds' →ₗ[ℂ] KFin r ds)

/-- The extension of `indFun` to `GL_n(ℝ)`. -/
def indExt : KFin n (pre ++ ds' ++ post) →ₗ[ℂ] (Langlands.GeneralLinear n ℝ → ℂ) :=
  (extensionLinear (shiftedExponent n (realPositionExponent (pre ++ ds ++ post)))).comp
    (indFun h ha hr' T)

theorem indExt_apply (F : KFin n (pre ++ ds' ++ post)) :
    indExt h ha hr' T F =
      extension (shiftedExponent n (realPositionExponent (pre ++ ds ++ post)))
        (indFun h ha hr' T F) :=
  rfl

theorem indExt_unitaryCompact (F : KFin n (pre ++ ds' ++ post)) (κ : unitaryCompact ℝ n) :
    indExt h ha hr' T F κ = (T (sliceK h ha hr' κ F) : Langlands.GeneralLinear r ℝ → ℂ) 1 := by
  rw [indExt_apply, ← toUnits_toUnitary n κ, extension_unitary, indFun_apply,
    ofUnitary_toUnitary]

variable {T}

include hr in
theorem indExt_mem (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))
    (F : KFin n (pre ++ ds' ++ post)) :
    indExt h ha hr' T F ∈ kFiniteFunctions
      (principalSeries ℝ n (realPositionCharacter (pre ++ ds ++ post))) (unitaryCompact ℝ n) :=
  extension_mem_kFiniteFunctions _ (realPositionCharacter_eq_signUnit_mul _)
    (continuous_indFun h ha hr' T F) (finiteDimensional_indFun h ha hr' T F)
    (indFun_signDiagonal_mul h ha hr hr' hT F)

/-- `Ind T F (ι(k) κ) = (T σ_κ F)(k)`. -/
theorem indExt_blockEmb (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))
    (F : KFin n (pre ++ ds' ++ post)) (κ : unitaryCompact ℝ n) (k : unitaryCompact ℝ r) :
    indExt h ha hr' T F (blockEmb h (k : Langlands.GeneralLinear r ℝ) * κ) =
      (T (sliceK h ha hr' κ F) : Langlands.GeneralLinear r ℝ → ℂ) k := by
  have key := indExt_unitaryCompact h ha hr' T F (blockEmbK h k * κ)
  rw [Subgroup.coe_mul, coe_blockEmbK, ← kRep_sliceK, hT, kRep_apply_coe, one_mul] at key
  exact key

include hr in
/-- **Slice identity.** `σ_κ (Ind T F) = T (σ_κ F)` for `κ ∈ O(n)`. -/
theorem slice_indExt (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))
    (F : KFin n (pre ++ ds' ++ post)) (κ : unitaryCompact ℝ n) :
    slice h (κ : Langlands.GeneralLinear n ℝ) (indExt h ha hr' T F) =
      (T (sliceK h ha hr' κ F) : Langlands.GeneralLinear r ℝ → ℂ) := by
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (slice_mem_principalSeries h (fun j => realPositionCharacter_mid (post := post) ha hr j)
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) _
      (indExt_mem h ha hr hr' hT F).1)
    (T (sliceK h ha hr' κ F)).2.1.1 fun k hk => ?_
  rw [slice_apply, sliceFactor_of_mem_unitaryCompact hk, one_mul]
  exact indExt_blockEmb h ha hr' hT F κ ⟨k, hk⟩

/-- Fourier coefficients along rotations outside the middle block. -/
theorem blockFourierCoefficient_indExt_outside (F : KFin n (pre ++ ds' ++ post)) {p : ℕ}
    (hp : p + 1 < n) (hout : p + 1 < a ∨ a + r ≤ p) (j : ℤ)
    (hF : ∀ g, blockFourierCoefficient n p j (F : Langlands.GeneralLinear n ℝ → ℂ) g = 0)
    (κ : unitaryCompact ℝ n) :
    blockFourierCoefficient n p j (indExt h ha hr' T F) κ = 0 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let w : ℝ → KFin r ds' := fun θ =>
    Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) • sliceK h ha hr' (rotK n p θ * κ) F
  have hS : ∀ θ, w θ ∈ (FiniteVectors.orbitSpan (realStandardRep n (pre ++ ds' ++ post)) F).map
      (sliceK h ha hr' 1) := fun θ =>
    Submodule.smul_mem _ _ ⟨kRep n (pre ++ ds' ++ post) (rotK n p θ * κ) F,
      kRep_mem_orbitSpan _ F, by rw [sliceK_kRep, one_mul]⟩
  have hval : ∀ (θ : ℝ) (x : Langlands.GeneralLinear r ℝ),
      (w θ : Langlands.GeneralLinear r ℝ → ℂ) x =
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (sliceFactor n a r x *
        (F : Langlands.GeneralLinear n ℝ → ℂ) (blockRotation n p θ * (blockEmb h x * κ))) := by
    intro θ x
    simp only [w, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, sliceK_apply_coe, slice_apply,
      Subgroup.coe_mul, coe_rotK]
    rw [mul_assoc, ← mul_assoc (blockEmb h x), ← blockRotation_mul_blockEmb h hp hout,
      mul_assoc]
  have hFc := RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions F.2
  have hi : ∀ x, Integrable (fun θ => (w θ : Langlands.GeneralLinear r ℝ → ℂ) x) μ := by
    intro x
    simp_rw [hval]
    refine Continuous.integrableOn_Ioc ?_
    exact (Complex.continuous_exp.comp (by fun_prop)).mul (continuous_const.mul
      (hFc.comp ((continuous_blockRotation n p).mul continuous_const)))
  have hv : ∀ x, ((0 : KFin r ds') : Langlands.GeneralLinear r ℝ → ℂ) x =
      ∫ θ, (w θ : Langlands.GeneralLinear r ℝ → ℂ) x ∂μ := by
    intro x
    simp_rw [hval]
    have hb := hF (blockEmb h x * κ)
    unfold blockFourierCoefficient at hb
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le] at hb
    have hc : ∀ θ : ℝ, Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) * (sliceFactor n a r x *
        (F : Langlands.GeneralLinear n ℝ → ℂ) (blockRotation n p θ * (blockEmb h x * κ))) =
        sliceFactor n a r x * ((F : Langlands.GeneralLinear n ℝ → ℂ)
          (blockRotation n p θ * (blockEmb h x * κ)) *
            Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))) := fun θ => by ring
    simp_rw [hc]
    rw [integral_const_mul, hb, mul_zero]
    rfl
  have key := map_integral_of_mem μ T _ hS hi hv 1
  rw [map_zero, Submodule.coe_zero, Pi.zero_apply] at key
  unfold blockFourierCoefficient
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hpt : (fun θ : ℝ => indExt h ha hr' T F (blockRotation n p θ * κ) *
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))) =
      fun θ => (T (w θ) : Langlands.GeneralLinear r ℝ → ℂ) 1 := by
    funext θ
    simp only [w, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [← indExt_unitaryCompact, mul_comm]
    rfl
  rw [hpt]
  exact key.symm

include hr hn in
/-- The Fourier conditions for `Ind T F` on `O(n)`. -/
theorem blockFourierCoefficient_indExt (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))
    (F : KFin n (pre ++ ds' ++ post)) {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt (pre ++ ds ++ post) p = some d) {j : ℤ} (hj : |j| < |d.weight|)
    (κ : unitaryCompact ℝ n) :
    blockFourierCoefficient n p j (indExt h ha hr' T F) κ = 0 := by
  have hpn : p + 1 < n := hn ▸ realInducedBlockAt_lt hd
  have hout : ∀ hout : p + 1 < a ∨ a + r ≤ p,
      blockFourierCoefficient n p j (indExt h ha hr' T F) κ = 0 := fun hout =>
    blockFourierCoefficient_indExt_outside h ha hr' F hpn hout j
      (F.2.1.2 p d ((realInducedBlockAt_outside ha hr hr' (by omega)).symm.trans hd) j hj) κ
  rcases realInducedBlockAt_append_cases (pre ++ ds) post p d hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases realInducedBlockAt_append_cases pre ds p d h2 with ⟨h3, -⟩ | ⟨h3, h4⟩
    · exact hout (Or.inl (by omega))
    · rw [ha] at h3 h4
      have hp' : p - a + 1 < r := hr ▸ realInducedBlockAt_lt h4
      have key := blockFourierCoefficient_slice h hp' j (κ : Langlands.GeneralLinear n ℝ)
        (indExt h ha hr' T F) 1
      rw [sliceFactor_one, one_mul, map_one, one_mul, show a + (p - a) = p by omega,
        slice_indExt h ha hr hr' hT F κ] at key
      rw [← key]
      exact (T (sliceK h ha hr' κ F)).2.1.2 (p - a) d h4 j hj 1
  · rw [realRank_append', ha, hr] at h1
    exact hout (Or.inr h1)

include hr hn in
theorem indExt_mem_kFin (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))
    (F : KFin n (pre ++ ds' ++ post)) : indExt h ha hr' T F ∈ KFin n (pre ++ ds ++ post) := by
  have hm := indExt_mem h ha hr hr' hT F
  exact ⟨mem_realStandardModule_of_unitaryCompact hn hm.1 fun p d hd j hj κ hκ =>
    blockFourierCoefficient_indExt h ha hr hr' hn hT F hd hj ⟨κ, hκ⟩, hm.2⟩

variable (T) in
/-- **The induced map** `Ind T : KFin n (pre ++ ds' ++ post) → KFin n (pre ++ ds ++ post)` of an
exactly `O(r)`-equivariant `T`. -/
def ind (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f)) :
    KFin n (pre ++ ds' ++ post) →ₗ[ℂ] KFin n (pre ++ ds ++ post) :=
  (indExt h ha hr' T).codRestrict _ (indExt_mem_kFin h ha hr hr' hn hT)

variable (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))

theorem ind_apply_coe (F : KFin n (pre ++ ds' ++ post)) :
    (ind h ha hr hr' hn T hT F : Langlands.GeneralLinear n ℝ → ℂ) = indExt h ha hr' T F :=
  rfl

theorem ind_apply_unitaryCompact (F : KFin n (pre ++ ds' ++ post)) (κ : unitaryCompact ℝ n) :
    (ind h ha hr hr' hn T hT F : Langlands.GeneralLinear n ℝ → ℂ) κ =
      (T (sliceK h ha hr' κ F) : Langlands.GeneralLinear r ℝ → ℂ) 1 :=
  indExt_unitaryCompact h ha hr' T F κ

/-- `Ind T` commutes exactly with right translation by `O(n)`. -/
theorem ind_kRep (κ' : unitaryCompact ℝ n) (F : KFin n (pre ++ ds' ++ post)) :
    ind h ha hr hr' hn T hT (kRep n (pre ++ ds' ++ post) κ' F) =
      kRep n (pre ++ ds ++ post) κ' (ind h ha hr hr' hn T hT F) := by
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (ind h ha hr hr' hn T hT (kRep n (pre ++ ds' ++ post) κ' F)).2.1.1
    (kRep n (pre ++ ds ++ post) κ' (ind h ha hr hr' hn T hT F)).2.1.1 fun g hg => ?_
  rw [kRep_apply_coe]
  have e1 := ind_apply_unitaryCompact h ha hr hr' hn hT (kRep n (pre ++ ds' ++ post) κ' F)
    ⟨g, hg⟩
  have e2 := ind_apply_unitaryCompact h ha hr hr' hn hT F (⟨g, hg⟩ * κ')
  rw [Subgroup.coe_mul] at e2
  rw [e1, e2, sliceK_kRep]

/-- **Slice identity.** `σ_κ (Ind T F) = T (σ_κ F)` for `κ ∈ O(n)`. -/
theorem sliceK_ind (κ : unitaryCompact ℝ n) (F : KFin n (pre ++ ds' ++ post)) :
    sliceK h ha hr κ (ind h ha hr hr' hn T hT F) = T (sliceK h ha hr' κ F) :=
  Subtype.ext (slice_indExt h ha hr hr' hT F κ)

end Extension

end InductionStages

end Langlands.Archimedean
