import Langlands.Representation.Archimedean.RealLeviDuality
import Langlands.Representation.Archimedean.RealLeviGeometry
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# Class slices of the dual principal series along a block diagonal Levi subgroup

Restriction of functions on `GL_N(ℝ)` to one diagonal block `GL_{sz_i}(ℝ)` of a block
diagonal Levi subgroup. For a concatenation `flat dss` of lists of real blocks, the restriction of
the dual principal series lies in the dual principal series of the class list `cl dss i`
twisted by `|·|^{s_i}`, `s_i = start_i - (N - sz_i)/2` (`slice`). It intertwines the actions of
the block's `O(sz_i)` and Lie algebra. Internal infrastructure for the proof of
`RealStandardLanglandsQuotientStatement`; see `RealLeviSlices.md`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLeviSlices

/-! ## Twisted lists -/

section Twist

/-- The block twisted by the character `|·|^s` at each of its positions. -/
def twistBlock (s : ℝ) : RealBlock → RealBlock
  | .character d => .character (RealJacquetFrobenius.charData d.parity (d.exponent + s))
  | .induced d => .induced (characterOfParams d.weight (d.exponent + s))

/-- The list twisted by `|·|^s`. -/
def twist (s : ℝ) (ds : List RealBlock) : List RealBlock := ds.map (twistBlock s)

theorem rank_twistBlock (s : ℝ) (b : RealBlock) : (twistBlock s b).rank = b.rank := by
  cases b <;> rfl

theorem twist_cons (s : ℝ) (b : RealBlock) (ds : List RealBlock) :
    twist s (b :: ds) = twistBlock s b :: twist s ds := rfl

theorem realRank_twist (s : ℝ) : ∀ ds : List RealBlock, realRank (twist s ds) = realRank ds
  | [] => rfl
  | b :: ds => by rw [twist_cons, realRank_cons, realRank_cons, rank_twistBlock, realRank_twist s ds]

theorem realBlockExponent_twistBlock (s : ℝ) (b : RealBlock) :
    realBlockExponent (twistBlock s b) = realBlockExponent b + s := by
  cases b with
  | character d => simp [twistBlock, realBlockExponent, RealJacquetFrobenius.charData]
  | induced d => simp [twistBlock, realBlockExponent]

theorem abs_cpow_add (x : ℝˣ) (a b : ℂ) :
    ((|(x : ℝ)| : ℝ) : ℂ) ^ (a + b) = ((|(x : ℝ)| : ℝ) : ℂ) ^ a * ((|(x : ℝ)| : ℝ) : ℂ) ^ b :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr x.ne_zero))

/-- The position characters of a twisted list are multiplied by `|·|^s`. -/
theorem realPositionCharacter_twist (s : ℝ) :
    ∀ (ds : List RealBlock) (p : ℕ), p < realRank ds → ∀ x : ℝˣ,
      realPositionCharacter (twist s ds) p x =
        realPositionCharacter ds p x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ)
  | [], p, hp, _ => by simp [realRank_nil] at hp
  | .character d :: _, 0, _, x => by
      simp only [twist_cons, twistBlock, realPositionCharacter]
      rw [RealJacquetFrobenius.charData_character_apply, d.character_eq x,
        ← RealJacquetFrobenius.charFun_mul_cpow _ _ _ x.ne_zero]
      rfl
  | .character _ :: ds, p + 1, hp, x => by
      simp only [twist_cons, twistBlock, realPositionCharacter]
      refine realPositionCharacter_twist s ds p ?_ x
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega
  | .induced d :: _, 0, _, x => by
      simp only [twist_cons, twistBlock, realPositionCharacter, realInducedFirstCharacter,
        characterOfParams_weight, characterOfParams_exponent]
      rw [mul_assoc, ← abs_cpow_add]
      congr 2
      ring
  | .induced d :: _, 1, _, x => by
      simp only [twist_cons, twistBlock, realPositionCharacter, realInducedSecondCharacter,
        characterOfParams_weight, characterOfParams_exponent]
      rw [← abs_cpow_add]
      congr 1
      ring
  | .induced _ :: ds, p + 2, hp, x => by
      simp only [twist_cons, twistBlock, realPositionCharacter]
      refine realPositionCharacter_twist s ds p ?_ x
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega

/-- The induction blocks of a twisted list are the twisted induction blocks, of the same
weights. -/
theorem realInducedBlockAt_twist (s : ℝ) :
    ∀ (ds : List RealBlock) (p : ℕ),
      realInducedBlockAt (twist s ds) p =
        (realInducedBlockAt ds p).map fun d => characterOfParams d.weight (d.exponent + s)
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => by
      simp only [twist_cons, twistBlock, realInducedBlockAt]
      exact realInducedBlockAt_twist s ds p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: ds, p + 2 => by
      simp only [twist_cons, twistBlock, realInducedBlockAt]
      exact realInducedBlockAt_twist s ds p

/-- All position characters take the value `1` at `1`. -/
theorem realPositionCharacter_one : ∀ (ds : List RealBlock) (p : ℕ),
    realPositionCharacter ds p 1 = 1
  | [], _ => rfl
  | .character d :: _, 0 => by simp [realPositionCharacter]
  | .character _ :: ds, p + 1 => realPositionCharacter_one ds p
  | .induced d :: _, 0 => by simp [realPositionCharacter, realInducedFirstCharacter]
  | .induced d :: _, 1 => by simp [realPositionCharacter, realInducedSecondCharacter]
  | .induced _ :: ds, p + 2 => realPositionCharacter_one ds p

end Twist

/-! ## Concatenated lists -/

section Append

theorem realRank_append (A B : List RealBlock) : realRank (A ++ B) = realRank A + realRank B := by
  simp [realRank, List.map_append, List.sum_append]

theorem realPositionCharacter_append_left :
    ∀ (A B : List RealBlock) (p : ℕ), p < realRank A →
      realPositionCharacter (A ++ B) p = realPositionCharacter A p
  | [], _, p, hp => by simp [realRank_nil] at hp
  | .character _ :: _, _, 0, _ => rfl
  | .character _ :: A, B, p + 1, hp => by
      simp only [List.cons_append, realPositionCharacter]
      refine realPositionCharacter_append_left A B p ?_
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega
  | .induced _ :: _, _, 0, _ => rfl
  | .induced _ :: _, _, 1, _ => rfl
  | .induced _ :: A, B, p + 2, hp => by
      simp only [List.cons_append, realPositionCharacter]
      refine realPositionCharacter_append_left A B p ?_
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega

theorem realPositionCharacter_append_right :
    ∀ (A B : List RealBlock) (p : ℕ),
      realPositionCharacter (A ++ B) (realRank A + p) = realPositionCharacter B p
  | [], _, p => by simp [realRank_nil]
  | .character d :: A, B, p => by
      have h : realRank (.character d :: A) + p = (realRank A + p) + 1 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [List.cons_append, h]
      exact realPositionCharacter_append_right A B p
  | .induced d :: A, B, p => by
      have h : realRank (.induced d :: A) + p = (realRank A + p) + 2 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [List.cons_append, h]
      exact realPositionCharacter_append_right A B p

theorem realInducedBlockAt_append_left :
    ∀ (A B : List RealBlock) (p : ℕ), p < realRank A →
      realInducedBlockAt (A ++ B) p = realInducedBlockAt A p
  | [], _, p, hp => by simp [realRank_nil] at hp
  | .character _ :: _, _, 0, _ => rfl
  | .character _ :: A, B, p + 1, hp => by
      simp only [List.cons_append, realInducedBlockAt]
      refine realInducedBlockAt_append_left A B p ?_
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega
  | .induced _ :: _, _, 0, _ => rfl
  | .induced _ :: _, _, 1, _ => rfl
  | .induced _ :: A, B, p + 2, hp => by
      simp only [List.cons_append, realInducedBlockAt]
      refine realInducedBlockAt_append_left A B p ?_
      rw [realRank_cons] at hp
      simp only [RealBlock.rank] at hp
      omega

theorem realInducedBlockAt_append_right :
    ∀ (A B : List RealBlock) (p : ℕ),
      realInducedBlockAt (A ++ B) (realRank A + p) = realInducedBlockAt B p
  | [], _, p => by simp [realRank_nil]
  | .character d :: A, B, p => by
      have h : realRank (.character d :: A) + p = (realRank A + p) + 1 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [List.cons_append, h]
      exact realInducedBlockAt_append_right A B p
  | .induced d :: A, B, p => by
      have h : realRank (.induced d :: A) + p = (realRank A + p) + 2 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [List.cons_append, h]
      exact realInducedBlockAt_append_right A B p

end Append

/-! ## Lists of classes -/

section Flat

open RealLeviChart

variable {c : ℕ}

/-- The concatenation of the class lists `dss 0, …, dss (c-1)`. -/
def flat (dss : Fin c → List RealBlock) : List RealBlock := (List.ofFn dss).flatten

/-- The class sizes. -/
def sz (dss : Fin c → List RealBlock) : Fin c → ℕ := fun i => realRank (dss i)

theorem flat_succ (dss : Fin (c + 1) → List RealBlock) :
    flat dss = dss 0 ++ flat fun i => dss i.succ := by
  simp [flat, List.ofFn_succ]

theorem realRank_flat : ∀ {c : ℕ} (dss : Fin c → List RealBlock),
    realRank (flat dss) = ∑ i, sz dss i
  | 0, _ => rfl
  | c + 1, dss => by
      rw [flat_succ, realRank_append, realRank_flat, Fin.sum_univ_succ]
      rfl

theorem start_zero' (s : Fin c → ℕ) : start s 0 = 0 := by simp [start]

theorem start_succ' (s : Fin (c + 1) → ℕ) (i : ℕ) :
    start s (i + 1) = s 0 + start (fun j : Fin c => s j.succ) i := by
  rw [start, Finset.sum_range_succ', start, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k < c
    · have hk' : k + 1 < c + 1 := by omega
      simp only [hk, hk', ↓reduceDIte]
      rfl
    · have hk' : ¬ k + 1 < c + 1 := by omega
      simp only [hk, hk', ↓reduceDIte]

theorem realPositionCharacter_flat : ∀ {c : ℕ} (dss : Fin c → List RealBlock) (i : Fin c)
    (a : ℕ), a < sz dss i →
      realPositionCharacter (flat dss) (start (sz dss) i + a) = realPositionCharacter (dss i) a
  | 0, _, i, _, _ => i.elim0
  | c + 1, dss, i, a, ha => by
      rw [flat_succ]
      induction i using Fin.cases with
      | zero =>
          rw [Fin.val_zero, start_zero', zero_add]
          exact realPositionCharacter_append_left _ _ a ha
      | succ i =>
          rw [Fin.val_succ, start_succ', add_assoc]
          have e : sz dss 0 = realRank (dss 0) := rfl
          rw [e, realPositionCharacter_append_right]
          exact realPositionCharacter_flat (fun j => dss j.succ) i a ha

theorem realInducedBlockAt_flat : ∀ {c : ℕ} (dss : Fin c → List RealBlock) (i : Fin c)
    (a : ℕ), a < sz dss i →
      realInducedBlockAt (flat dss) (start (sz dss) i + a) = realInducedBlockAt (dss i) a
  | 0, _, i, _, _ => i.elim0
  | c + 1, dss, i, a, ha => by
      rw [flat_succ]
      induction i using Fin.cases with
      | zero =>
          rw [Fin.val_zero, start_zero', zero_add]
          exact realInducedBlockAt_append_left _ _ a ha
      | succ i =>
          rw [Fin.val_succ, start_succ', add_assoc]
          have e : sz dss 0 = realRank (dss 0) := rfl
          rw [e, realInducedBlockAt_append_right]
          exact realInducedBlockAt_flat (fun j => dss j.succ) i a ha

/-- The twist of the class `i`: `s_i = start_i - (N - sz_i)/2`. -/
def shift (dss : Fin c → List RealBlock) (i : Fin c) : ℝ :=
  (start (sz dss) i : ℝ) - (((∑ j, sz dss j : ℕ) : ℝ) - (sz dss i : ℝ)) / 2

/-- The twisted class list `|·|^{s_i} ⊗ dss i`. -/
def cl (dss : Fin c → List RealBlock) (i : Fin c) : List RealBlock :=
  twist (shift dss i) (dss i)

theorem realRank_cl (dss : Fin c → List RealBlock) (i : Fin c) :
    realRank (cl dss i) = sz dss i :=
  realRank_twist _ _

end Flat

/-! ## The block embeddings -/

section Emb

open RealLeviChart

variable {c : ℕ} (sz : Fin c → ℕ) (i : Fin c)

/-- The matrix `diag(1, …, y, …, 1)` with `y` in the block `i`. -/
def embA (y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ :=
  blockDiagHom sz (Pi.mulSingle i y)

/-- The block diagonal matrices `diag(A_0, …, A_{c-1})`, as a linear map. -/
def blockDiagLin :
    (∀ j, Matrix (Fin (sz j)) (Fin (sz j)) ℝ) →ₗ[ℝ]
      Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ where
  toFun := blockDiagHom sz
  map_add' := map_add _
  map_smul' r A := by
    ext p q
    simp [blockDiagHom_apply]

/-- The embedding `Y ↦ diag(0, …, Y, …, 0)` of `𝔤𝔩_{sz_i}(ℝ)` as the block `i`. -/
def embL : Matrix (Fin (sz i)) (Fin (sz i)) ℝ →ₗ[ℝ] Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ :=
  (blockDiagLin sz).comp (LinearMap.single ℝ (fun j => Matrix (Fin (sz j)) (Fin (sz j)) ℝ) i)

theorem embL_apply (Y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    embL sz i Y = blockDiagHom sz (Pi.single i Y) :=
  rfl

theorem embA_eq (y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    embA sz i y = 1 + embL sz i (y - 1) := by
  rw [embA, embL_apply, ← map_one (blockDiagHom sz), ← map_add]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem embA_one : embA sz i 1 = 1 := by
  simp [embA]

theorem embA_mul (x y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    embA sz i (x * y) = embA sz i x * embA sz i y := by
  rw [embA, embA, embA, ← map_mul, Pi.mulSingle_mul]

theorem embA_eq_add :
    embA sz i = fun y => (1 - embL sz i 1) + LinearMap.toContinuousLinearMap (embL sz i) y := by
  funext y
  rw [embA_eq, map_sub, LinearMap.coe_toContinuousLinearMap']
  abel

theorem hasFDerivAt_embA (y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    HasFDerivAt (embA sz i) (LinearMap.toContinuousLinearMap (embL sz i)) y := by
  rw [embA_eq_add]
  exact (LinearMap.toContinuousLinearMap (embL sz i)).hasFDerivAt.const_add _

theorem contDiff_embA : ContDiff ℝ ∞ (embA sz i) := by
  rw [embA_eq_add]
  exact contDiff_const.add (LinearMap.toContinuousLinearMap (embL sz i)).contDiff

/-- The embedding of `GL_{sz_i}(ℝ)` in `GL_N(ℝ)` as the block `i`. -/
def emb : Langlands.GeneralLinear (sz i) ℝ →* Langlands.GeneralLinear (∑ j, sz j) ℝ :=
  (blockDiagGL sz).comp (MonoidHom.mulSingle (fun j => Langlands.GeneralLinear (sz j) ℝ) i)

theorem emb_eq (x : Langlands.GeneralLinear (sz i) ℝ) :
    emb sz i x = blockDiagGL sz (Pi.mulSingle i x) :=
  rfl

theorem emb_val (x : Langlands.GeneralLinear (sz i) ℝ) :
    ((emb sz i x : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
      Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) =
      embA sz i (x : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) := by
  rw [emb_eq, blockDiagGL_val, embA]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem emb_mem_unitaryCompact {x : Langlands.GeneralLinear (sz i) ℝ}
    (hx : x ∈ unitaryCompact ℝ (sz i)) : emb sz i x ∈ unitaryCompact ℝ (∑ j, sz j) := by
  have h := blockDiagGL_mem_unitaryCompact (sz := sz)
    (Pi.mulSingle (M := fun j => unitaryCompact ℝ (sz j)) i ⟨x, hx⟩)
  convert h using 2
  rw [emb_eq]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- The diagonal entries `a` placed at the positions of the block `i`, and `1` elsewhere. -/
def pad (a : Fin (sz i) → ℝˣ) (q : Fin (∑ j, sz j)) : ℝˣ :=
  Pi.mulSingle (M := fun j => Fin (sz j) → ℝˣ) i a (finSigmaFinEquiv.symm q).1
    (finSigmaFinEquiv.symm q).2

theorem emb_diagonalUnits (a : Fin (sz i) → ℝˣ) :
    emb sz i (Iwasawa.diagonalUnits a) = Iwasawa.diagonalUnits (pad sz i a) := by
  ext : 1
  rw [emb_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, embA, blockDiagHom_apply]
  have h : (Pi.mulSingle i (diagonal fun b => ((a b : ℝˣ) : ℝ)) :
      ∀ j, Matrix (Fin (sz j)) (Fin (sz j)) ℝ) =
      fun j => diagonal fun b =>
        ((Pi.mulSingle (M := fun j => Fin (sz j) → ℝˣ) i a j b : ℝˣ) : ℝ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [h, Matrix.blockDiagonal'_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rfl

theorem emb_mem_upperUnipotent {x : Langlands.GeneralLinear (sz i) ℝ}
    (hx : x ∈ upperUnipotent (sz i) ℝ) : emb sz i x ∈ upperUnipotent (∑ j, sz j) ℝ := by
  refine ⟨fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨⟨j, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    obtain ⟨⟨k, b⟩, rfl⟩ := finSigmaFinEquiv.surjective q
    show ((emb sz i x : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
      Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) _ _ = 0
    rw [emb_val, embA, blockDiagHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    by_cases hjk : j = k
    · subst hjk
      rw [Matrix.blockDiagonal'_apply_eq]
      have hab : b < a := by
        have h1 := Fin.lt_def.mp hpq
        change ((pos sz j b : Fin (∑ j, sz j)) : ℕ) < (pos sz j a : ℕ) at h1
        rw [val_pos, val_pos] at h1
        exact Fin.lt_def.mpr (by omega)
      by_cases hji : j = i
      · subst hji
        rw [Pi.mulSingle_eq_same]
        exact hx.1 hab
      · rw [Pi.mulSingle_eq_of_ne hji]
        exact Matrix.one_apply_ne (ne_of_gt hab)
    · exact Matrix.blockDiagonal'_apply_ne _ _ _ hjk
  · obtain ⟨⟨j, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    show ((emb sz i x : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
      Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) _ _ = 1
    rw [emb_val, embA, blockDiagHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]
    by_cases hji : j = i
    · subst hji
      rw [Pi.mulSingle_eq_same]
      exact hx.2 a
    · rw [Pi.mulSingle_eq_of_ne hji]
      exact Matrix.one_apply_eq a

/-- `diag(g_0, …, x, …, g_{c-1}) = diag(1, …, x, …, 1) · diag(g_0, …, 1, …, g_{c-1})`. -/
theorem emb_mul_blockDiagGL_update (g : ∀ j, Langlands.GeneralLinear (sz j) ℝ)
    (x : Langlands.GeneralLinear (sz i) ℝ) :
    emb sz i x * blockDiagGL sz (Function.update g i 1) = blockDiagGL sz (Function.update g i x) := by
  rw [emb_eq, ← map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

theorem blockDiagGL_update_mul_emb (g : ∀ j, Langlands.GeneralLinear (sz j) ℝ)
    (x : Langlands.GeneralLinear (sz i) ℝ) :
    blockDiagGL sz (Function.update g i 1) * emb sz i x = blockDiagGL sz (Function.update g i x) := by
  rw [emb_eq, ← map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- `diag(g_0, …, 1, …, g_{c-1})` commutes with `diag(0, …, Y, …, 0)`. -/
theorem blockDiagGL_update_mul_embL (g : ∀ j, Langlands.GeneralLinear (sz j) ℝ)
    (Y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    ((blockDiagGL sz (Function.update g i 1) : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
        Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) * embL sz i Y =
      embL sz i Y * ((blockDiagGL sz (Function.update g i 1) :
        Langlands.GeneralLinear (∑ j, sz j) ℝ) : Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) := by
  rw [blockDiagGL_val, embL_apply, ← map_mul, ← map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

theorem blockDiagGL_update_conj_embL (g : ∀ j, Langlands.GeneralLinear (sz j) ℝ)
    (Y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    ((blockDiagGL sz (Function.update g i 1) : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
        Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) * embL sz i Y *
      (((blockDiagGL sz (Function.update g i 1))⁻¹ : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
        Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) = embL sz i Y := by
  rw [blockDiagGL_update_mul_embL, mul_assoc, Units.mul_inv, mul_one]

/-- The embedding of `O(sz_i)` in `O(N)` as the block `i`. -/
def embK (k : Matrix.unitaryGroup (Fin (sz i)) ℝ) : Matrix.unitaryGroup (Fin (∑ j, sz j)) ℝ :=
  ⟨embA sz i (k : Matrix (Fin (sz i)) (Fin (sz i)) ℝ), by
    have h := emb_mem_unitaryCompact sz i (x := Unitary.toUnits k) k.2
    change ((emb sz i (Unitary.toUnits k) : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
      Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) ∈ Matrix.unitaryGroup _ ℝ at h
    rw [emb_val] at h
    exact h⟩

theorem toUnits_embK (k : Matrix.unitaryGroup (Fin (sz i)) ℝ) :
    (Unitary.toUnits (embK sz i k) : Langlands.GeneralLinear (∑ j, sz j) ℝ) =
      emb sz i (Unitary.toUnits k) :=
  Units.ext (emb_val sz i (Unitary.toUnits k)).symm

/-- The complexified embedding `ℂ ⊗ 𝔤𝔩_{sz_i}(ℝ) → ℂ ⊗ 𝔤𝔩_N(ℝ)`. -/
def embLC : (ℂ ⊗[ℝ] Matrix (Fin (sz i)) (Fin (sz i)) ℝ) →ₗ[ℂ]
    ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ :=
  (embL sz i).baseChange ℂ

theorem embLC_tmul (z : ℂ) (Y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    embLC sz i (z ⊗ₜ Y) = z ⊗ₜ embL sz i Y :=
  LinearMap.baseChange_tmul _ _ _

end Emb

/-! ## Smoothness and derivatives of restrictions to a block -/

section Smooth

open RealLeviChart

variable {c : ℕ} (sz : Fin c → ℕ) (i : Fin c)

theorem contMDiff_comp_emb {f : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ (∑ j, sz j)) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℝ (sz i)) 𝓘(ℝ, ℂ) ∞ (fun x => f (emb sz i x)) := by
  refine contMDiff_of_contDiffOn (ψ := fun y => unitsExtension f (embA sz i y)) ?_ ?_
  · refine (contDiffOn_unitsExtension hf).comp (contDiff_embA sz i).contDiffOn ?_
    rintro _ ⟨g, rfl⟩
    show IsUnit (embA sz i (g : Matrix (Fin (sz i)) (Fin (sz i)) ℝ))
    rw [← emb_val]
    exact Units.isUnit _
  · intro g
    rw [← emb_val, unitsExtension_val]

theorem rightDerivative_comp_emb {f : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ (∑ j, sz j)) 𝓘(ℝ, ℂ) ∞ f)
    (Y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) (x : Langlands.GeneralLinear (sz i) ℝ) :
    rightDerivative (matrixModel ℝ (sz i)) Y (fun y => f (emb sz i y)) x =
      rightDerivative (matrixModel ℝ (∑ j, sz j)) (embL sz i Y) f (emb sz i x) := by
  rw [rightDerivative_eq_fderiv_mul_left (contMDiff_comp_emb sz i hf),
    rightDerivative_eq_fderiv_mul_left hf]
  set G : Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ → ℂ := fun z =>
    unitsExtension f (((emb sz i x : Langlands.GeneralLinear (∑ j, sz j) ℝ) :
      Matrix (Fin (∑ j, sz j)) (Fin (∑ j, sz j)) ℝ) * z) with hG
  have hev : (fun y : Matrix (Fin (sz i)) (Fin (sz i)) ℝ =>
      unitsExtension (fun y => f (emb sz i y)) ((x : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) * y)) =ᶠ[nhds 1]
      G ∘ embA sz i := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (isUnit_one (M := Matrix (Fin (sz i)) (Fin (sz i)) ℝ))]
      with y hy
    obtain ⟨u, rfl⟩ := hy
    rw [← Units.val_mul, unitsExtension_val, Function.comp_apply, hG]
    simp only
    rw [← emb_val, ← Units.val_mul, unitsExtension_val, map_mul]
  rw [hev.fderiv_eq]
  have hGd : DifferentiableAt ℝ G (embA sz i 1) := by
    rw [embA_one]
    exact differentiableAt_unitsExtension_mul_left hf _
  rw [fderiv_comp 1 hGd (hasFDerivAt_embA sz i 1).differentiableAt,
    (hasFDerivAt_embA sz i 1).fderiv, embA_one, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap']

end Smooth

/-! ## Free algebras acting compatibly -/

section Free

variable {ι V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A linear map intertwining the generators intertwines the free algebra actions. -/
theorem lift_intertwine (T : V →ₗ[ℂ] W) (g : ι → Module.End ℂ V) (h : ι → Module.End ℂ W)
    (hgh : ∀ x v, T (g x v) = h x (T v)) (a : FreeAlgebra ℂ ι) (v : V) :
    T (FreeAlgebra.lift ℂ g a v) = FreeAlgebra.lift ℂ h a (T v) := by
  induction a using FreeAlgebra.induction generalizing v with
  | grade0 r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | grade1 x =>
    simp only [FreeAlgebra.lift_ι_apply, hgh]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- A submodule stable under the generators is stable under the free algebra. -/
theorem lift_mem (g : ι → Module.End ℂ V) (U : Submodule ℂ V) (hU : ∀ x, ∀ v ∈ U, g x v ∈ U)
    (a : FreeAlgebra ℂ ι) {v : V} (hv : v ∈ U) : FreeAlgebra.lift ℂ g a v ∈ U := by
  induction a using FreeAlgebra.induction generalizing v with
  | grade0 r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact U.smul_mem r hv
  | grade1 x =>
    rw [FreeAlgebra.lift_ι_apply]
    exact hU x v hv
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply]
    exact ha (hb hv)
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem (ha hv) (hb hv)

end Free

/-! ## Slices of the dual space -/

section Slice

open RealLeviChart RealPrincipalSeriesDuality PartialJacquet RealLeviDuality

variable {c : ℕ} (dss : Fin c → List RealBlock) (i : Fin c)

theorem pad_finSigmaFinEquiv (a : Fin (sz dss i) → ℝˣ) (j : Fin c) (b : Fin (sz dss j)) :
    pad (sz dss) i a (finSigmaFinEquiv ⟨j, b⟩) =
      Pi.mulSingle (M := fun j => Fin (sz dss j) → ℝˣ) i a j b := by
  rw [pad, Equiv.symm_apply_apply]

/-- The character of the padded diagonal entries is the character of the twisted class list. -/
theorem principalSeriesCharacter_pad (a : Fin (sz dss i) → ℝˣ) :
    principalSeriesCharacter ℝ (∑ j, sz dss j) (dualChar (realPositionCharacter (flat dss)))
        (pad (sz dss) i a) =
      principalSeriesCharacter ℝ (sz dss i) (dualChar (realPositionCharacter (cl dss i))) a := by
  rw [principalSeriesCharacter, ← Equiv.prod_comp finSigmaFinEquiv, Fintype.prod_sigma,
    Fintype.prod_eq_single i]
  · rw [principalSeriesCharacter]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hv : ((finSigmaFinEquiv (⟨i, b⟩ : Σ j, Fin (sz dss j)) : Fin (∑ j, sz dss j)) : ℕ) =
        start (sz dss) i + b := val_pos (sz dss) i b
    rw [pad_finSigmaFinEquiv, Pi.mulSingle_eq_same, hv, dualChar, dualChar,
      realPositionCharacter_flat dss i b b.2, cl, realPositionCharacter_twist _ _ _ b.2,
      Module.finrank_self, pow_one, Real.norm_eq_abs, mul_inv, mul_assoc, ← Complex.cpow_neg,
      ← abs_cpow_add]
    congr 2
    simp only [shift]
    push_cast
    ring
  · intro j hj
    refine Finset.prod_eq_one fun b _ => ?_
    rw [pad_finSigmaFinEquiv, Pi.mulSingle_eq_of_ne hj, Pi.one_apply, dualChar,
      realPositionCharacter_one, inv_one, one_mul, Units.val_one, norm_one, one_pow,
      Complex.ofReal_one, Complex.one_cpow]

theorem slice_mem {u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ}
    (hu : u ∈ DualSpace (∑ j, sz dss j) (flat dss)) :
    (fun x => u (emb (sz dss) i x)) ∈ DualSpace (sz dss i) (cl dss i) := by
  refine ⟨⟨contMDiff_comp_emb (sz dss) i hu.1.1, fun a n g => ?_⟩, ?_⟩
  · have h := hu.1.2 (pad (sz dss) i a) ⟨_, emb_mem_upperUnipotent (sz dss) i n.2⟩
      (emb (sz dss) i g)
    rw [principalSeriesCharacter_pad] at h
    show u (emb (sz dss) i (Iwasawa.diagonalUnits a * (n : Langlands.GeneralLinear (sz dss i) ℝ) *
      g)) = _
    rw [map_mul, map_mul, emb_diagonalUnits]
    exact h
  · have hfin : u ∈ kFiniteVectors (Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear (∑ j, sz dss j) ℝ)) (unitaryCompact ℝ (∑ j, sz dss j)) := hu.2
    show (fun x => u (emb (sz dss) i x)) ∈ kFiniteVectors (Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear (sz dss i) ℝ)) (unitaryCompact ℝ (sz dss i))
    rw [mem_kFiniteVectors_iff] at hfin ⊢
    have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ (sz dss i) =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (sz dss i) ℝ)
          (k : Langlands.GeneralLinear (sz dss i) ℝ) (fun x => u (emb (sz dss) i x))) ≤
        (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ (∑ j, sz dss j) =>
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (∑ j, sz dss j) ℝ)
            (k : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) u)).map
          (LinearMap.funLeft ℂ ℂ (emb (sz dss) i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine ⟨_, Submodule.subset_span ⟨⟨emb (sz dss) i k, emb_mem_unitaryCompact (sz dss) i k.2⟩,
        rfl⟩, ?_⟩
      funext x
      show u (emb (sz dss) i x * emb (sz dss) i k) = u (emb (sz dss) i (x * k))
      rw [map_mul]
    exact Submodule.finiteDimensional_of_le hle

/-- The slice `u ↦ u ∘ emb_i` of the dual space to the class `i`. -/
def slice : DualSpace (∑ j, sz dss j) (flat dss) →ₗ[ℂ] DualSpace (sz dss i) (cl dss i) where
  toFun u := ⟨fun x => (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) (emb (sz dss) i x),
    slice_mem dss i u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_apply (u : DualSpace (∑ j, sz dss j) (flat dss))
    (x : Langlands.GeneralLinear (sz dss i) ℝ) :
    (slice dss i u : Langlands.GeneralLinear (sz dss i) ℝ → ℂ) x =
      (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) (emb (sz dss) i x) :=
  rfl

/-- The representation of `O(N)` on the global dual space. -/
abbrev repG : Representation ℂ (Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ)
    (DualSpace (∑ j, sz dss j) (flat dss)) :=
  principalSeriesRep ℝ (∑ j, sz dss j) (dualChar (realPositionCharacter (flat dss)))

/-- The Lie algebra action on the global dual space. -/
abbrev lieG : (ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ) →ₗ⁅ℂ⁆
    Module.End ℂ (DualSpace (∑ j, sz dss j) (flat dss)) :=
  principalSeriesLie ℝ (∑ j, sz dss j) (dualChar (realPositionCharacter (flat dss)))

/-- The representation of `O(sz_i)` on the class dual space. -/
abbrev repC : Representation ℂ (Matrix.unitaryGroup (Fin (sz dss i)) ℝ)
    (DualSpace (sz dss i) (cl dss i)) :=
  principalSeriesRep ℝ (sz dss i) (dualChar (realPositionCharacter (cl dss i)))

/-- The Lie algebra action on the class dual space. -/
abbrev lieC : (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ) →ₗ⁅ℂ⁆
    Module.End ℂ (DualSpace (sz dss i) (cl dss i)) :=
  principalSeriesLie ℝ (sz dss i) (dualChar (realPositionCharacter (cl dss i)))

/-- The global generators attached to the class `i`: `ρ(ι_i k)` and `π(ι_i X)`. -/
def gensG : Matrix.unitaryGroup (Fin (sz dss i)) ℝ ⊕
      (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ) →
    Module.End ℂ (DualSpace (∑ j, sz dss j) (flat dss)) :=
  GKModuleDensity.gens (repG dss) (lieG dss) ∘ Sum.map (embK (sz dss) i) (embLC (sz dss) i)

theorem gensG_inl (k : Matrix.unitaryGroup (Fin (sz dss i)) ℝ) :
    gensG dss i (Sum.inl k) = repG dss (embK (sz dss) i k) :=
  rfl

theorem gensG_inr (X : ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ) :
    gensG dss i (Sum.inr X) = lieG dss (embLC (sz dss) i X) :=
  rfl

theorem slice_rep (k : Matrix.unitaryGroup (Fin (sz dss i)) ℝ)
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    slice dss i (repG dss (embK (sz dss) i k) u) = repC dss i k (slice dss i u) := by
  apply Subtype.ext
  funext x
  show (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
      (emb (sz dss) i x * (Unitary.toUnits (embK (sz dss) i k) :
        Langlands.GeneralLinear (∑ j, sz dss j) ℝ)) =
    (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) (emb (sz dss) i (x * Unitary.toUnits k))
  rw [toUnits_embK, map_mul]

theorem slice_lie (X : ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ)
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    slice dss i (lieG dss (embLC (sz dss) i X) u) = lieC dss i X (slice dss i u) := by
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    apply Subtype.ext
    funext x
    rw [embLC_tmul, slice_apply, coe_principalSeriesLie_tmul, coe_principalSeriesLie_tmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ((slice dss i u : DualSpace (sz dss i) (cl dss i)) :
        Langlands.GeneralLinear (sz dss i) ℝ → ℂ) = fun y =>
          (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) (emb (sz dss) i y) from rfl,
      rightDerivative_comp_emb (sz dss) i u.2.1.1 Y x]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY]

theorem slice_gensG (x : Matrix.unitaryGroup (Fin (sz dss i)) ℝ ⊕
      (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ))
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    slice dss i (gensG dss i x u) = GKModuleDensity.gens (repC dss i) (lieC dss i) x (slice dss i u) := by
  rcases x with k | X
  · rw [gensG_inl, slice_rep]
    rfl
  · rw [gensG_inr, slice_lie]
    rfl

/-- Slicing intertwines the free algebra actions. -/
theorem slice_lift (a : FreeAlgebra ℂ (Matrix.unitaryGroup (Fin (sz dss i)) ℝ ⊕
      (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ)))
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    slice dss i (FreeAlgebra.lift ℂ (gensG dss i) a u) =
      FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss i) (lieC dss i)) a (slice dss i u) :=
  lift_intertwine _ _ _ (slice_gensG dss i) a u

variable {dss i}

theorem repG_comm_lieG {g : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    {m : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ}
    (hm : (Unitary.toUnits m : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) =
      blockDiagGL (sz dss) (Function.update g i 1))
    (X : ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ)
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    repG dss m (lieG dss (embLC (sz dss) i X) u) = lieG dss (embLC (sz dss) i X) (repG dss m u) := by
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    apply Subtype.ext
    rw [principalSeriesRep_apply_coe, embLC_tmul, coe_principalSeriesLie_tmul,
      coe_principalSeriesLie_tmul, principalSeriesRep_apply_coe, map_smul,
      rightTranslation_rightDerivative u.2.1.1, hm, blockDiagGL_update_conj_embL]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY]

theorem repG_comm_gensG {g : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    {m : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ}
    (hm : (Unitary.toUnits m : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) =
      blockDiagGL (sz dss) (Function.update g i 1))
    (x : Matrix.unitaryGroup (Fin (sz dss i)) ℝ ⊕
      (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ))
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    repG dss m (gensG dss i x u) = gensG dss i x (repG dss m u) := by
  rcases x with k | X
  · rw [gensG_inl]
    apply Subtype.ext
    funext y
    show (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
        (y * (Unitary.toUnits m : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
          (Unitary.toUnits (embK (sz dss) i k) : Langlands.GeneralLinear (∑ j, sz dss j) ℝ)) =
      (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
        (y * (Unitary.toUnits (embK (sz dss) i k) : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
          (Unitary.toUnits m : Langlands.GeneralLinear (∑ j, sz dss j) ℝ))
    rw [toUnits_embK, hm, mul_assoc, mul_assoc, blockDiagGL_update_mul_emb,
      emb_mul_blockDiagGL_update]
  · rw [gensG_inr]
    exact repG_comm_lieG hm X u

theorem repG_comm_lift {g : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    {m : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ}
    (hm : (Unitary.toUnits m : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) =
      blockDiagGL (sz dss) (Function.update g i 1))
    (a : FreeAlgebra ℂ (Matrix.unitaryGroup (Fin (sz dss i)) ℝ ⊕
      (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ)))
    (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    repG dss m (FreeAlgebra.lift ℂ (gensG dss i) a u) =
      FreeAlgebra.lift ℂ (gensG dss i) a (repG dss m u) :=
  lift_intertwine _ _ _ (repG_comm_gensG hm) a u

end Slice

end RealLeviSlices

end Langlands.Archimedean
