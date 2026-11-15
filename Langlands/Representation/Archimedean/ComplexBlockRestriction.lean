import Langlands.Representation.Archimedean.ComplexSwapJacquetProof
import Langlands.Representation.Archimedean.ComplexSwapJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducible

/-!
# Restriction of complex principal series to a `GL_2(ℂ)` block

For `ds = pre ++ d :: e :: post` with `pre.length = p`, restriction along the block embedding
`GL_2(ℂ) → GL_n(ℂ)` at the positions `p`, `p + 1` maps the `U(n)`-finite functions of the
standard module of `ds` to the `U(2)`-finite functions of the standard module of the pair
`d`, `e` with exponents shifted by `(n - 2 - 2p)/2` (`res`), compatibly with `U(2)` and
`𝔤𝔩_2(ℂ)`. The rank-one Jacquet functional of `ComplexSwapJacquetFunctional` at the positions
`p`, `p + 1` factors through `res` (`lamTwo_res`). Hence, if `d`, `e` are not linked and the
`GL_2(ℂ)` standard module is irreducible, every `(𝔤𝔩_n(ℂ), U(n))`-stable subspace on which the
functional vanishes is zero (`eq_bot_of_lamN`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexBlock

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ} (p : ℕ) (hp : p + 2 ≤ n)

/-! ## The block embedding on matrices -/

/-- The positions `p` and `p + 1`. -/
def pos (k : Fin 2) : Fin n := ⟨p + k, by omega⟩

theorem pos_val (k : Fin 2) : ((pos p hp k : Fin n) : ℕ) = p + k := rfl

theorem pos_injective : Function.Injective (pos p hp) := by
  intro k l h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simp only [pos_val] at h'
  omega

theorem pos_lt_pos_iff (k l : Fin 2) : pos p hp k < pos p hp l ↔ k < l := by
  rw [Fin.lt_def, Fin.lt_def, pos_val, pos_val]
  omega

theorem pos_eq_pos_iff (k l : Fin 2) : pos p hp k = pos p hp l ↔ k = l :=
  (pos_injective p hp).eq_iff

/-- Every position is in the block or not. -/
theorem mem_range_or (a : Fin n) : (∃ k, a = pos p hp k) ∨ ∀ k, a ≠ pos p hp k := by
  by_cases h : ∃ k, a = pos p hp k
  · exact Or.inl h
  · push Not at h
    exact Or.inr h

/-- The `n × 2` matrix of the inclusion of the coordinates `p`, `p + 1`. -/
def incl : Matrix (Fin n) (Fin 2) ℂ := Matrix.of fun a k => if a = pos p hp k then 1 else 0

/-- `X ↦ P X Pᵀ`: the `2 × 2` matrix `X` in rows and columns `p`, `p + 1`, zero elsewhere. -/
def lin (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  incl p hp * X * (incl p hp)ᵀ

theorem lin_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin n) :
    lin p hp X a b = ∑ l, (∑ k, (if a = pos p hp k then 1 else 0) * X k l) *
      (if b = pos p hp l then 1 else 0) := by
  simp only [lin, Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]

theorem lin_apply_pos (X : Matrix (Fin 2) (Fin 2) ℂ) (k l : Fin 2) :
    lin p hp X (pos p hp k) (pos p hp l) = X k l := by
  rw [lin_apply]
  simp [pos_eq_pos_iff]

theorem lin_apply_left (X : Matrix (Fin 2) (Fin 2) ℂ) {a : Fin n} (ha : ∀ k, a ≠ pos p hp k)
    (b : Fin n) : lin p hp X a b = 0 := by
  rw [lin_apply]
  simp [ha]

theorem lin_apply_right (X : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin n) {b : Fin n}
    (hb : ∀ k, b ≠ pos p hp k) : lin p hp X a b = 0 := by
  rw [lin_apply]
  simp [hb]

theorem inclT_mul_incl : (incl p hp)ᵀ * incl p hp = 1 := by
  ext k l
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply]
  simp [pos_eq_pos_iff, eq_comm]

theorem lin_mul (X Y : Matrix (Fin 2) (Fin 2) ℂ) : lin p hp X * lin p hp Y = lin p hp (X * Y) := by
  simp only [lin]
  calc incl p hp * X * (incl p hp)ᵀ * (incl p hp * Y * (incl p hp)ᵀ)
      = incl p hp * X * ((incl p hp)ᵀ * incl p hp) * Y * (incl p hp)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = incl p hp * (X * Y) * (incl p hp)ᵀ := by
        rw [inclT_mul_incl, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem lin_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) : lin p hp (X + Y) = lin p hp X + lin p hp Y := by
  simp only [lin, Matrix.mul_add, Matrix.add_mul]

theorem lin_sub (X Y : Matrix (Fin 2) (Fin 2) ℂ) : lin p hp (X - Y) = lin p hp X - lin p hp Y := by
  simp only [lin, Matrix.mul_sub, Matrix.sub_mul]

theorem lin_zero : lin p hp (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [lin]

theorem lin_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : lin p hp (c • X) = c • lin p hp X := by
  simp only [lin, Matrix.mul_smul, Matrix.smul_mul]

theorem lin_single (k l : Fin 2) (c : ℂ) :
    lin p hp (Matrix.single k l c) = Matrix.single (pos p hp k) (pos p hp l) c := by
  ext a b
  rcases mem_range_or p hp a with ⟨k', rfl⟩ | ha
  · rcases mem_range_or p hp b with ⟨l', rfl⟩ | hb
    · rw [lin_apply_pos]
      simp [Matrix.single_apply, pos_eq_pos_iff]
    · rw [lin_apply_right p hp _ _ hb]
      simp [(hb l).symm]
  · rw [lin_apply_left p hp _ ha]
    simp [(ha k).symm]

theorem incl_conjTranspose : (incl p hp)ᴴ = (incl p hp)ᵀ := by
  ext k a
  simp [incl, Matrix.conjTranspose_apply, apply_ite star]

theorem star_lin (X : Matrix (Fin 2) (Fin 2) ℂ) : star (lin p hp X) = lin p hp (star X) := by
  ext a b
  rw [Matrix.star_apply]
  rcases mem_range_or p hp a with ⟨k, rfl⟩ | ha
  · rcases mem_range_or p hp b with ⟨l, rfl⟩ | hb
    · rw [lin_apply_pos, lin_apply_pos, Matrix.star_apply]
    · rw [lin_apply_left p hp _ hb, lin_apply_right p hp _ _ hb, star_zero]
  · rw [lin_apply_right p hp _ _ ha, lin_apply_left p hp _ ha, star_zero]

/-! ## The block embedding `GL_2(ℂ) → GL_n(ℂ)` -/

/-- `M ↦ P M Pᵀ + (1 - P Pᵀ)`: the identity matrix with the block `M` in rows and columns
`p`, `p + 1`. -/
def blockMat (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  lin p hp M + (1 - lin p hp 1)

theorem lin_mul_compl (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lin p hp M * (1 - lin p hp 1) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lin_mul, Matrix.mul_one, sub_self]

theorem compl_mul_lin (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - lin p hp 1) * lin p hp M = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lin_mul, Matrix.one_mul, sub_self]

theorem compl_mul_compl : (1 - lin p hp 1) * (1 - lin p hp 1) = (1 - lin p hp 1 :
    Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.sub_mul, Matrix.one_mul, lin_mul_compl, sub_zero]

theorem blockMat_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat p hp M * blockMat p hp N = blockMat p hp (M * N) := by
  rw [blockMat, blockMat, blockMat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, lin_mul,
    lin_mul_compl, compl_mul_lin, compl_mul_compl, add_zero, zero_add]

theorem blockMat_one : blockMat p hp (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [blockMat, add_sub_cancel]

theorem blockMat_mul_lin (M X : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat p hp M * lin p hp X = lin p hp (M * X) := by
  rw [blockMat, Matrix.add_mul, lin_mul, compl_mul_lin, add_zero]

theorem blockMat_add_lin (M X : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat p hp (M + X) = blockMat p hp M + lin p hp X := by
  rw [blockMat, blockMat, lin_add]
  abel

theorem star_blockMat (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (blockMat p hp M) = blockMat p hp (star M) := by
  rw [blockMat, blockMat, star_add, star_sub, star_one, star_lin, star_lin, star_one]

theorem blockMat_apply_pos (M : Matrix (Fin 2) (Fin 2) ℂ) (k l : Fin 2) :
    blockMat p hp M (pos p hp k) (pos p hp l) = M k l := by
  simp only [blockMat, Matrix.add_apply, Matrix.sub_apply, lin_apply_pos, Matrix.one_apply,
    pos_eq_pos_iff]
  ring

theorem blockMat_apply_left (M : Matrix (Fin 2) (Fin 2) ℂ) {a : Fin n}
    (ha : ∀ k, a ≠ pos p hp k) (b : Fin n) :
    blockMat p hp M a b = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  simp only [blockMat, Matrix.add_apply, Matrix.sub_apply, lin_apply_left p hp _ ha]
  ring

theorem blockMat_apply_right (M : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin n) {b : Fin n}
    (hb : ∀ k, b ≠ pos p hp k) :
    blockMat p hp M a b = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  simp only [blockMat, Matrix.add_apply, Matrix.sub_apply, lin_apply_right p hp _ _ hb]
  ring

/-- `blockMat` as a monoid homomorphism. -/
def blockHom : Matrix (Fin 2) (Fin 2) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun := blockMat p hp
  map_one' := blockMat_one p hp
  map_mul' M N := (blockMat_mul p hp M N).symm

/-- The block embedding `GL_2(ℂ) → GL_n(ℂ)` at the positions `p`, `p + 1`. -/
def block : Langlands.GeneralLinear 2 ℂ →* Langlands.GeneralLinear n ℂ :=
  Units.map (blockHom p hp)

theorem block_val (g : Langlands.GeneralLinear 2 ℂ) :
    ((block p hp g : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      blockMat p hp (g : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

theorem block_mem_unitaryCompact {g : Langlands.GeneralLinear 2 ℂ}
    (hg : g ∈ unitaryCompact ℂ 2) : block p hp g ∈ unitaryCompact ℂ n := by
  rw [mem_unitaryCompact_iff] at hg ⊢
  rw [block_val, star_blockMat, blockMat_mul, hg, blockMat_one]

theorem block_mem_upperUnipotent {u : Langlands.GeneralLinear 2 ℂ}
    (hu : u ∈ upperUnipotent 2 ℂ) : block p hp u ∈ upperUnipotent n ℂ := by
  obtain ⟨hut, hud⟩ := hu
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · change blockMat p hp (u : Matrix (Fin 2) (Fin 2) ℂ) a b = 0
    have hne : a ≠ b := fun h => (lt_irrefl a) (h ▸ hab)
    rcases mem_range_or p hp a with ⟨k, rfl⟩ | ha
    · rcases mem_range_or p hp b with ⟨l, rfl⟩ | hb
      · rw [blockMat_apply_pos]
        exact hut ((pos_lt_pos_iff p hp l k).mp hab)
      · rw [blockMat_apply_right p hp _ _ hb, Matrix.one_apply_ne hne]
    · rw [blockMat_apply_left p hp _ ha, Matrix.one_apply_ne hne]
  · change blockMat p hp (u : Matrix (Fin 2) (Fin 2) ℂ) a a = 1
    rcases mem_range_or p hp a with ⟨k, rfl⟩ | ha
    · rw [blockMat_apply_pos]
      exact hud k
    · rw [blockMat_apply_left p hp _ ha, Matrix.one_apply_eq]

/-- The diagonal entries `a 0`, `a 1` at the positions `p`, `p + 1`, and `1` elsewhere. -/
def blockDiag (a : Fin 2 → ℂˣ) (j : Fin n) : ℂˣ :=
  if j = pos p hp 0 then a 0 else if j = pos p hp 1 then a 1 else 1

theorem blockDiag_pos (a : Fin 2 → ℂˣ) (k : Fin 2) : blockDiag p hp a (pos p hp k) = a k := by
  fin_cases k
  · simp [blockDiag]
  · simp [blockDiag, pos_eq_pos_iff]

theorem blockDiag_of_ne (a : Fin 2 → ℂˣ) {j : Fin n} (hj : ∀ k, j ≠ pos p hp k) :
    blockDiag p hp a j = 1 := by
  simp [blockDiag, hj 0, hj 1]

theorem block_diagonalUnits (a : Fin 2 → ℂˣ) :
    block p hp (Iwasawa.diagonalUnits a) = Iwasawa.diagonalUnits (blockDiag p hp a) := by
  apply Units.ext
  rw [block_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val]
  ext x y
  rcases mem_range_or p hp x with ⟨k, rfl⟩ | hx
  · rcases mem_range_or p hp y with ⟨l, rfl⟩ | hy
    · rw [blockMat_apply_pos, Matrix.diagonal_apply, Matrix.diagonal_apply]
      simp only [pos_eq_pos_iff, blockDiag_pos]
    · rw [blockMat_apply_right p hp _ _ hy, Matrix.diagonal_apply_ne _ (fun h => hy k h.symm),
        Matrix.one_apply_ne (fun h => hy k h.symm)]
  · by_cases hxy : x = y
    · subst hxy
      rw [blockMat_apply_left p hp _ hx, Matrix.diagonal_apply_eq, blockDiag_of_ne p hp a hx,
        Matrix.one_apply_eq, Units.val_one]
    · rw [blockMat_apply_left p hp _ hx, Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]


/-! ## Restriction of functions to the block -/

/-- Restriction of functions on `GL_n(ℂ)` along the block embedding. -/
def restrictLin : (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear 2 ℂ → ℂ) :=
  LinearMap.funLeft ℂ ℂ (block p hp)

theorem restrictLin_apply (f : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear 2 ℂ) :
    restrictLin p hp f g = f (block p hp g) :=
  rfl

theorem restrictLin_rightTranslation (k : Langlands.GeneralLinear 2 ℂ)
    (f : Langlands.GeneralLinear n ℂ → ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 2 ℂ) k (restrictLin p hp f) =
      restrictLin p hp
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (block p hp k) f) := by
  funext g
  change f (block p hp (g * k)) = f (block p hp g * block p hp k)
  rw [map_mul]

/-- `lin` as a complex-linear map. -/
def linL : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := lin p hp
  map_add' := lin_add p hp
  map_smul' := lin_smul p hp

theorem contDiff_blockMat : ContDiff ℝ ∞ (blockMat p hp) := by
  have h : blockMat p hp = fun M =>
      ((linL p hp).restrictScalars ℝ).toContinuousLinearMap M + (1 - lin p hp 1) := rfl
  rw [h]
  exact (ContinuousLinearMap.contDiff _).add contDiff_const

theorem isUnit_blockMat {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsUnit M) :
    IsUnit (blockMat p hp M) :=
  hM.map (blockHom p hp)

theorem contMDiff_restrictLin {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℂ 2) 𝓘(ℝ, ℂ) ∞ (restrictLin p hp f) := by
  refine contMDiff_of_contDiffOn (ψ := unitsExtension f ∘ blockMat p hp) ?_ fun g => ?_
  · exact (contDiffOn_unitsExtension hf).comp (contDiff_blockMat p hp).contDiffOn
      fun y hy => isUnit_blockMat p hp hy
  · rw [Function.comp_apply, ← block_val, unitsExtension_val]
    rfl

/-! ## The twisted characters of the block -/

/-- The exponent shift `(n - 2 - 2p)/2` relating the modulus characters of `GL_n` at the
positions `p`, `p + 1` and of `GL_2`. -/
def shift (n p : ℕ) : ℂ := ((n : ℂ) - 2 - 2 * (p : ℂ)) / 2

/-- The character `d` with exponent shifted by `s`. -/
def twist (s : ℂ) (d : ComplexCharacterData) : ComplexCharacterData :=
  characterOfParams d.weight (d.exponent + s)

theorem principalSeriesCharacter_blockDiag (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hpre : pre.length = p) (a : Fin 2 → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (pre ++ d :: e :: post))
        (blockDiag p hp a) =
      principalSeriesCharacter ℂ 2
        (complexPositionCharacter [twist (shift n p) d, twist (shift n p) e]) a := by
  have h0 : ((pos p hp 0 : Fin n) : ℕ) = pre.length := by rw [pos_val]; simp [hpre]
  have h1 : ((pos p hp 1 : Fin n) : ℕ) = pre.length + 1 := by rw [pos_val]; simp [hpre]
  have hne : pos p hp 0 ≠ pos p hp 1 := by rw [Ne, pos_eq_pos_iff]; decide
  rw [principalSeriesCharacter_eq, principalSeriesCharacter_eq, Fin.prod_univ_two,
    Finset.prod_eq_mul (pos p hp 0) (pos p hp 1) hne ?_ (by simp) (by simp)]
  · rw [blockDiag_pos, blockDiag_pos, h0, h1, ComplexSwapJacquet.posWeight_append_cons,
      ComplexSwapJacquet.posExponent_append_cons, ComplexSwapJacquet.posWeight_append_cons_succ,
      ComplexSwapJacquet.posExponent_append_cons_succ]
    simp only [Fin.val_zero, Fin.val_one, posWeight, posExponent, twist, characterOfParams_weight,
      characterOfParams_exponent, shift]
    congr 2
    · rw [← hpre]
      ring
    · rw [← hpre]
      push_cast
      ring
  · intro c _ hc
    rw [blockDiag_of_ne p hp a (fun k => by fin_cases k; exacts [hc.1, hc.2]), Units.val_one,
      ComplexSwapJacquet.unitChar_one]

theorem restrictLin_mem_complexStandardModule {pre post : List ComplexCharacterData}
    {d e : ComplexCharacterData} (hpre : pre.length = p) {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ complexStandardModule n (pre ++ d :: e :: post)) :
    restrictLin p hp f ∈
      complexStandardModule 2 [twist (shift n p) d, twist (shift n p) e] := by
  refine ⟨contMDiff_restrictLin p hp hf.1, fun a u g => ?_⟩
  rw [restrictLin_apply, restrictLin_apply, map_mul, map_mul, block_diagonalUnits,
    ← principalSeriesCharacter_blockDiag p hp pre post d e hpre]
  exact hf.2 (blockDiag p hp a) ⟨block p hp u, block_mem_upperUnipotent p hp u.2⟩ (block p hp g)

theorem restrictLin_mem_kFiniteVectors {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n)) :
    restrictLin p hp f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 2 ℂ))
      (unitaryCompact ℂ 2) := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ 2 =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 2 ℂ) (k : Langlands.GeneralLinear 2 ℂ)
          (restrictLin p hp f)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
          f)).map (restrictLin p hp) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨block p hp k, block_mem_unitaryCompact p hp k.2⟩, rfl⟩,
      (restrictLin_rightTranslation p hp k f).symm⟩
  exact Submodule.finiteDimensional_of_le hle

/-- The `U(N)`-finite functions of the standard module of `ds` on `GL_N(ℂ)`. -/
abbrev KFs (N : ℕ) (ds : List ComplexCharacterData) : Submodule ℂ (Langlands.GeneralLinear N ℂ → ℂ) :=
  kFiniteFunctions (complexStandardModule N ds) (unitaryCompact ℂ N)

variable (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
  (hpre : pre.length = p)

/-- Restriction to the block: from the `U(n)`-finite functions of the standard module of
`pre ++ d :: e :: post` to the `U(2)`-finite functions of the standard module of the twisted
pair. -/
def res : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] KFs 2 [twist (shift n p) d, twist (shift n p) e] :=
  ((restrictLin p hp).comp (KFs n (pre ++ d :: e :: post)).subtype).codRestrict _ fun f =>
    ⟨restrictLin_mem_complexStandardModule p hp hpre f.2.1, restrictLin_mem_kFiniteVectors p hp f.2.2⟩

theorem res_apply (f : KFs n (pre ++ d :: e :: post)) (g : Langlands.GeneralLinear 2 ℂ) :
    (res p hp pre post d e hpre f : Langlands.GeneralLinear 2 ℂ → ℂ) g =
      (f : Langlands.GeneralLinear n ℂ → ℂ) (block p hp g) :=
  rfl

/-! ## Compatibility with `U(2)` and with the Lie algebra -/

theorem blockMat_mem_unitaryGroup {k : Matrix (Fin 2) (Fin 2) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    blockMat p hp k ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hk ⊢
  rw [star_blockMat, blockMat_mul, hk, blockMat_one]

/-- The block embedding `U(2) → U(n)`. -/
def blockU (k : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨blockMat p hp k, blockMat_mem_unitaryGroup p hp k.2⟩

theorem block_toUnits (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    block p hp (Unitary.toUnits k) = Unitary.toUnits (blockU p hp k) :=
  Units.ext rfl

theorem res_rep (k : Matrix.unitaryGroup (Fin 2) ℂ) (f : KFs n (pre ++ d :: e :: post)) :
    complexStandardRep 2 [twist (shift n p) d, twist (shift n p) e] k (res p hp pre post d e hpre f) =
      res p hp pre post d e hpre (complexStandardRep n (pre ++ d :: e :: post) (blockU p hp k) f) := by
  apply Subtype.ext
  funext g
  rw [principalSeriesRep_apply_coe, res_apply]
  change (f : Langlands.GeneralLinear n ℂ → ℂ) (block p hp (g * Unitary.toUnits k)) =
    (f : Langlands.GeneralLinear n ℂ → ℂ) (block p hp g * Unitary.toUnits (blockU p hp k))
  rw [map_mul, block_toUnits]

theorem rightDerivative_restrictLin {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (m : Langlands.GeneralLinear 2 ℂ) :
    rightDerivative (matrixModel ℂ 2) X (restrictLin p hp f) m =
      rightDerivative (matrixModel ℂ n) (lin p hp X) f (block p hp m) := by
  rw [rightDerivative_eq_fderiv (contMDiff_restrictLin p hp hf), rightDerivative_eq_fderiv hf,
    block_val]
  have heq : unitsExtension (restrictLin p hp f) =ᶠ[nhds (m : Matrix (Fin 2) (Fin 2) ℂ)]
      unitsExtension f ∘ blockMat p hp := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit m)] with y hy
    obtain ⟨u, rfl⟩ := hy
    rw [unitsExtension_val, Function.comp_apply, ← block_val, unitsExtension_val]
    rfl
  have hL : HasFDerivAt (blockMat p hp) ((linL p hp).restrictScalars ℝ).toContinuousLinearMap
      (m : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h : blockMat p hp = fun M =>
        ((linL p hp).restrictScalars ℝ).toContinuousLinearMap M + (1 - lin p hp 1) := rfl
    rw [h]
    exact (ContinuousLinearMap.hasFDerivAt _).add_const _
  have hU : HasFDerivAt (unitsExtension f)
      (fderiv ℝ (unitsExtension f) (blockMat p hp (m : Matrix (Fin 2) (Fin 2) ℂ)))
      (blockMat p hp (m : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (differentiableAt_unitsExtension hf (isUnit_blockMat p hp (Units.isUnit m))).hasFDerivAt
  rw [heq.fderiv_eq, (hU.comp _ hL).fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (unitsExtension f) _ (lin p hp ((m : Matrix (Fin 2) (Fin 2) ℂ) * X)) = _
  rw [← blockMat_mul_lin]

theorem res_lie_one_tmul (X : Matrix (Fin 2) (Fin 2) ℂ) (f : KFs n (pre ++ d :: e :: post)) :
    complexStandardLie 2 [twist (shift n p) d, twist (shift n p) e] ((1 : ℂ) ⊗ₜ[ℝ] X)
        (res p hp pre post d e hpre f) =
      res p hp pre post d e hpre
        (complexStandardLie n (pre ++ d :: e :: post) ((1 : ℂ) ⊗ₜ[ℝ] lin p hp X) f) := by
  apply Subtype.ext
  funext g
  rw [principalSeriesLie_one_tmul_apply_coe, res_apply, principalSeriesLie_one_tmul_apply_coe]
  exact rightDerivative_restrictLin p hp f.2.1.1 X g

/-- The image under restriction of a `(𝔤𝔩_n, U(n))`-stable subspace is `(𝔤𝔩_2, U(2))`-stable. -/
theorem map_res_stable (W : Submodule ℂ (KFs n (pre ++ d :: e :: post)))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W,
      complexStandardRep n (pre ++ d :: e :: post) k w ∈ W)
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W,
      complexStandardLie n (pre ++ d :: e :: post) X w ∈ W) :
    (∀ (k : Matrix.unitaryGroup (Fin 2) ℂ), ∀ v ∈ W.map (res p hp pre post d e hpre),
      complexStandardRep 2 [twist (shift n p) d, twist (shift n p) e] k v ∈
        W.map (res p hp pre post d e hpre)) ∧
    (∀ (t : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ), ∀ v ∈ W.map (res p hp pre post d e hpre),
      complexStandardLie 2 [twist (shift n p) d, twist (shift n p) e] t v ∈
        W.map (res p hp pre post d e hpre)) := by
  refine ⟨?_, ?_⟩
  · rintro k _ ⟨w, hw, rfl⟩
    rw [res_rep]
    exact ⟨_, hWK _ w hw, rfl⟩
  · rintro t _ ⟨w, hw, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul c X =>
      have hc : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply, res_lie_one_tmul]
      exact Submodule.smul_mem _ c ⟨_, hWL _ w hw, rfl⟩
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂


/-! ## The chart and the rank-one Jacquet integrand -/

theorem one_apply_pos (k l : Fin 2) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (pos p hp k) (pos p hp l) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) k l := by
  simp [Matrix.one_apply, pos_eq_pos_iff]

theorem fin_two_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

theorem blockMat_swap :
    blockMat p hp (Matrix.swap ℂ (0 : Fin 2) 1) = Matrix.swap ℂ (pos p hp 0) (pos p hp 1) := by
  ext a b
  rw [← Matrix.mul_one (Matrix.swap ℂ (pos p hp 0) (pos p hp 1))]
  rcases mem_range_or p hp a with ⟨k, rfl⟩ | ha
  · rcases mem_range_or p hp b with ⟨l, rfl⟩ | hb
    · rw [blockMat_apply_pos, ← Matrix.mul_one (Matrix.swap ℂ (0 : Fin 2) 1)]
      rcases fin_two_cases k with rfl | rfl
      · rw [Matrix.swap_mul_apply_left, Matrix.swap_mul_apply_left, one_apply_pos]
      · rw [Matrix.swap_mul_apply_right, Matrix.swap_mul_apply_right, one_apply_pos]
    · rw [blockMat_apply_right p hp _ _ hb]
      rcases fin_two_cases k with rfl | rfl
      · rw [Matrix.swap_mul_apply_left, Matrix.one_apply_ne (fun h => hb 0 h.symm),
          Matrix.one_apply_ne (fun h => hb 1 h.symm)]
      · rw [Matrix.swap_mul_apply_right, Matrix.one_apply_ne (fun h => hb 0 h.symm),
          Matrix.one_apply_ne (fun h => hb 1 h.symm)]
  · rw [blockMat_apply_left p hp _ ha, Matrix.swap_mul_of_ne (ha 0) (ha 1)]

theorem blockMat_transvection (z : ℂ) :
    blockMat p hp (Matrix.transvection (0 : Fin 2) 1 z) =
      Matrix.transvection (pos p hp 0) (pos p hp 1) z := by
  rw [Matrix.transvection, Matrix.transvection, blockMat_add_lin, blockMat_one, lin_single]

theorem hj_two : ((1 : Fin 2) : ℕ) = ((0 : Fin 2) : ℕ) + 1 := rfl

theorem hj_pos : ((pos p hp 1 : Fin n) : ℕ) = ((pos p hp 0 : Fin n) : ℕ) + 1 := by
  simp [pos_val]

theorem block_chart (z : ℂ) :
    block p hp (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj_two z) =
      ComplexSwapJacquet.chart (pos p hp 0) (pos p hp 1) (hj_pos p hp) z := by
  apply Units.ext
  rw [block_val, ComplexSwapJacquet.chart_val, ComplexSwapJacquet.chart_val, ← blockMat_mul,
    blockMat_swap, blockMat_transvection]

theorem length_two (x y : ComplexCharacterData) : [x, y].length = 2 := rfl

include hpre in
theorem kappa_block (hn : (pre ++ d :: e :: post).length = n) (c : ℂ) :
    ComplexSwapJacquet.kappa [twist (shift n p) d, twist (shift n p) e] (length_two _ _) 1 c =
      ComplexSwapJacquet.kappa (pre ++ d :: e :: post) hn (pos p hp 1) c := by
  have h : (pre ++ d :: e :: post).get (Fin.cast hn.symm (pos p hp 1)) = e :=
    ComplexSwapJacquet.getElem_append_cons_cons_right _ _ _ _ _ (by simp [pos_val, hpre]) _
  simp only [ComplexSwapJacquet.kappa, h]
  change (c.re : ℂ) * (2 * (twist (shift n p) e).exponent + (((2 : ℕ) : ℂ) - 1) -
      2 * (((1 : Fin 2) : ℕ) : ℂ)) + (c.im : ℂ) * (Complex.I * ((twist (shift n p) e).weight : ℂ)) = _
  simp only [twist, characterOfParams_weight, characterOfParams_exponent, shift, pos_val,
    Fin.val_one]
  push_cast
  ring

theorem coe_res (f : KFs n (pre ++ d :: e :: post)) :
    (res p hp pre post d e hpre f : Langlands.GeneralLinear 2 ℂ → ℂ) =
      restrictLin p hp (f : Langlands.GeneralLinear n ℂ → ℂ) :=
  rfl

theorem integrand_res (hn : (pre ++ d :: e :: post).length = n) (c : ℂ)
    (f : KFs n (pre ++ d :: e :: post)) (z : ℂ) :
    ComplexSwapJacquet.integrand [twist (shift n p) d, twist (shift n p) e] (length_two _ _) 0 1
        hj_two c
        (res p hp pre post d e hpre f) z =
      ComplexSwapJacquet.integrand (pre ++ d :: e :: post) hn (pos p hp 0) (pos p hp 1)
        (hj_pos p hp) c f z := by
  simp only [ComplexSwapJacquet.integrand]
  rw [coe_res, rightDerivative_restrictLin p hp f.2.1.1, lin_single, restrictLin_apply,
    block_chart, kappa_block p hp pre post d e hpre hn]


/-! ## The rank-one Jacquet functionals on `GL_n` and on the block -/

include hpre in
theorem hi_pos : ((pos p hp 0 : Fin n) : ℕ) = pre.length := by
  simp [pos_val, hpre]

theorem twist_exponent_sub (s : ℂ) :
    (twist s d).exponent - (twist s e).exponent = d.exponent - e.exponent := by
  simp only [twist, characterOfParams_exponent]
  ring

theorem re_twist_nonneg (s : ℂ) (hre : 0 ≤ (d.exponent - e.exponent).re) :
    0 ≤ ((twist s d).exponent - (twist s e).exponent).re := by
  rwa [twist_exponent_sub]

/-- The rank-one Jacquet functional `Λ_c` of the standard module of `pre ++ d :: e :: post`
at the positions `p`, `p + 1` of `d` and `e`. -/
def lamN (hn : (pre ++ d :: e :: post).length = n) (hre : 0 ≤ (d.exponent - e.exponent).re)
    (c : ℂ) : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] ℂ :=
  ComplexSwapJacquet.functional
    (ComplexSwapJacquet.chartLieFacts _ hn (pos p hp 0) (pos p hp 1) (hj_pos p hp))
    (ComplexSwapJacquet.chartDecay pre post d e (pos p hp 0) (pos p hp 1)
      (hi_pos p hp pre hpre) (hj_pos p hp) hre) c

/-- The rank-one Jacquet functional `Λ_c` of the standard module of the twisted pair on
`GL_2(ℂ)`. -/
def lamTwo (s : ℂ) (hre : 0 ≤ (d.exponent - e.exponent).re) (c : ℂ) :
    KFs 2 [twist s d, twist s e] →ₗ[ℂ] ℂ :=
  ComplexSwapJacquet.functional
    (ComplexSwapJacquet.chartLieFacts _ (length_two _ _) 0 1 hj_two)
    (ComplexSwapJacquet.chartDecay [] [] (twist s d) (twist s e) 0 1 rfl hj_two
      (re_twist_nonneg d e s hre)) c

/-- **The functional only sees the block**: `Λ_c^{(n)}(f) = Λ_c^{(2)}(f ∘ block)`. -/
theorem lamTwo_res (hn : (pre ++ d :: e :: post).length = n)
    (hre : 0 ≤ (d.exponent - e.exponent).re) (c : ℂ) (f : KFs n (pre ++ d :: e :: post)) :
    lamTwo d e (shift n p) hre c (res p hp pre post d e hpre f) =
      lamN p hp pre post d e hpre hn hre c f := by
  simp only [lamTwo, lamN, ComplexSwapJacquet.functional_apply]
  congr 1
  funext z
  exact integrand_res p hp pre post d e hpre hn c f z

/-- Some `Λ_c^{(2)}` is nonzero (the nonvanishing at `n = 2`). -/
theorem exists_lamTwo_ne_zero (s : ℂ) (hre : 0 ≤ (d.exponent - e.exponent).re)
    (hne : d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent) :
    ∃ c, lamTwo d e s hre c ≠ 0 := by
  have hne' : (twist s d).weight ≠ (twist s e).weight ∨
      (twist s d).exponent ≠ (twist s e).exponent := by
    simp only [twist, characterOfParams_weight, characterOfParams_exponent]
    rcases hne with h | h
    · exact Or.inl h
    · exact Or.inr fun h' => h (add_right_cancel h')
  obtain ⟨c, f, hf, hint⟩ := ComplexSwapJacquet.exists_integral_integrand_ne_zero [] []
    (twist s d) (twist s e) 2 (length_two _ _) 0 1 rfl hj_two (re_twist_nonneg d e s hre) hne'
  refine ⟨c, fun h0 => hint ?_⟩
  have h1 := ComplexSwapJacquet.functional_apply
    (ComplexSwapJacquet.chartLieFacts _ (length_two _ _) 0 1 hj_two)
    (ComplexSwapJacquet.chartDecay [] [] (twist s d) (twist s e) 0 1 rfl hj_two
      (re_twist_nonneg d e s hre)) c ⟨f, hf⟩
  have h2 : lamTwo d e s hre c ⟨f, hf⟩ = 0 := by
    rw [h0]
    rfl
  exact h1.symm.trans h2

/-! ## Linkage -/

theorem isComplexLinked_symm {d e : ComplexCharacterData} (h : IsComplexLinked d e) :
    IsComplexLinked e d := by
  obtain ⟨a, b, hab, h1, h2⟩ := h
  refine ⟨-a, -b, by rw [neg_mul_neg]; exact hab, ?_, ?_⟩
  · push_cast
    rw [← h1]
    ring
  · push_cast
    rw [← h2]
    ring

theorem isComplexLinked_twist_iff (s : ℂ) :
    IsComplexLinked (twist s d) (twist s e) ↔ IsComplexLinked d e := by
  have h1 : (twist s d).exponent + ((twist s d).weight : ℂ) / 2 -
      ((twist s e).exponent + ((twist s e).weight : ℂ) / 2) =
        d.exponent + (d.weight : ℂ) / 2 - (e.exponent + (e.weight : ℂ) / 2) := by
    simp only [twist, characterOfParams_weight, characterOfParams_exponent]
    ring
  have h2 : (twist s d).exponent - ((twist s d).weight : ℂ) / 2 -
      ((twist s e).exponent - ((twist s e).weight : ℂ) / 2) =
        d.exponent - (d.weight : ℂ) / 2 - (e.exponent - (e.weight : ℂ) / 2) := by
    simp only [twist, characterOfParams_weight, characterOfParams_exponent]
    ring
  unfold IsComplexLinked
  rw [h1, h2]

/-! ## The key lemma -/

/-- **Key lemma.** If `d`, `e` are not linked and `Λ_c^{(2)} ≠ 0`, then every
`(𝔤𝔩_n, U(n))`-stable subspace of the `U(n)`-finite functions of the standard module of
`pre ++ d :: e :: post` on which `Λ_c^{(n)}` vanishes is zero. -/
theorem eq_bot_of_lamN (hirr : ComplexGLTwoUnlinkedIrreducibleStatement)
    (hn : (pre ++ d :: e :: post).length = n) (hre : 0 ≤ (d.exponent - e.exponent).re)
    (hlink : ¬ IsComplexLinked d e) (c : ℂ) (hc : lamTwo d e (shift n p) hre c ≠ 0)
    (W : Submodule ℂ (KFs n (pre ++ d :: e :: post)))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W,
      complexStandardRep n (pre ++ d :: e :: post) k w ∈ W)
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W,
      complexStandardLie n (pre ++ d :: e :: post) X w ∈ W)
    (hW0 : ∀ w ∈ W, lamN p hp pre post d e hpre hn hre c w = 0) : W = ⊥ := by
  obtain ⟨hK, hL⟩ := map_res_stable p hp pre post d e hpre W hWK hWL
  have hlink' : ¬ IsComplexLinked (twist (shift n p) d) (twist (shift n p) e) := by
    rwa [isComplexLinked_twist_iff]
  rcases (hirr _ _ hlink').2 _ hK hL with hV | hV
  · rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    apply ComplexPermutation.kFiniteEval_one_separating
    intro k
    have hres : res p hp pre post d e hpre (complexStandardRep n (pre ++ d :: e :: post) k w) = 0 := by
      have h := Submodule.mem_map_of_mem (f := res p hp pre post d e hpre) (hWK k w hw)
      rw [hV] at h
      exact (Submodule.mem_bot ℂ).mp h
    have h1 := congrFun (congrArg Subtype.val hres) 1
    rw [res_apply, map_one] at h1
    rw [kFiniteEval_apply]
    exact h1
  · exfalso
    apply hc
    apply LinearMap.ext
    intro v
    have hv : v ∈ W.map (res p hp pre post d e hpre) := by
      rw [hV]
      exact Submodule.mem_top
    obtain ⟨w, hw, rfl⟩ := hv
    rw [lamTwo_res p hp pre post d e hpre hn, hW0 w hw, LinearMap.zero_apply]

/-! ## The Jacquet property of `Λ_c^{(n)}` -/

/-- `Λ_c^{(n)}` is a Jacquet functional on the `U(n)`-finite functions of the standard module of
`pre ++ d :: e :: post` with the exponents of `pre ++ e :: d :: post` (the bookkeeping of
`ComplexSwapJacquet.exists_swapJacquetFunctional`, for this particular functional). -/
theorem isJacquet_lamN (hn : (pre ++ d :: e :: post).length = n)
    (hes : (pre ++ e :: d :: post).length = n) (hre : 0 ≤ (d.exponent - e.exponent).re) (c : ℂ) :
    IsComplexJacquetFunctional n (complexStandardLie n (pre ++ d :: e :: post))
      (lamN p hp pre post d e hpre hn hre c)
      (ComplexPermutation.listExponent n (pre ++ e :: d :: post) hes)
      (ComplexPermutation.listWeight n (pre ++ e :: d :: post) hes) := by
  have hi : ((pos p hp 0 : Fin n) : ℕ) = pre.length := hi_pos p hp pre hpre
  have hj : ((pos p hp 1 : Fin n) : ℕ) = ((pos p hp 0 : Fin n) : ℕ) + 1 := hj_pos p hp
  have hgi : ∀ (l : List ComplexCharacterData) (hl : l.length = n) (k : Fin n),
      l.get (Fin.cast hl.symm k) = l[(k : ℕ)]'(by rw [hl]; exact k.2) := fun _ _ _ => rfl
  have hds_i : (pre ++ d :: e :: post).get (Fin.cast hn.symm (pos p hp 0)) = d := by
    rw [hgi _ hn]; exact ComplexSwapJacquet.getElem_append_cons_cons_left _ _ _ _ _ hi _
  have hds_j : (pre ++ d :: e :: post).get (Fin.cast hn.symm (pos p hp 1)) = e := by
    rw [hgi _ hn]; exact ComplexSwapJacquet.getElem_append_cons_cons_right _ _ _ _ _ (by omega) _
  have hes_i : (pre ++ e :: d :: post).get (Fin.cast hes.symm (pos p hp 0)) = e := by
    rw [hgi _ hes]; exact ComplexSwapJacquet.getElem_append_cons_cons_left _ _ _ _ _ hi _
  have hes_j : (pre ++ e :: d :: post).get (Fin.cast hes.symm (pos p hp 1)) = d := by
    rw [hgi _ hes]; exact ComplexSwapJacquet.getElem_append_cons_cons_right _ _ _ _ _ (by omega) _
  have hother : ∀ k : Fin n, k ≠ pos p hp 0 → k ≠ pos p hp 1 →
      (pre ++ e :: d :: post).get (Fin.cast hes.symm k) =
        (pre ++ d :: e :: post).get (Fin.cast hn.symm k) := by
    intro k hki hkj
    rw [hgi _ hes, hgi _ hn]
    apply ComplexSwapJacquet.getElem_append_cons_cons_of_ne
    · intro h; exact hki (Fin.ext (by omega))
    · intro h; exact hkj (Fin.ext (by omega))
  apply ComplexSwapJacquet.isComplexJacquetFunctional_functional
  · intro k hki hkj
    rw [ComplexPermutation.listExponent, ComplexSwapJacquet.kappa_one, hother k hki hkj]
  · rw [ComplexPermutation.listExponent, ComplexSwapJacquet.kappa_one, hes_i, hds_j, hj]
    push_cast
    ring
  · rw [ComplexPermutation.listExponent, ComplexSwapJacquet.kappa_one, hes_j, hds_i, hj]
    push_cast
    ring
  · intro k hki hkj
    rw [ComplexPermutation.listWeight, ComplexSwapJacquet.kappa_I, hother k hki hkj]
  · rw [ComplexPermutation.listWeight, ComplexSwapJacquet.kappa_I, hes_i, hds_j]
  · rw [ComplexPermutation.listWeight, ComplexSwapJacquet.kappa_I, hes_j, hds_i]

end Langlands.Archimedean.ComplexBlock
