import Langlands.GroupScheme.SplitExistence.SimpleRootData
import Langlands.GroupScheme.SplitExistence.RootLieConj
import Langlands.GroupScheme.SplitExistence.WeylWords
import Langlands.GroupScheme.SplitExistence.Primitive

/-!
# Integral Weyl elements of simple `SL₂`-data

For integral `SL₂`-data `S : SimpleRootData P b`, the rational matrices `(E i 1)` and `(F i 1)`
form generators of a rational Lie algebra with a triangular weight structure (`toLieGens`).

For a simple root `i`, the integral Weyl element `n_i = u_i(1) u_{-i}(-1) u_i(1)`
(`weylMat`) has the integral inverse `u_i(-1) u_{-i}(1) u_i(-1)` (`weylMatInv`); over every
commutative ring they are the images of `[[0, 1], [-1, 0]]` and of its inverse under `φ i`
(`map_weylMat`, `map_weylMatInv`); both move weights by the simple reflection `s_i`, and
conjugation by them preserves the rational Lie algebra `lieSpan`. The products of these
elements along a word of simple roots (`wordMat`, `wordMatInv`) move weights by the Weyl group
element of the word.

For a reduced root datum with finitely many roots, the component of `lieSpan` whose weight is a
root is a line (`exists_line_of_root`): it is the conjugate of the line of a simple root by
a Weyl word.
-/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

/-- Conjugation by matrices mapping weights by mutually inverse linear automorphisms
transports the weight of a homogeneous matrix. -/
theorem IsWtHom.conj_linearEquiv {ι X R : Type*} [Fintype ι] [AddCommGroup X] [Ring R]
    {wt : ι → X} (f : X ≃ₗ[ℤ] X) {g g' : Matrix ι ι R} (hg : MapsWt wt f g)
    (hg' : MapsWt wt f.symm g') {μ : X} {A : Matrix ι ι R} (hA : IsWtHom wt μ A) :
    IsWtHom wt (f μ) (g * A * g') := by
  intro c d h
  rw [(hg.mul hA.mapsWt).mul hg' c d h]
  simp only [Function.comp_apply, map_add, LinearEquiv.apply_symm_apply]

/-- The cast `ℤ → ULift ℤ` is injective. -/
theorem intCast_ulift_injective : Function.Injective (Int.castRingHom (ULift.{u} ℤ)) := by
  intro a c h
  have := congrArg ULift.down h
  simpa using this

namespace SimpleRootData

section SL2

variable {R : Type*} [CommRing R]

theorem sl2Weyl_eq_upper_lower_upper :
    (sl2Weyl : SpecialLinearGroup (Fin 2) R) = sl2Upper 1 * sl2Lower (-1) * sl2Upper 1 := by
  apply Subtype.ext
  change !![(0 : R), 1; -1, 0] = !![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]
  simp

theorem sl2Weyl_inv_eq_upper_lower_upper :
    (sl2Weyl : SpecialLinearGroup (Fin 2) R)⁻¹ = sl2Upper (-1) * sl2Lower 1 * sl2Upper (-1) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  change !![(0 : R), 1; -1, 0] * (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -1; 0, 1]) = 1
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Weyl_inv_eq_cube :
    (sl2Weyl : SpecialLinearGroup (Fin 2) R)⁻¹ = sl2Weyl * sl2Weyl * sl2Weyl := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  change !![(0 : R), 1; -1, 0] *
    (!![(0 : R), 1; -1, 0] * !![(0 : R), 1; -1, 0] * !![(0 : R), 1; -1, 0]) = 1
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end SL2

open Classical

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (S : SimpleRootData P b)

theorem isDividedPowerFamily_E (i : b.support) : IsDividedPowerFamily (S.E i) :=
  ⟨S.E_zero i, S.E_mul i, S.E_eq_zero i⟩

theorem isDividedPowerFamily_F (i : b.support) : IsDividedPowerFamily (S.F i) :=
  ⟨S.F_zero i, S.F_mul i, S.F_eq_zero i⟩

theorem isWtHom_E (i : b.support) (k : ℕ) : IsWtHom S.wt (k • P.root i) (S.E i k) :=
  fun c d h => S.E_weight i k c d h

theorem isWtHom_F (i : b.support) (k : ℕ) : IsWtHom S.wt (-(k • P.root i)) (S.F i k) := by
  intro c d h
  rw [← S.F_weight i k c d h, add_neg_cancel_right]

/-! ### The rational Lie algebra of the simple root operators -/

/-- The additive character `μ ↦ ⟨μ, α_i^∨⟩` of `X`, with values in `ℚ`. -/
def corootChar (i : b.support) : X →+ ℚ where
  toFun x := (P.toLinearMap x (P.coroot i) : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

/-- The rational operators `E i 1` and `F i 1` of the simple roots, as generators of a rational
Lie algebra with a triangular weight structure. -/
def toLieGens : LieGens S.wt b.support where
  α i := P.root i
  e i := (S.E i 1).map (Int.castRingHom ℚ)
  f i := (S.F i 1).map (Int.castRingHom ℚ)
  χ := corootChar
  coeff_inj _ _ h := coeff_eq_of_sum_eq h
  e_wt i := by simpa using (S.isWtHom_E i 1).map (Int.castRingHom ℚ)
  f_wt i := by simpa using (S.isWtHom_F i 1).map (Int.castRingHom ℚ)
  e_f i j := by
    rw [matAd_apply, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_sub _ (map_sub (Int.castRingHom ℚ))]
    split_ifs with h
    · subst h
      rw [S.E_F_same, Matrix.diagonal_map (map_zero _)]
      rfl
    · rw [S.E_F_comm i j h, sub_self, Matrix.map_zero _ (map_zero _)]

theorem toLieGens_e (i : b.support) : S.toLieGens.e i = (S.E i 1).map (Int.castRingHom ℚ) :=
  rfl

theorem toLieGens_f (i : b.support) : S.toLieGens.f i = (S.F i 1).map (Int.castRingHom ℚ) :=
  rfl

theorem toLieGens_α (i : b.support) : S.toLieGens.α i = P.root i :=
  rfl

theorem divExp_E_conj_mem (i : b.support) (s : ℚ) {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) :
    divExp (S.E i) s * x * divExp (S.E i) (-s) ∈ S.toLieGens.lieSpan :=
  divExp_conj_mem (S.isDividedPowerFamily_E i) (fun _ hy => S.toLieGens.matAd_e_mem i hy) s hx

theorem divExp_F_conj_mem (i : b.support) (s : ℚ) {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) :
    divExp (S.F i) s * x * divExp (S.F i) (-s) ∈ S.toLieGens.lieSpan :=
  divExp_conj_mem (S.isDividedPowerFamily_F i) (fun _ hy => S.toLieGens.matAd_f_mem i hy) s hx

/-! ### Weyl elements of the simple roots -/

/-- The integral Weyl element `n_i = u_i(1) u_{-i}(-1) u_i(1)` of a simple root. -/
def weylMat (i : b.support) : Matrix (Fin S.n) (Fin S.n) ℤ :=
  divExp (S.E i) (1 : ℤ) * divExp (S.F i) (-1 : ℤ) * divExp (S.E i) (1 : ℤ)

/-- The integral inverse `u_i(-1) u_{-i}(1) u_i(-1)` of the Weyl element of a simple root. -/
def weylMatInv (i : b.support) : Matrix (Fin S.n) (Fin S.n) ℤ :=
  divExp (S.E i) (-1 : ℤ) * divExp (S.F i) (1 : ℤ) * divExp (S.E i) (-1 : ℤ)

private theorem divExp_cancel {D : ℕ → Matrix (Fin S.n) (Fin S.n) ℤ}
    (hD : IsDividedPowerFamily D) (s t : ℤ) (h : s + t = 0) (M : Matrix (Fin S.n) (Fin S.n) ℤ) :
    divExp D s * (divExp D t * M) = M := by
  rw [← Matrix.mul_assoc, divExp_mul hD, h, divExp_zero hD, Matrix.one_mul]

theorem weylMat_mul_weylMatInv (i : b.support) : S.weylMat i * S.weylMatInv i = 1 := by
  have hE := S.isDividedPowerFamily_E i
  have hF := S.isDividedPowerFamily_F i
  simp only [weylMat, weylMatInv, Matrix.mul_assoc]
  rw [S.divExp_cancel hE 1 (-1) (by norm_num), S.divExp_cancel hF (-1) 1 (by norm_num),
    divExp_mul hE, add_neg_cancel, divExp_zero hE]

theorem weylMatInv_mul_weylMat (i : b.support) : S.weylMatInv i * S.weylMat i = 1 := by
  have hE := S.isDividedPowerFamily_E i
  have hF := S.isDividedPowerFamily_F i
  simp only [weylMat, weylMatInv, Matrix.mul_assoc]
  rw [S.divExp_cancel hE (-1) 1 (by norm_num), S.divExp_cancel hF 1 (-1) (by norm_num),
    divExp_mul hE, neg_add_cancel, divExp_zero hE]

theorem map_weylMat_eq (i : b.support) (R : Type*) [CommRing R] :
    (S.weylMat i).map (Int.castRingHom R) =
      divExp (S.E i) (1 : R) * divExp (S.F i) (-1 : R) * divExp (S.E i) (1 : R) := by
  simp only [weylMat, Matrix.map_mul, divExp_map, map_one, map_neg]

theorem map_weylMatInv_eq (i : b.support) (R : Type*) [CommRing R] :
    (S.weylMatInv i).map (Int.castRingHom R) =
      divExp (S.E i) (-1 : R) * divExp (S.F i) (1 : R) * divExp (S.E i) (-1 : R) := by
  simp only [weylMatInv, Matrix.map_mul, divExp_map, map_one, map_neg]

/-- Over every commutative ring, the Weyl element is the image of `[[0, 1], [-1, 0]]`. -/
theorem map_weylMat (i : b.support) (R : Type u) [CommRing R] :
    (S.weylMat i).map (Int.castRingHom R) =
      ((S.φ i R sl2Weyl : GL (Fin S.n) R) : Matrix (Fin S.n) (Fin S.n) R) := by
  rw [S.map_weylMat_eq, sl2Weyl_eq_upper_lower_upper, map_mul, map_mul, Units.val_mul,
    Units.val_mul, S.φ_upper, S.φ_lower]

/-- Over every commutative ring, the inverse Weyl element is the image of the inverse of
`[[0, 1], [-1, 0]]`. -/
theorem map_weylMatInv (i : b.support) (R : Type u) [CommRing R] :
    (S.weylMatInv i).map (Int.castRingHom R) =
      (((S.φ i R sl2Weyl)⁻¹ : GL (Fin S.n) R) : Matrix (Fin S.n) (Fin S.n) R) := by
  rw [S.map_weylMatInv_eq, ← map_inv, sl2Weyl_inv_eq_upper_lower_upper, map_mul, map_mul,
    Units.val_mul, Units.val_mul, S.φ_upper, S.φ_lower]

/-- The Weyl element moves weights by the simple reflection. -/
theorem mapsWt_weylMat (i : b.support) : MapsWt S.wt (P.reflection i) (S.weylMat i) := by
  refine MapsWt.of_map (intCast_ulift_injective.{u}) ?_
  rw [S.map_weylMat i (ULift.{u} ℤ)]
  exact fun c d h => S.weyl_weight i _ c d h

/-- The inverse Weyl element moves weights by the simple reflection. -/
theorem mapsWt_weylMatInv (i : b.support) :
    MapsWt S.wt (P.reflection i).symm (S.weylMatInv i) := by
  have hw : MapsWt S.wt (P.reflection i)
      ((S.φ i (ULift.{u} ℤ) sl2Weyl : GL (Fin S.n) (ULift.{u} ℤ)) :
        Matrix (Fin S.n) (Fin S.n) (ULift.{u} ℤ)) :=
    fun c d h => S.weyl_weight i _ c d h
  refine MapsWt.of_map (intCast_ulift_injective.{u}) ?_
  rw [S.map_weylMatInv i (ULift.{u} ℤ), ← map_inv, sl2Weyl_inv_eq_cube, map_mul, map_mul,
    Units.val_mul, Units.val_mul]
  intro c d h
  rw [(hw.mul hw).mul hw c d h]
  simp only [Function.comp_apply, RootPairing.reflection_same]
  rfl

/-- Conjugation by the Weyl element transports weights by the simple reflection. -/
theorem isWtHom_weylMat_conj (i : b.support) {R : Type*} [Ring R] {μ : X}
    {A : Matrix (Fin S.n) (Fin S.n) R} (hA : IsWtHom S.wt μ A) :
    IsWtHom S.wt (P.reflection i μ)
      ((S.weylMat i).map (Int.castRingHom R) * A * (S.weylMatInv i).map (Int.castRingHom R)) :=
  IsWtHom.conj_linearEquiv (P.reflection i) ((S.mapsWt_weylMat i).map _)
    ((S.mapsWt_weylMatInv i).map _) hA

/-- Conjugation by the Weyl element preserves the rational Lie algebra. -/
theorem weylMat_conj_mem (i : b.support) {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) :
    (S.weylMat i).map (Int.castRingHom ℚ) * x * (S.weylMatInv i).map (Int.castRingHom ℚ) ∈
      S.toLieGens.lieSpan := by
  rw [S.map_weylMat_eq, S.map_weylMatInv_eq]
  have h1 := S.divExp_E_conj_mem i 1 hx
  have h2 := S.divExp_F_conj_mem i (-1) h1
  rw [neg_neg] at h2
  have h3 := S.divExp_E_conj_mem i 1 h2
  convert h3 using 1
  simp only [Matrix.mul_assoc]

/-- Conjugation by the inverse Weyl element preserves the rational Lie algebra. -/
theorem weylMatInv_conj_mem (i : b.support) {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) :
    (S.weylMatInv i).map (Int.castRingHom ℚ) * x * (S.weylMat i).map (Int.castRingHom ℚ) ∈
      S.toLieGens.lieSpan := by
  rw [S.map_weylMat_eq, S.map_weylMatInv_eq]
  have h1 := S.divExp_E_conj_mem i (-1) hx
  rw [neg_neg] at h1
  have h2 := S.divExp_F_conj_mem i 1 h1
  have h3 := S.divExp_E_conj_mem i (-1) h2
  rw [neg_neg] at h3
  convert h3 using 1
  simp only [Matrix.mul_assoc]

/-! ### Weyl words -/

/-- The product `n_{i₁} ⋯ n_{i_m}` of the Weyl elements along a word of simple roots. -/
def wordMat : List b.support → Matrix (Fin S.n) (Fin S.n) ℤ
  | [] => 1
  | i :: w => S.weylMat i * wordMat w

/-- The product `n_{i_m}⁻¹ ⋯ n_{i₁}⁻¹` of the inverse Weyl elements along a word. -/
def wordMatInv : List b.support → Matrix (Fin S.n) (Fin S.n) ℤ
  | [] => 1
  | i :: w => wordMatInv w * S.weylMatInv i

theorem wordMatInv_mul_wordMat (w : List b.support) : S.wordMatInv w * S.wordMat w = 1 := by
  induction w with
  | nil => exact Matrix.one_mul 1
  | cons i w ih =>
    rw [wordMat, wordMatInv, Matrix.mul_assoc, ← Matrix.mul_assoc (S.weylMatInv i),
      S.weylMatInv_mul_weylMat, Matrix.one_mul, ih]

theorem wordMat_mul_wordMatInv (w : List b.support) : S.wordMat w * S.wordMatInv w = 1 := by
  induction w with
  | nil => exact Matrix.one_mul 1
  | cons i w ih =>
    rw [wordMat, wordMatInv, Matrix.mul_assoc, ← Matrix.mul_assoc (S.wordMat w), ih,
      Matrix.one_mul, S.weylMat_mul_weylMatInv]

theorem mapsWt_wordMat (w : List b.support) : MapsWt S.wt (weylWord P b w) (S.wordMat w) := by
  induction w with
  | nil =>
    intro c d h
    exact MapsWt.one c d h
  | cons i w ih =>
    intro c d h
    rw [weylWord_cons]
    exact ((S.mapsWt_weylMat i).mul ih) c d h

theorem mapsWt_wordMatInv (w : List b.support) :
    MapsWt S.wt (weylWord P b w).symm (S.wordMatInv w) := by
  induction w with
  | nil =>
    intro c d h
    exact MapsWt.one c d h
  | cons i w ih =>
    intro c d h
    rw [weylWord_cons_symm]
    exact (ih.mul (S.mapsWt_weylMatInv i)) c d h

/-- Conjugation by a Weyl word transports weights by its Weyl group element. -/
theorem isWtHom_wordMat_conj (w : List b.support) {R : Type*} [Ring R] {μ : X}
    {A : Matrix (Fin S.n) (Fin S.n) R} (hA : IsWtHom S.wt μ A) :
    IsWtHom S.wt (weylWord P b w μ)
      ((S.wordMat w).map (Int.castRingHom R) * A * (S.wordMatInv w).map (Int.castRingHom R)) :=
  IsWtHom.conj_linearEquiv (weylWord P b w) ((S.mapsWt_wordMat w).map _)
    ((S.mapsWt_wordMatInv w).map _) hA

/-- Conjugation by the inverse of a Weyl word transports weights by the inverse of its Weyl
group element. -/
theorem isWtHom_wordMatInv_conj (w : List b.support) {R : Type*} [Ring R] {μ : X}
    {A : Matrix (Fin S.n) (Fin S.n) R} (hA : IsWtHom S.wt μ A) :
    IsWtHom S.wt ((weylWord P b w).symm μ)
      ((S.wordMatInv w).map (Int.castRingHom R) * A * (S.wordMat w).map (Int.castRingHom R)) :=
  IsWtHom.conj_linearEquiv (weylWord P b w).symm ((S.mapsWt_wordMatInv w).map _)
    ((S.mapsWt_wordMat w).map _) hA

theorem wordMat_conj_mem (w : List b.support) {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) :
    (S.wordMat w).map (Int.castRingHom ℚ) * x * (S.wordMatInv w).map (Int.castRingHom ℚ) ∈
      S.toLieGens.lieSpan := by
  induction w generalizing x with
  | nil => simpa [wordMat, wordMatInv] using hx
  | cons i w ih =>
    have h := S.weylMat_conj_mem i (ih hx)
    convert h using 1
    simp only [wordMat, wordMatInv, Matrix.map_mul, Matrix.mul_assoc]

theorem wordMatInv_conj_mem (w : List b.support) {x : Matrix (Fin S.n) (Fin S.n) ℚ}
    (hx : x ∈ S.toLieGens.lieSpan) :
    (S.wordMatInv w).map (Int.castRingHom ℚ) * x * (S.wordMat w).map (Int.castRingHom ℚ) ∈
      S.toLieGens.lieSpan := by
  induction w generalizing x with
  | nil => simpa [wordMat, wordMatInv] using hx
  | cons i w ih =>
    have h := ih (S.weylMatInv_conj_mem i hx)
    convert h using 1
    simp only [wordMat, wordMatInv, Matrix.map_mul, Matrix.mul_assoc]

/-- Undoing a conjugation by a Weyl word over `ℚ`. -/
theorem wordMat_conj_wordMatInv_conj (w : List b.support) (x : Matrix (Fin S.n) (Fin S.n) ℚ) :
    (S.wordMat w).map (Int.castRingHom ℚ) *
        ((S.wordMatInv w).map (Int.castRingHom ℚ) * x * (S.wordMat w).map (Int.castRingHom ℚ)) *
          (S.wordMatInv w).map (Int.castRingHom ℚ) = x := by
  have h1 := congrArg (fun M : Matrix (Fin S.n) (Fin S.n) ℤ => M.map (Int.castRingHom ℚ)) (S.wordMat_mul_wordMatInv w)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]

/-- Undoing a conjugation by the inverse of a Weyl word over `ℚ`. -/
theorem wordMatInv_conj_wordMat_conj (w : List b.support) (x : Matrix (Fin S.n) (Fin S.n) ℚ) :
    (S.wordMatInv w).map (Int.castRingHom ℚ) *
        ((S.wordMat w).map (Int.castRingHom ℚ) * x * (S.wordMatInv w).map (Int.castRingHom ℚ)) *
          (S.wordMat w).map (Int.castRingHom ℚ) = x := by
  have h1 := congrArg (fun M : Matrix (Fin S.n) (Fin S.n) ℤ => M.map (Int.castRingHom ℚ)) (S.wordMatInv_mul_wordMat w)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]

/-! ### The root lines of the rational Lie algebra -/

variable [Finite J] [P.IsReduced]

/-- The component of `lieSpan` of the weight of a root is a line: it is spanned by a nonzero
element of `lieSpan` of that weight. -/
theorem exists_line_of_root (j : J) :
    ∃ y : Matrix (Fin S.n) (Fin S.n) ℚ, y ∈ S.toLieGens.lieSpan ∧ IsWtHom S.wt (P.root j) y ∧
      y ≠ 0 ∧ ∀ x ∈ S.toLieGens.lieSpan, IsWtHom S.wt (P.root j) x → ∃ q : ℚ, x = q • y := by
  classical
  obtain ⟨w, i, hj⟩ := exists_weylWord_root (b := b) j
  set y := (S.wordMat w).map (Int.castRingHom ℚ) * S.toLieGens.e i *
    (S.wordMatInv w).map (Int.castRingHom ℚ) with hy
  refine ⟨y, S.wordMat_conj_mem w (S.toLieGens.e_mem i), ?_, ?_, ?_⟩
  · rw [hj]
    exact S.isWtHom_wordMat_conj w (S.toLieGens.e_wt i)
  · intro h0
    apply map_rat_ne_zero (S.E_one_map_ne_zero i 2 Nat.prime_two)
    rw [← toLieGens_e, ← S.wordMatInv_conj_wordMat_conj w (S.toLieGens.e i), ← hy, h0,
      Matrix.mul_zero, Matrix.zero_mul]
  · intro x hx hxw
    have hx' := S.wordMatInv_conj_mem w hx
    have hxw' := S.isWtHom_wordMatInv_conj w hxw
    rw [hj, LinearEquiv.symm_apply_apply] at hxw'
    obtain ⟨q, hq⟩ := S.toLieGens.exists_eq_smul_e_of_isWtHom hx' i hxw'
    refine ⟨q, ?_⟩
    rw [← S.wordMat_conj_wordMatInv_conj w x, hq, hy, Matrix.mul_smul, Matrix.smul_mul]

end SimpleRootData

end Langlands.GroupScheme.SplitExistence
