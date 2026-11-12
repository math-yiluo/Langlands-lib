import Langlands.Shimura.Unitary.KottwitzDualGroup
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Kottwitz's representation `r` of the unramified L-group

The representation `W = ⨂_τ ⋀^{n - n(Φτ)} Lⁿ` of `Ĝ ⋊ ℤ`, with `(ζ, g)` acting by
`ζ⁻¹ ⨂_τ det(g_τ)⁻¹ ⋀(g_τ)` and the Frobenius generator acting by reindexing the
factors and applying the Hodge-star crossing isomorphism `⋀ᵏ ≃ ⋀^{n-k}` at the
factors where the CM type is crossed. Kottwitz's condition (b) and the extreme
weight `μ` are proved. See the paired Markdown for conventions and sources.
-/

noncomputable section

open Module exteriorPower Set.powersetCard
open scoped Matrix TensorProduct

namespace Langlands.Shimura.KottwitzDual

universe u v

/-! ### The determinant of the signed antidiagonal -/

section SignedAntidiagonal

variable (L : Type v) [Field L]

theorem det_signedAntidiagonal (m : ℕ) : (signedAntidiagonal m L).det = 1 := by
  induction m with
  | zero => exact Matrix.det_isEmpty
  | succ m ih =>
    rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (Fin.last m)]
    · have hsub : (signedAntidiagonal (m + 1) L).submatrix (Fin.last m).succAbove Fin.succ =
          signedAntidiagonal m L := by
        ext k l
        simp only [Matrix.submatrix_apply, Fin.succAbove_last, signedAntidiagonal,
          Fin.rev_castSucc, Fin.succ_inj, Fin.val_castSucc]
      rw [hsub, ih, mul_one]
      simp only [signedAntidiagonal, Fin.rev_last, ↓reduceIte, Fin.val_last]
      rw [← mul_pow]; simp
    · intro i _ hi
      have : ¬ ((0 : Fin (m + 1)) = Fin.rev i) := fun h =>
        hi (by rw [← Fin.rev_rev i, ← h, Fin.rev_zero])
      simp [signedAntidiagonal, this]
    · simp

end SignedAntidiagonal

/-! ### The wedge pairing and the Hodge star on `⋀ Lⁿ` -/

section Star

variable {L : Type v} [Field L]

variable (L) in
/-- The top-degree coordinate `⋀ⁿ Lⁿ → L`, `v₀ ∧ ⋯ ∧ v_{n-1} ↦ det (vᵢ)ᵢ`. -/
def topForm (n : ℕ) : ⋀[L]^n (Fin n → L) →ₗ[L] L :=
  alternatingMapLinearEquiv Matrix.detRowAlternating

theorem topForm_ιMulti {n : ℕ} (v : Fin n → Fin n → L) :
    topForm L n (ιMulti L n v) = (Matrix.of v).det := by
  rw [topForm, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem topForm_map {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (x : ⋀[L]^n (Fin n → L)) :
    topForm L n (exteriorPower.map n (Matrix.toLin' A) x) = A.det * topForm L n x := by
  have h : (topForm L n).comp (exteriorPower.map n (Matrix.toLin' A)) = A.det • topForm L n := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      map_apply_ιMulti, topForm_ιMulti, smul_eq_mul]
    have hv : Matrix.of (Matrix.toLin' A ∘ v) = Matrix.of v * A.transpose := by
      ext i j
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [hv, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  exact LinearMap.congr_fun h x

theorem mul_mem_exteriorPower {M : Type*} [AddCommGroup M] [Module L M] {k m N : ℕ}
    (h : k + m = N) (y : ⋀[L]^k M) (x : ⋀[L]^m M) : y.1 * x.1 ∈ ⋀[L]^N M := by
  subst h
  change y.1 * x.1 ∈ LinearMap.range (ExteriorAlgebra.ι L (M := M)) ^ (k + m)
  rw [pow_add]
  exact Submodule.mul_mem_mul y.2 x.2

/-- The wedge pairing `⋀ᵏ Lⁿ × ⋀ᵐ Lⁿ → L`, `(y, x) ↦ top (y ∧ x)`, for `k + m = n`. -/
def wedgePairing {n k m : ℕ} (h : k + m = n) :
    ⋀[L]^k (Fin n → L) →ₗ[L] Module.Dual L (⋀[L]^m (Fin n → L)) :=
  LinearMap.mk₂ L (fun y x => topForm L n ⟨y.1 * x.1, mul_mem_exteriorPower h y x⟩)
    (fun y₁ y₂ x => by
      rw [← map_add]; congr 1; ext; simp [add_mul])
    (fun c y x => by
      rw [← map_smul]; congr 1; ext; simp)
    (fun y x₁ x₂ => by
      rw [← map_add]; congr 1; ext; simp [mul_add])
    (fun c y x => by
      rw [← map_smul]; congr 1; ext; simp)

theorem wedgePairing_apply {n k m : ℕ} (h : k + m = n) (y : ⋀[L]^k (Fin n → L))
    (x : ⋀[L]^m (Fin n → L)) :
    wedgePairing h y x = topForm L n ⟨y.1 * x.1, mul_mem_exteriorPower h y x⟩ := rfl

/-- `top (A y ∧ A x) = det A · top (y ∧ x)`. -/
theorem wedgePairing_map {n k m : ℕ} (h : k + m = n) (A : Matrix (Fin n) (Fin n) L)
    (y : ⋀[L]^k (Fin n → L)) (x : ⋀[L]^m (Fin n → L)) :
    wedgePairing h (exteriorPower.map k (Matrix.toLin' A) y)
        (exteriorPower.map m (Matrix.toLin' A) x) = A.det * wedgePairing h y x := by
  rw [wedgePairing_apply, wedgePairing_apply, ← topForm_map]
  congr 1
  ext
  change (exteriorPower.map k (Matrix.toLin' A) y : ExteriorAlgebra L (Fin n → L)) *
    (exteriorPower.map m (Matrix.toLin' A) x : ExteriorAlgebra L (Fin n → L)) = _
  rw [exteriorPower.coe_map, exteriorPower.coe_map, exteriorPower.coe_map]
  exact (map_mul _ _ _).symm

theorem wedgePairing_eq_of_mul_eq {n k m : ℕ} (h : k + m = n) {y : ⋀[L]^k (Fin n → L)}
    {x : ⋀[L]^m (Fin n → L)} {z : ⋀[L]^n (Fin n → L)} (hz : y.1 * x.1 = z.1) :
    wedgePairing h y x = topForm L n z := by
  rw [wedgePairing_apply]
  congr 1
  exact Subtype.ext hz

/-! #### The exterior power of the dot product -/

variable (L) in
/-- The dot product on `Lⁿ`, as a map to the dual. -/
def dotForm (n : ℕ) : (Fin n → L) →ₗ[L] Module.Dual L (Fin n → L) :=
  Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) L)

theorem dotForm_apply {n : ℕ} (v w : Fin n → L) : dotForm L n v w = v ⬝ᵥ w := by
  simp [dotForm, Matrix.toBilin'_apply']

theorem bijective_dotForm (n : ℕ) : Function.Bijective (dotForm L n) := by
  have hinj : Function.Injective (dotForm L n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    funext i
    have := LinearMap.congr_fun hv (Pi.single i 1)
    simpa [dotForm_apply, dotProduct_single] using this
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj⟩

/-- `exteriorPower.map` along a linear equivalence, as a linear equivalence. -/
def mapEquiv {M N : Type*} [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (k : ℕ) (e : M ≃ₗ[L] N) : ⋀[L]^k M ≃ₗ[L] ⋀[L]^k N :=
  LinearEquiv.ofLinearMap (exteriorPower.map k e.toLinearMap)
    (exteriorPower.map k e.symm.toLinearMap)
    (by rw [← map_comp, show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from
      LinearMap.ext e.apply_symm_apply, map_id])
    (by rw [← map_comp, show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from
      LinearMap.ext e.symm_apply_apply, map_id])

@[simp] theorem mapEquiv_apply {M N : Type*} [AddCommGroup M] [Module L M] [AddCommGroup N]
    [Module L N] (k : ℕ) (e : M ≃ₗ[L] N) (x : ⋀[L]^k M) :
    mapEquiv k e x = exteriorPower.map k e.toLinearMap x := rfl

/-- The exterior power `Ψ` of the dot product, `⋀ᵐ Lⁿ ≃ (⋀ᵐ Lⁿ)*`. -/
def exteriorDot (n m : ℕ) : ⋀[L]^m (Fin n → L) ≃ₗ[L] Module.Dual L (⋀[L]^m (Fin n → L)) :=
  (mapEquiv m (LinearEquiv.ofBijective (dotForm L n) (bijective_dotForm n))).trans
    (LinearEquiv.ofBijective (pairingDual L (Fin n → L) m)
      (bijective_pairingDual (R := L) (M := Fin n → L) (n := m)))

theorem exteriorDot_ιMulti {n m : ℕ} (v w : Fin m → Fin n → L) :
    exteriorDot n m (ιMulti L m v) (ιMulti L m w) = (Matrix.of fun i j => v j ⬝ᵥ w i).det := by
  simp [exteriorDot, map_apply_ιMulti, pairingDual_ιMulti_ιMulti, dotForm_apply]

/-- `Ψ (A z) x = Ψ z (Aᵀ x)`. -/
theorem exteriorDot_map {n m : ℕ} (A : Matrix (Fin n) (Fin n) L) (z x : ⋀[L]^m (Fin n → L)) :
    exteriorDot n m (exteriorPower.map m (Matrix.toLin' A) z) x =
      exteriorDot n m z (exteriorPower.map m (Matrix.toLin' A.transpose) x) := by
  have h : (exteriorDot n m).toLinearMap.comp (exteriorPower.map m (Matrix.toLin' A)) =
      (exteriorDot n m).toLinearMap.compl₂ (exteriorPower.map m (Matrix.toLin' A.transpose)) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v =>
      exteriorPower.linearMap_ext (AlternatingMap.ext fun w => ?_))
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearEquiv.coe_coe, map_apply_ιMulti, exteriorDot_ιMulti]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.toLin'_apply]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  exact LinearMap.congr_fun₂ h z x

/-! #### Nondegeneracy of the wedge pairing -/

theorem det_basisFun_comp_ne_zero {N : ℕ} (f : Fin N → Fin N) (hf : Function.Injective f) :
    (Matrix.of (Pi.basisFun L (Fin N) ∘ f)).det ≠ 0 := by
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσ : Matrix.of (Pi.basisFun L (Fin N) ∘ f) =
      (1 : Matrix (Fin N) (Fin N) L).submatrix σ id := by
    ext i j
    simp [σ, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hσ, Matrix.det_permute, Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem wedgePairing_basis_of_not_disjoint {k m : ℕ} (S : Set.powersetCard (Fin (k + m)) k)
    (T : Set.powersetCard (Fin (k + m)) m) (hST : ¬ Disjoint S.val T.val) :
    wedgePairing (L := L) rfl ((Pi.basisFun L (Fin (k + m))).exteriorPower k S)
      ((Pi.basisFun L (Fin (k + m))).exteriorPower m T) = 0 := by
  rw [wedgePairing_eq_of_mul_eq rfl (z := 0), map_zero]
  simp only [basis_apply, ιMulti_family_apply_coe, ZeroMemClass.coe_zero]
  exact ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint (R := L) _ S T hST

theorem wedgePairing_basis_ne_zero_of_disjoint {k m : ℕ} (S : Set.powersetCard (Fin (k + m)) k)
    (T : Set.powersetCard (Fin (k + m)) m) (hST : Disjoint S.val T.val) :
    wedgePairing (L := L) rfl ((Pi.basisFun L (Fin (k + m))).exteriorPower k S)
      ((Pi.basisFun L (Fin (k + m))).exteriorPower m T) ≠ 0 := by
  rw [wedgePairing_eq_of_mul_eq rfl (z := (((permOfDisjoint hST).sign : ℤ) : L) •
    exteriorPower.ιMulti_family L (k + m) (Pi.basisFun L (Fin (k + m))) (disjUnion hST))]
  · rw [map_smul, smul_eq_mul, exteriorPower.ιMulti_family, topForm_ιMulti]
    refine mul_ne_zero ?_ (det_basisFun_comp_ne_zero _ (ofFinEmbEquiv.symm _).injective)
    rcases Int.units_eq_one_or (permOfDisjoint hST).sign with h | h <;> simp [h]
  · simp only [basis_apply, ιMulti_family_apply_coe, Submodule.coe_smul]
    rw [ExteriorAlgebra.ιMulti_family_mul_of_disjoint (R := L) _ S T hST, Units.smul_def,
      Int.cast_smul_eq_zsmul]

theorem wedgePairing_injective {n k m : ℕ} (h : k + m = n) :
    Function.Injective (wedgePairing (L := L) h) := by
  subst h
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hcard : m + k = Fintype.card (Fin (k + m)) := by simp [add_comm]
  refine ((Pi.basisFun L (Fin (k + m))).exteriorPower k).ext_elem fun S => ?_
  have h0 := LinearMap.congr_fun hy ((Pi.basisFun L (Fin (k + m))).exteriorPower m
    (compl hcard S))
  rw [← ((Pi.basisFun L (Fin (k + m))).exteriorPower k).sum_repr y] at h0
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, smul_eq_mul] at h0
  rw [Finset.sum_eq_single S] at h0
  · rw [map_zero, Finsupp.zero_apply]
    refine (mul_eq_zero.mp h0).resolve_right (wedgePairing_basis_ne_zero_of_disjoint _ _ ?_)
    change Disjoint S.val S.valᶜ
    exact disjoint_compl_right
  · intro S' _ hS'
    rw [wedgePairing_basis_of_not_disjoint S' _ ?_, mul_zero]
    intro hd
    change Disjoint S'.val S.valᶜ at hd
    rw [disjoint_compl_right_iff] at hd
    exact hS' (Subtype.ext (Finset.eq_of_subset_of_card_le hd (by rw [card_eq, card_eq])))
  · intro hS
    exact absurd (Finset.mem_univ S) hS

theorem wedgePairing_bijective {n k m : ℕ} (h : k + m = n) :
    Function.Bijective (wedgePairing (L := L) h) := by
  refine ⟨wedgePairing_injective h, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact wedgePairing_injective h
  · subst h
    simpa using Nat.choose_symm_add (a := k) (b := m)

/-! #### The Hodge star and the crossing isomorphism -/

/-- The Hodge star `⋆ = Ψ⁻¹ ∘ D : ⋀ᵏ Lⁿ ≃ ⋀ᵐ Lⁿ` for `k + m = n`. -/
def hodgeStar {n k m : ℕ} (h : k + m = n) : ⋀[L]^k (Fin n → L) ≃ₗ[L] ⋀[L]^m (Fin n → L) :=
  (LinearEquiv.ofBijective (wedgePairing h) (wedgePairing_bijective h)).trans
    (exteriorDot n m).symm

theorem exteriorDot_hodgeStar {n k m : ℕ} (h : k + m = n) (y : ⋀[L]^k (Fin n → L)) :
    exteriorDot n m (hodgeStar h y) = wedgePairing h y := by
  simp [hodgeStar]

/-- A matrix unit as a linear automorphism of `Lⁿ`. -/
def glEquiv {n : ℕ} (g : GL (Fin n) L) : (Fin n → L) ≃ₗ[L] (Fin n → L) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L))
    (Matrix.toLin' (g⁻¹ : GL (Fin n) L).val)
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.toLin'_one])

@[simp] theorem glEquiv_toLinearMap {n : ℕ} (g : GL (Fin n) L) :
    (glEquiv g).toLinearMap = Matrix.toLin' (g : Matrix (Fin n) (Fin n) L) := rfl

theorem map_toLin'_mul {n k : ℕ} (A B : Matrix (Fin n) (Fin n) L) (x : ⋀[L]^k (Fin n → L)) :
    exteriorPower.map k (Matrix.toLin' (A * B)) x =
      exteriorPower.map k (Matrix.toLin' A) (exteriorPower.map k (Matrix.toLin' B) x) := by
  rw [Matrix.toLin'_mul, map_comp, LinearMap.comp_apply]

theorem map_toLin'_one {n k : ℕ} (x : ⋀[L]^k (Fin n → L)) :
    exteriorPower.map k (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) L)) x = x := by
  rw [Matrix.toLin'_one, map_id, LinearMap.id_apply]

/-- `⋆ (g y) = det g · (g⁻¹)ᵀ (⋆ y)`. -/
theorem hodgeStar_map {n k m : ℕ} (h : k + m = n) (g : GL (Fin n) L) (y : ⋀[L]^k (Fin n → L)) :
    hodgeStar h (exteriorPower.map k (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L)) y) =
      (g : Matrix (Fin n) (Fin n) L).det • exteriorPower.map m
        (Matrix.toLin' (g⁻¹ : GL (Fin n) L).val.transpose) (hodgeStar h y) := by
  apply (exteriorDot n m).injective
  refine LinearMap.ext fun x => ?_
  have hx : x = exteriorPower.map m (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L))
      (exteriorPower.map m (Matrix.toLin' (g⁻¹ : GL (Fin n) L).val) x) := by
    rw [← map_toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_toLin'_one]
  rw [exteriorDot_hodgeStar, map_smul, LinearMap.smul_apply, exteriorDot_map,
    Matrix.transpose_transpose, exteriorDot_hodgeStar, smul_eq_mul]
  conv_lhs => rw [hx]
  rw [wedgePairing_map]

/-- The crossing isomorphism `C = ⋀ᵐ(J') ∘ ⋆ : ⋀ᵏ Lⁿ ≃ ⋀ᵐ Lⁿ` for `k + m = n`. -/
def crossing {n k m : ℕ} (h : k + m = n) : ⋀[L]^k (Fin n → L) ≃ₗ[L] ⋀[L]^m (Fin n → L) :=
  (hodgeStar h).trans (mapEquiv m (glEquiv (signedAntidiagonalUnit n L)))

theorem crossing_apply {n k m : ℕ} (h : k + m = n) (y : ⋀[L]^k (Fin n → L)) :
    crossing h y = exteriorPower.map m (Matrix.toLin' (signedAntidiagonal n L))
      (hodgeStar h y) := rfl

/-- `C (g y) = det g · θ(g) (C y)`. -/
theorem crossing_map {n k m : ℕ} (h : k + m = n) (g : GL (Fin n) L) (y : ⋀[L]^k (Fin n → L)) :
    crossing h (exteriorPower.map k (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L)) y) =
      (g : Matrix (Fin n) (Fin n) L).det • exteriorPower.map m
        (Matrix.toLin' (twist n L g : Matrix (Fin n) (Fin n) L)) (crossing h y) := by
  rw [crossing_apply, crossing_apply, hodgeStar_map, map_smul, ← map_toLin'_mul,
    ← map_toLin'_mul]
  congr 3
  rw [twist_apply]
  simp only [Units.val_mul, transposeInv_val, mul_assoc]
  rw [show ((signedAntidiagonalUnit n L)⁻¹ : GL (Fin n) L).val * signedAntidiagonal n L = 1 from
    Units.inv_mul (signedAntidiagonalUnit n L), mul_one]
  rfl

/-! #### Highest weight vectors -/

/-- The highest weight vector `e₀ ∧ ⋯ ∧ e_{k-1}` of `⋀ᵏ Lⁿ`. -/
def hwVector {n : ℕ} (k : ℕ) (hk : k ≤ n) : ⋀[L]^k (Fin n → L) :=
  ιMulti L k (fun j => Pi.basisFun L (Fin n) (Fin.castLE hk j))

theorem signedAntidiagonal_mulVec {n : ℕ} (w : Fin n → L) (c : Fin n) :
    (signedAntidiagonal n L *ᵥ w) c = (-1) ^ (c : ℕ) * w (Fin.rev c) := by
  simp only [Matrix.mulVec, dotProduct, signedAntidiagonal]
  rw [Finset.sum_eq_single (Fin.rev c)]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

/-- The crossing isomorphism carries highest weight vectors to highest weight vectors. -/
theorem crossing_hwVector {n k m : ℕ} (h : k + m = n) (hk : k ≤ n) (hm : m ≤ n) :
    crossing h (hwVector (L := L) k hk) = hwVector m hm := by
  subst h
  -- the minor of a family `w` on the last `m` coordinates
  have key : wedgePairing (L := L) rfl (hwVector k hk) =
      (exteriorDot (k + m) m (hwVector m hm)).comp
        (exteriorPower.map m (Matrix.toLin' (signedAntidiagonal (k + m) L))) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, map_apply_ιMulti]
    set N : Matrix (Fin m) (Fin m) L := Matrix.of fun i j => w i (Fin.natAdd k j)
    -- left side: a block triangular determinant
    have hL : wedgePairing (L := L) rfl (hwVector k hk) (ιMulti L m w) = N.det := by
      rw [wedgePairing_eq_of_mul_eq rfl (z := ιMulti L (k + m)
        (Fin.append (fun j => Pi.basisFun L (Fin (k + m)) (Fin.castLE hk j)) w)), topForm_ιMulti]
      · rw [← Matrix.det_reindex_self finSumFinEquiv.symm]
        have hblock : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (Matrix.of
            (Fin.append (fun j => Pi.basisFun L (Fin (k + m)) (Fin.castLE hk j)) w)) =
            Matrix.fromBlocks 1 0 (Matrix.of fun i j => w i (Fin.castAdd m j)) N := by
          ext (i | i) (j | j)
          · simp [Matrix.one_apply, Pi.single_apply, Fin.ext_iff, eq_comm]
          · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
              finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
              Fin.append_left, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
              Pi.basisFun_apply, Pi.single_apply, Fin.ext_iff]
            split_ifs with hc
            · have := i.isLt
              simp only [Fin.val_natAdd, Fin.val_castLE] at hc
              omega
            · rfl
          · simp [N]
          · simp [N]
        rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
      · simp only [hwVector, ιMulti_apply_coe]
        exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _
    -- right side: `N` times the transpose of `J'_m`
    have hR : exteriorDot (k + m) m (hwVector m hm)
        (ιMulti L m (Matrix.toLin' (signedAntidiagonal (k + m) L) ∘ w)) = N.det := by
      rw [hwVector, exteriorDot_ιMulti]
      have hmat : (Matrix.of fun i j => Pi.basisFun L (Fin (k + m)) (Fin.castLE hm j) ⬝ᵥ
          (Matrix.toLin' (signedAntidiagonal (k + m) L) ∘ w) i) =
          N * (signedAntidiagonal m L).transpose := by
        ext i j
        simp only [Matrix.of_apply, Function.comp_apply, Pi.basisFun_apply, Matrix.toLin'_apply,
          single_dotProduct, one_mul, signedAntidiagonal_mulVec, Matrix.mul_apply,
          Matrix.transpose_apply, signedAntidiagonal, N]
        rw [Finset.sum_eq_single (Fin.rev j)]
        · have hrev : Fin.rev (Fin.castLE hm j) = Fin.natAdd k (Fin.rev j) := by
            ext
            simp only [Fin.val_rev, Fin.val_castLE, Fin.val_natAdd]
            omega
          simp [hrev, mul_comm]
        · intro l _ hl
          simp [hl]
        · simp
      rw [hmat, Matrix.det_mul, Matrix.det_transpose, det_signedAntidiagonal, mul_one]
    rw [hL, hR]
  have hstar : hodgeStar (L := L) rfl (hwVector k hk) = exteriorPower.map m
      (Matrix.toLin' (signedAntidiagonal (k + m) L).transpose) (hwVector m hm) := by
    apply (exteriorDot (k + m) m).injective
    refine LinearMap.ext fun x => ?_
    rw [exteriorDot_hodgeStar, key, exteriorDot_map, Matrix.transpose_transpose]
    rfl
  rw [crossing_apply, hstar, ← map_toLin'_mul, signedAntidiagonal_mul_transpose, map_toLin'_one]

end Star

/-! ### Kottwitz's representation -/

section Representation

variable {L : Type v} [Field L] {n : ℕ}

/-- The underlying map of `ρ_k(g) = det(g)⁻¹ ⋀ᵏ(g)`. -/
def wedgeRepFun (k : ℕ) (g : GL (Fin n) L) : ⋀[L]^k (Fin n → L) ≃ₗ[L] ⋀[L]^k (Fin n → L) :=
  (LinearEquiv.smulOfUnit (Matrix.GeneralLinearGroup.det g)⁻¹).trans (mapEquiv k (glEquiv g))

theorem wedgeRepFun_apply (k : ℕ) (g : GL (Fin n) L) (x : ⋀[L]^k (Fin n → L)) :
    wedgeRepFun k g x = ((g : Matrix (Fin n) (Fin n) L).det)⁻¹ •
      exteriorPower.map k (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L)) x := by
  change exteriorPower.map k (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L))
    ((Matrix.GeneralLinearGroup.det g)⁻¹ • x) = _
  rw [Units.smul_def, map_smul, Units.val_inv_eq_inv_val,
    Matrix.GeneralLinearGroup.val_det_apply]

/-- The representation `ρ_k(g) = det(g)⁻¹ ⋀ᵏ(g)` of `GL_n` on `⋀ᵏ Lⁿ`
(isomorphic to `⋀^{n-k}` of the dual of the standard representation). -/
def wedgeRep (k : ℕ) : GL (Fin n) L →* (⋀[L]^k (Fin n → L) ≃ₗ[L] ⋀[L]^k (Fin n → L)) where
  toFun := wedgeRepFun k
  map_one' := LinearEquiv.ext fun x => by
    rw [wedgeRepFun_apply, Units.val_one, Matrix.det_one, inv_one, one_smul, map_toLin'_one]
    rfl
  map_mul' g g' := LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, wedgeRepFun_apply, wedgeRepFun_apply, wedgeRepFun_apply,
      Units.val_mul, map_toLin'_mul, map_smul, smul_smul, Matrix.det_mul, mul_inv]

theorem wedgeRep_apply (k : ℕ) (g : GL (Fin n) L) (x : ⋀[L]^k (Fin n → L)) :
    wedgeRep k g x = ((g : Matrix (Fin n) (Fin n) L).det)⁻¹ •
      exteriorPower.map k (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L)) x :=
  wedgeRepFun_apply k g x

theorem coe_wedgeRep_apply (k : ℕ) (g : GL (Fin n) L) (x : ⋀[L]^k (Fin n → L)) :
    (wedgeRep k g x : ExteriorAlgebra L (Fin n → L)) = ((g : Matrix (Fin n) (Fin n) L).det)⁻¹ •
      ExteriorAlgebra.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) L)) x.1 := by
  rw [wedgeRep_apply, Submodule.coe_smul, exteriorPower.coe_map]

variable {S : Type u} [Fintype S]

/-- The representation space `W = ⨂_τ ⋀^{k τ} Lⁿ`. -/
abbrev KottwitzSpace (S : Type u) (n : ℕ) (L : Type v) [Field L] (k : S → ℕ) : Type (max u v) :=
  ⨂[L] τ : S, ⋀[L]^(k τ) (Fin n → L)

omit [Fintype S] in
theorem kottwitzSpace_ext {k : S → ℕ} {f g : KottwitzSpace S n L k ≃ₗ[L] KottwitzSpace S n L k}
    (H : ∀ m : ∀ τ, ⋀[L]^(k τ) (Fin n → L),
      f (PiTensorProduct.tprod L m) = g (PiTensorProduct.tprod L m)) : f = g :=
  LinearEquiv.toLinearMap_injective (PiTensorProduct.ext (MultilinearMap.ext H))

/-- The underlying map of the representation of `Ĝ` on `W`. -/
def dualRepFun (k : S → ℕ) (x : DualGroup S n L) :
    KottwitzSpace S n L k ≃ₗ[L] KottwitzSpace S n L k :=
  (LinearEquiv.smulOfUnit x.1⁻¹).trans
    (PiTensorProduct.congr fun τ => wedgeRep (k τ) (x.2 τ))

omit [Fintype S] in
theorem dualRepFun_tprod (k : S → ℕ) (x : DualGroup S n L) (m : ∀ τ, ⋀[L]^(k τ) (Fin n → L)) :
    dualRepFun k x (PiTensorProduct.tprod L m) =
      ((x.1 : L))⁻¹ • PiTensorProduct.tprod L (fun τ => wedgeRep (k τ) (x.2 τ) (m τ)) := by
  change PiTensorProduct.congr (fun τ => wedgeRep (k τ) (x.2 τ))
    (x.1⁻¹ • PiTensorProduct.tprod L m) = _
  rw [Units.smul_def, map_smul, PiTensorProduct.congr_tprod, Units.val_inv_eq_inv_val]

/-- The representation `(ζ, g) ↦ ζ⁻¹ ⨂_τ ρ_{k τ}(g_τ)` of `Ĝ` on `W`. -/
def dualRep (k : S → ℕ) :
    DualGroup S n L →* (KottwitzSpace S n L k ≃ₗ[L] KottwitzSpace S n L k) where
  toFun := dualRepFun k
  map_one' := kottwitzSpace_ext fun m => by
    rw [dualRepFun_tprod]
    simp
  map_mul' x y := kottwitzSpace_ext fun m => by
    rw [LinearEquiv.mul_apply, dualRepFun_tprod, dualRepFun_tprod, map_smul, dualRepFun_tprod,
      smul_smul]
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, LinearEquiv.mul_apply,
      Units.val_mul, mul_inv, mul_comm]

omit [Fintype S] in
theorem dualRep_tprod (k : S → ℕ) (x : DualGroup S n L) (m : ∀ τ, ⋀[L]^(k τ) (Fin n → L)) :
    dualRep k x (PiTensorProduct.tprod L m) =
      ((x.1 : L))⁻¹ • PiTensorProduct.tprod L (fun τ => wedgeRep (k τ) (x.2 τ) (m τ)) :=
  dualRepFun_tprod k x m

/-! #### The Frobenius operator -/

omit [Fintype S] in
theorem CMPerm.apply_eq_base (G : CMPerm S) (τ : S) (b : Bool) :
    (G : Equiv.Perm (S × Bool)) (τ, b) = (CMPerm.base G τ, xor b (CMPerm.crosses G τ)) :=
  CMPerm.apply_eq G τ b

theorem dualEndo_snd (G : CMPerm S) (x : DualGroup S n L) (τ' : S) :
    (dualEndo G x).2 τ' =
      if CMPerm.crosses G ((CMPerm.base G).symm τ') then
        twist n L (x.2 ((CMPerm.base G).symm τ'))
      else x.2 ((CMPerm.base G).symm τ') := rfl

variable (h : S × Bool → ℕ) (hsum : ∀ τ, h (τ, true) + h (τ, false) = n)
  (G : CMPerm S) (hG : ∀ x, h ((G : Equiv.Perm (S × Bool)) x) = h x)

omit [Fintype S] in
include hsum hG in
theorem hodge_add_of_crosses {τ : S} (hc : CMPerm.crosses G τ = true) :
    h (τ, false) + h (CMPerm.base G τ, false) = n := by
  have h1 := hG (τ, false)
  rw [CMPerm.apply_eq_base, hc, Bool.false_xor] at h1
  have h2 := hsum (CMPerm.base G τ)
  omega

omit [Fintype S] in
include hG in
theorem hodge_eq_of_not_crosses {τ : S} (hc : ¬ CMPerm.crosses G τ = true) :
    h (CMPerm.base G τ, false) = h (τ, false) := by
  have h1 := hG (τ, false)
  rw [CMPerm.apply_eq_base, Bool.eq_false_iff.mpr hc, Bool.false_xor] at h1
  exact h1

/-- The component at `τ'` of the Frobenius operator: the crossing isomorphism if
`G` moves `Φ (π⁻¹ τ')` out of the CM type, the identity otherwise. -/
def factorEquiv (τ' : S) :
    ⋀[L]^(h ((CMPerm.base G).symm τ', false)) (Fin n → L) ≃ₗ[L]
      ⋀[L]^(h (τ', false)) (Fin n → L) :=
  if hc : CMPerm.crosses G ((CMPerm.base G).symm τ') = true then
    crossing (by simpa using hodge_add_of_crosses h hsum G hG hc)
  else
    LinearEquiv.ofEq _ _ (congrArg (fun j => ⋀[L]^j (Fin n → L))
      (by simpa using (hodge_eq_of_not_crosses h G hG hc).symm))

omit [Fintype S] in
theorem factorEquiv_wedgeRep (τ' : S) (g : GL (Fin n) L)
    (y : ⋀[L]^(h ((CMPerm.base G).symm τ', false)) (Fin n → L)) :
    factorEquiv h hsum G hG τ' (wedgeRep _ g y) =
      (if CMPerm.crosses G ((CMPerm.base G).symm τ') then
        ((g : Matrix (Fin n) (Fin n) L).det)⁻¹ else 1) •
        wedgeRep _ (if CMPerm.crosses G ((CMPerm.base G).symm τ') then twist n L g else g)
          (factorEquiv h hsum G hG τ' y) := by
  unfold factorEquiv
  split_ifs with hc
  · have hdet : ((twist n L g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det =
        ((g : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
      have := congrArg Units.val (det_twist n L g)
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    rw [wedgeRep_apply, wedgeRep_apply, map_smul, crossing_map, smul_smul, smul_smul, hdet,
      inv_inv]
  · rw [one_smul]
    apply Subtype.ext
    rw [LinearEquiv.coe_ofEq_apply, coe_wedgeRep_apply, coe_wedgeRep_apply,
      LinearEquiv.coe_ofEq_apply]

/-- The exterior degrees `k τ = h (τ, false) = n - h (τ, true)`. -/
abbrev hodgeDegrees {S : Type u} (h : S × Bool → ℕ) : S → ℕ := fun τ => h (τ, false)

/-- The Frobenius operator `R : W ≃ W`: reindex the factors along the base permutation
of `G` and apply `factorEquiv` at each factor. -/
def frobOp : KottwitzSpace S n L (hodgeDegrees h) ≃ₗ[L] KottwitzSpace S n L (hodgeDegrees h) :=
  (PiTensorProduct.reindex L (fun τ => ⋀[L]^(h (τ, false)) (Fin n → L)) (CMPerm.base G)).trans
    (PiTensorProduct.congr (factorEquiv h hsum G hG))

omit [Fintype S] in
theorem frobOp_tprod (m : ∀ τ, ⋀[L]^(h (τ, false)) (Fin n → L)) :
    frobOp h hsum G hG (PiTensorProduct.tprod L m) =
      PiTensorProduct.tprod L
        (fun τ' => factorEquiv h hsum G hG τ' (m ((CMPerm.base G).symm τ'))) := by
  simp [frobOp]

/-- `R ∘ r(x) = r(G·x) ∘ R` on the dual group. -/
theorem frobOp_mul_dualRep (x : DualGroup S n L) :
    frobOp h hsum G hG * dualRep (hodgeDegrees h) x =
      dualRep (hodgeDegrees h) (dualEndo G x) * frobOp h hsum G hG := by
  refine kottwitzSpace_ext fun m => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dualRep_tprod, map_smul, frobOp_tprod,
    frobOp_tprod, dualRep_tprod]
  simp_rw [factorEquiv_wedgeRep, dualEndo_snd]
  rw [MultilinearMap.map_smul_univ, smul_smul]
  congr 1
  rw [dualEndo_fst, Units.val_mul, Units.coe_prod, mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  refine (Equiv.prod_comp (CMPerm.base G).symm (fun τ =>
    if CMPerm.crosses G τ then ((x.2 τ : Matrix (Fin n) (Fin n) L).det)⁻¹ else 1)).trans ?_
  refine Finset.prod_congr rfl fun τ _ => ?_
  split_ifs <;> simp [Matrix.GeneralLinearGroup.val_det_apply]

theorem dualRep_dualEndo (x : DualGroup S n L) :
    dualRep (hodgeDegrees h) (dualEndo G x) =
      frobOp h hsum G hG * dualRep (hodgeDegrees h) x * (frobOp h hsum G hG)⁻¹ := by
  rw [frobOp_mul_dualRep, mul_inv_cancel_right]

theorem dualRep_zpow (z : ℤ) (x : DualGroup S n L) :
    dualRep (hodgeDegrees h) ((dualAction S n L G ^ z) x) =
      frobOp h hsum G hG ^ z * dualRep (hodgeDegrees h) x * (frobOp h hsum G hG ^ z)⁻¹ := by
  induction z using Int.induction_on generalizing x with
  | zero => simp
  | succ z ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, dualAction_apply, dualRep_dualEndo h hsum G hG,
      zpow_add_one]
    group
  | pred z ih =>
    have hx : x = dualAction S n L G ((dualAction S n L G)⁻¹ x) := by
      rw [MulAut.apply_inv_self]
    rw [zpow_sub_one, MulAut.mul_apply, ih]
    conv_rhs => rw [hx]
    rw [dualAction_apply, dualRep_dualEndo h hsum G hG, zpow_sub_one]
    group

/-- Kottwitz's representation `r` of the unramified L-group `Ĝ ⋊ ℤ` on
`W = ⨂_τ ⋀^{n - n(Φτ)} Lⁿ`. -/
def kottwitzRep : LGroup S n L G →*
    (KottwitzSpace S n L (hodgeDegrees h) ≃ₗ[L] KottwitzSpace S n L (hodgeDegrees h)) :=
  SemidirectProduct.lift (dualRep (hodgeDegrees h))
    (zpowersHom _ (frobOp h hsum G hG))
    (fun g => MonoidHom.ext fun x => by
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, zpowersHom_apply]
      exact dualRep_zpow h hsum G hG _ x)

theorem kottwitzRep_inl (x : DualGroup S n L) :
    kottwitzRep h hsum G hG (SemidirectProduct.inl x) = dualRep (hodgeDegrees h) x :=
  SemidirectProduct.lift_inl _ _ _ _

theorem kottwitzRep_frob :
    kottwitzRep h hsum G hG (LGroup.frob (n := n) (L := L) G) = frobOp h hsum G hG := by
  simp [kottwitzRep, LGroup.frob]

/-! #### Kottwitz's condition (b): Frobenius fixes the highest weight vector -/

theorem hwVector_coe_congr {k k' : ℕ} (e : k = k') (hk : k ≤ n) (hk' : k' ≤ n) :
    (hwVector (L := L) k hk : ExteriorAlgebra L (Fin n → L)) =
      (hwVector (L := L) k' hk' : ExteriorAlgebra L (Fin n → L)) := by
  subst e
  rfl

omit [Fintype S] in
include hsum in
theorem hodge_false_le (τ : S) : h (τ, false) ≤ n := by
  have := hsum τ
  omega

/-- The highest weight vector `⨂_τ e₀ ∧ ⋯ ∧ e_{k τ - 1}` of `W`. -/
def hwTensor : KottwitzSpace S n L (hodgeDegrees h) :=
  PiTensorProduct.tprod L (fun τ => hwVector (h (τ, false)) (hodge_false_le h hsum τ))

omit [Fintype S] in
theorem factorEquiv_hwVector (τ' : S) :
    factorEquiv h hsum G hG τ' (hwVector _ (hodge_false_le h hsum _)) =
      hwVector (L := L) (h (τ', false)) (hodge_false_le h hsum τ') := by
  unfold factorEquiv
  split_ifs with hc
  · exact crossing_hwVector _ _ _
  · apply Subtype.ext
    rw [LinearEquiv.coe_ofEq_apply]
    exact hwVector_coe_congr (by simpa using (hodge_eq_of_not_crosses h G hG hc).symm) _ _

/-- Kottwitz's condition (b): the Frobenius element `1 ⋊ Φ` fixes the highest weight
vector. -/
theorem kottwitzRep_frob_hwTensor :
    kottwitzRep h hsum G hG (LGroup.frob (n := n) (L := L) G) (hwTensor h hsum) =
      hwTensor (L := L) h hsum := by
  rw [kottwitzRep_frob, hwTensor, frobOp_tprod]
  simp only [factorEquiv_hwVector]

/-! #### The weight of the highest weight vector -/

/-- The diagonal element of `GL_n(L)` with unit entries `s`. -/
def diagUnit {n : ℕ} (s : Fin n → Lˣ) : GL (Fin n) L :=
  ⟨Matrix.diagonal (fun j => (s j : L)), Matrix.diagonal (fun j => (((s j)⁻¹ : Lˣ) : L)),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

theorem diagUnit_val {n : ℕ} (s : Fin n → Lˣ) :
    ((diagUnit s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun j => (s j : L)) := rfl

theorem map_diagonal_hwVector {n : ℕ} (d : Fin n → L) (k : ℕ) (hk : k ≤ n) :
    exteriorPower.map k (Matrix.toLin' (Matrix.diagonal d)) (hwVector k hk) =
      (∏ j : Fin k, d (Fin.castLE hk j)) • hwVector k hk := by
  rw [hwVector, map_apply_ιMulti, ← AlternatingMap.map_smul_univ]
  congr 1
  funext j x
  simp only [Function.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal,
    Pi.basisFun_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with hx
  · rw [hx]
  · simp

/-- `ρ_k(diag s)` acts on `e₀ ∧ ⋯ ∧ e_{k-1}` by `∏_{j ≥ k} s_j⁻¹`. -/
theorem wedgeRep_diagUnit_hwVector {n : ℕ} (s : Fin n → Lˣ) (k : ℕ) (hk : k ≤ n) :
    wedgeRep k (diagUnit s) (hwVector k hk) =
      (∏ j : Fin n, if k ≤ (j : ℕ) then ((s j : L))⁻¹ else 1) • hwVector k hk := by
  rw [wedgeRep_apply, diagUnit_val, map_diagonal_hwVector, smul_smul, Matrix.det_diagonal]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  have hcast : ∀ j : Fin k, Fin.castLE hk j = Fin.castAdd m j := fun j => Fin.ext rfl
  have h1 : ∀ i : Fin k, ¬ (k ≤ ((Fin.castAdd m i : Fin (k + m)) : ℕ)) := fun i => by
    simp only [Fin.val_castAdd]
    omega
  have h2 : ∀ i : Fin m, k ≤ ((Fin.natAdd k i : Fin (k + m)) : ℕ) := fun i => by
    simp only [Fin.val_natAdd]
    omega
  simp only [hcast, h1, h2, ite_false, ite_true, Finset.prod_const_one, one_mul, mul_inv,
    Finset.prod_inv_distrib]
  have hA : (∏ i : Fin k, (s (Fin.castAdd m i) : L)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
  rw [mul_comm (∏ i : Fin k, (s (Fin.castAdd m i) : L))⁻¹, mul_assoc, inv_mul_cancel₀ hA,
    mul_one]

/-- Kottwitz's condition (a), weight part: the highest weight vector has weight `μ`,
`μ(ζ, (diag s_τ)_τ) = ζ⁻¹ ∏_τ ∏_{j ≥ k_τ} s_{τ,j}⁻¹`. -/
theorem dualRep_diagUnit_hwTensor (ζ : Lˣ) (s : S → Fin n → Lˣ) :
    dualRep (hodgeDegrees h) (ζ, fun τ => diagUnit (s τ)) (hwTensor h hsum) =
      (((ζ : L))⁻¹ * ∏ τ, ∏ j : Fin n,
        if h (τ, false) ≤ (j : ℕ) then ((s τ j : L))⁻¹ else 1) • hwTensor h hsum := by
  rw [hwTensor, dualRep_tprod]
  simp only [wedgeRep_diagUnit_hwVector]
  rw [MultilinearMap.map_smul_univ, smul_smul]

end Representation

end Langlands.Shimura.KottwitzDual
