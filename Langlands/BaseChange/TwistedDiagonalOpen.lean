import Langlands.BaseChange.Norm
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units

/-! # Open neighborhoods from diagonal twisted conjugation -/

noncomputable section

namespace Langlands.BaseChange

open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator RightActions Ring
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)

universe u v

/-- Twist the diagonals in `A` by the prescribed subgroup. -/
def twistedDiagonalSaturation {F : Type u} [CommRing F] {E : Type v} [Field E] [Algebra F E]
    {n : ℕ} (σ : E ≃ₐ[F] E) (K : Subgroup (GeneralLinear n E)) (A : Set (Fin n → Eˣ)) :
    Set (GeneralLinear n E) :=
  {g | ∃ k ∈ K, ∃ a ∈ A, k⁻¹ * diagonalUnits a * entrywiseAut σ n k = g}

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  {E : Type v} [NormedField E] [NormedAlgebra F E] [FiniteDimensional F E]
  {n : ℕ} (σ : E ≃ₐ[F] E)

local notation "M" => Matrix (Fin n) (Fin n) E

private def diagonalProjection : M →L[F] M :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => diagonal X.diag
      map_add' X Y := by ext i j; by_cases h : i = j <;> simp [h, Matrix.diag]
      map_smul' c X := by ext i j; by_cases h : i = j <;> simp [h, Matrix.diag] }

private theorem twistedDiagonal_neighborhood (K : OpenSubgroup (GeneralLinear n E))
    (A : Set (Fin n → Eˣ)) (a : Fin n → Eˣ) (ha : a ∈ A)
    (hA : IsOpen ((fun b : Fin n → Eˣ => fun i => (b i : E)) '' A))
    (hReg : ∀ (i j : Fin n), i ≠ j → ∀ z : E,
      (a i : E) * σ z = (a j : E) * z → z = 0) :
    twistedDiagonalSaturation σ K.toSubgroup A ∈ nhds (diagonalUnits a) := by
  classical
  let : CompleteSpace M := FiniteDimensional.complete F M
  let P : M →L[F] M := diagonalProjection
  let U : M →L[F] M := ContinuousLinearMap.id F M - P
  let S : M →L[F] M := σ.toLinearMap.mapMatrix.toContinuousLinearMap.comp U
  let D : M := (diagonalUnits a : GeneralLinear n E).val
  let k (x : M) := 1 + U x
  let d (x : M) := D + P x
  let s (x : M) := 1 + S x
  let f (x : M) := Ring.inverse (k x) * d x * s x
  let Df : M →L[F] M := -(U <• D) + P + D • S
  have hP (x : M) : P x = diagonal x.diag := rfl
  have hU (x : M) : U x = x - diagonal x.diag := rfl
  have hS (x : M) (i j : Fin n) : S x i j = σ (U x i j) := rfl
  have hD : D = diagonal (fun i => (a i : E)) := diagonalUnits_val a
  have hDeriv : HasStrictFDerivAt f Df 0 := by
    have hk : HasStrictFDerivAt k U 0 := U.hasStrictFDerivAt.const_add (c := 1)
    have hd : HasStrictFDerivAt d P 0 := P.hasStrictFDerivAt.const_add (c := D)
    have hs : HasStrictFDerivAt s S 0 := S.hasStrictFDerivAt.const_add (c := 1)
    have hki : k 0 = 1 := by simp [k]
    have hi : HasStrictFDerivAt (fun x : M => Ring.inverse x)
        (-ContinuousLinearMap.id F M) (k 0) := by
      rw [hki]
      have h₁ : ContinuousLinearMap.mulLeftRight F M 1 1 = ContinuousLinearMap.id F M := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one]
        rfl
      have hr := hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Mˣ)
      simp only [inv_one, Units.val_one, h₁] at hr
      convert! hr using 1
    have h := ((hi.comp 0 hk).mul' hd).mul' hs
    have hDform : (Ring.inverse (k 0) * d 0) • S +
        ((Ring.inverse (k 0)) • P + ((-ContinuousLinearMap.id F M).comp U) <• d 0) <• s 0 = Df := by
      apply ContinuousLinearMap.ext
      intro x
      simp [Df, hki, d, s, Ring.inverse_one, add_comm, add_left_comm]
    rw [← hDform]
    exact h
  have hInj : Function.Injective Df := by
    apply (injective_iff_map_eq_zero Df.toLinearMap).2
    intro x hx
    have hh (i j : Fin n) : Df x i j =
        -(U x i j * (a j : E)) + P x i j + (a i : E) * S x i j := by
      change ((-(U x * D) + P x) + D * S x) i j = _
      rw [hD]
      simp
    ext i j
    have hij := congrArg (fun Y : M => Y i j) hx
    change Df x i j = 0 at hij
    rw [hh, hS, hU, hP] at hij
    by_cases h : i = j
    · subst j
      simpa using hij
    · simp only [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h,
        sub_zero, add_zero] at hij
      have hz : (a i : E) * σ (x i j) = (a j : E) * x i j := by
        linear_combination hij
      exact hReg i j h (x i j) hz
  have hSurj : Df.range = ⊤ := LinearMap.range_eq_top.mpr
    (LinearMap.injective_iff_surjective.mp hInj)
  have hf0 : f 0 = D := by simp [f, k, d, s, Ring.inverse_one]
  have hNearK : ∀ᶠ x : M in nhds 0, k x ∈
      (Units.val : GeneralLinear n E → M) '' (K : Set (GeneralLinear n E)) := by
    apply (continuous_const.add U.continuous).continuousAt.eventually
    have hOpen := Units.isOpenEmbedding_val.isOpenMap _ K.isOpen
    have hone : k 0 ∈ (Units.val : GeneralLinear n E → M) '' (K : Set (GeneralLinear n E)) :=
      ⟨1, K.one_mem, by simp [k]⟩
    exact hOpen.mem_nhds hone
  have hNearA : ∀ᶠ x : M in nhds 0,
      (fun i => (a i : E) + x i i) ∈ (fun b : Fin n → Eˣ => fun i => (b i : E)) '' A := by
    have hc : Continuous (fun x : M => fun i => (a i : E) + x i i) :=
      continuous_pi fun i => continuous_const.add ((continuous_apply i).comp (continuous_apply i))
    apply hc.continuousAt.eventually
    exact hA.mem_nhds ⟨a, ha, by funext i; simp⟩
  have hIm : (Units.val : GeneralLinear n E → M) ''
      twistedDiagonalSaturation σ K.toSubgroup A ∈ nhds D := by
    have hm : Filter.map f (nhds (0 : M)) = nhds D :=
      (hDeriv.map_nhds_eq_of_surj hSurj).trans (congrArg (fun x : M => nhds x) hf0)
    rw [← hm]
    change ∀ᶠ x : M in nhds 0, f x ∈ _
    filter_upwards [hNearK, hNearA] with x hx hy
    obtain ⟨g, hg, hgx⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hy
    refine ⟨g⁻¹ * diagonalUnits b * entrywiseAut σ n g, ⟨g, hg, b, hb, rfl⟩, ?_⟩
    have hdiag : (diagonalUnits b : GeneralLinear n E).val = d x := by
      rw [diagonalUnits_val, show d x = D + P x from rfl, hD, hP]
      ext i j
      by_cases h : i = j
      · subst j; simpa using congrFun hbx i
      · simp [h]
    have hAut : (entrywiseAut σ n g).val = s x := by
      change (g.val).map σ.toRingHom = 1 + S x
      rw [hgx]
      ext i j
      change σ ((1 + U x) i j) = (1 + S x) i j
      simp [hS, Matrix.one_apply]
    have hInv : (g⁻¹ : GeneralLinear n E).val = Ring.inverse (k x) := by
      rw [← hgx, Ring.inverse_unit]
    simp only [Units.val_mul, hdiag, hInv, hAut, f]
  have hCont := Units.continuous_val.continuousAt (x := diagonalUnits a)
  apply Filter.mem_of_superset (hCont.preimage_mem_nhds hIm)
  rintro y ⟨z, hz, hzy⟩
  exact (Units.ext hzy : z = y) ▸ hz

/-- The twisted saturation is open if the diagonal entries vary in an open
set and each off-diagonal twisted linear equation has zero kernel. -/
theorem isOpen_twistedDiagonalSaturation (K : OpenSubgroup (GeneralLinear n E))
    (A : Set (Fin n → Eˣ))
    (hA : IsOpen ((fun b : Fin n → Eˣ => fun i => (b i : E)) '' A))
    (hReg : ∀ a ∈ A, ∀ i j : Fin n, i ≠ j → ∀ z : E,
      (a i : E) * σ z = (a j : E) * z → z = 0) :
    IsOpen (twistedDiagonalSaturation σ K.toSubgroup A) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨g, hg, a, ha, rfl⟩
  let e : GeneralLinear n E ≃ₜ GeneralLinear n E :=
    (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight (entrywiseAut σ n g))
  have he : e (diagonalUnits a) = g⁻¹ * diagonalUnits a * entrywiseAut σ n g := rfl
  rw [← he, ← e.map_nhds_eq]
  apply Filter.mem_of_superset (twistedDiagonal_neighborhood σ K A a ha hA (hReg a ha))
  rintro z ⟨k, hk, b, hb, rfl⟩
  refine ⟨k * g, K.mul_mem hk hg, b, hb, ?_⟩
  change (k * g)⁻¹ * diagonalUnits b * entrywiseAut σ n (k * g) =
    (g⁻¹ * (k⁻¹ * diagonalUnits b * entrywiseAut σ n k)) * entrywiseAut σ n g
  rw [_root_.mul_inv_rev, map_mul]
  simp only [mul_assoc]

end Langlands.BaseChange
