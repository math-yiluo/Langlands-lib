import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition
import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Global.RankinSelberg.UnfoldingOrdinary
import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints
import Langlands.Automorphic.CuspidalL2.Basics

/-! # Points supported at one finite place and the unequal-rank Whittaker kernel

For a finite place `v`, the actual adelic point `ι_v(h)` with component `h ∈ GL_m(F_v)` at
`v` and `1` elsewhere (`localPoint`) is multiplicative, has the expected local components,
commutes with every point whose `v`-component is `1`, is compatible with padding, and lies
in `N_m(𝔸)` when `h` is upper unitriangular. From these, the kernel
`W(diag(g, 1)) W'(g) |det g|^(s - (r-t)/2)` of the unequal-rank global Whittaker integral
transforms under left translation by `ι_v(d)` with a scalar factor, for every `d` that
normalizes the upper unitriangular group (in particular for every torus element `ϖ^λ`), as
soon as `W` and `W'` factor at `v` through right `GL(𝒪_v)`-invariant local functions. See the
paired Markdown for the argument.
-/

noncomputable section
universe u
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight (IsUnitriangular)
open UnequalAnalytic (padGL_apply)
open LocalPointFactorization

variable {F : Type u} [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

/-! ### Points supported at one place -/

/-- An adelic point is determined by its infinite and finite parts. -/
theorem adelicGL_ext_infinite_finite {m : ℕ} {x y : AdelicGL F m}
    (h1 : AdelicGL.infinite F m x = AdelicGL.infinite F m y)
    (h2 : AdelicGL.finite F m x = AdelicGL.finite F m y) : x = y := by
  rw [← AdelicGL.pair_projections F m x, ← AdelicGL.pair_projections F m y, h1, h2]

theorem localPoint_one (m : ℕ) (v : FinitePlace F) : localPoint F m v 1 = 1 := by
  simp only [localPoint, map_one]

/-- An entry of `ι_v(h)` equals the corresponding entry of the identity matrix as soon as the
entry of `h` does. -/
theorem adelicEquiv_localPoint_apply_of_eq {m : ℕ} {v : FinitePlace F} (h : FiniteLocalGL F m v)
    {i j : Fin m}
    (hij : (h : Matrix (Fin m) (Fin m) (FiniteCompletion F v)) i j =
      (1 : Matrix (Fin m) (Fin m) (FiniteCompletion F v)) i j) :
    (E m (localPoint F m v h) : Matrix (Fin m) (Fin m) (Adeles F)) i j =
      (1 : Matrix (Fin m) (Fin m) (Adeles F)) i j := by
  rw [adelicEquiv_localPoint F]
  set x := AdelicGL.ofFinite F m (FiniteAdelicGL.localInclusion F m v h)
  have h1 : ((x : Matrix (Fin m) (Fin m) (Adeles F)) i j).1 =
      ((1 : Matrix (Fin m) (Fin m) (Adeles F)) i j).1 := by
    have e := AdelicGL.infinite_apply F m x i j
    rw [infinite_ofFinite F] at e
    rw [← e]
    by_cases hij' : i = j
    · subst hij'
      simp
    · simp [Matrix.one_apply_ne hij']
  have h2 : ((x : Matrix (Fin m) (Fin m) (Adeles F)) i j).2 =
      ((1 : Matrix (Fin m) (Fin m) (Adeles F)) i j).2 := by
    have e := AdelicGL.finite_apply F m x i j
    rw [finite_ofFinite F] at e
    rw [← e]
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    rw [← FiniteAdelicGL.localProjection_apply]
    by_cases hw : w = v
    · subst hw
      rw [FiniteAdelicGL.localProjection_localInclusion, hij]
      by_cases hij' : i = j
      · subst hij'
        (simp; rfl)
      · (simp [Matrix.one_apply_ne hij']; rfl)
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F m v w hw]
      by_cases hij' : i = j
      · subst hij'
        (simp; rfl)
      · (simp [Matrix.one_apply_ne hij']; rfl)
  exact Prod.ext h1 h2

/-- `ι_v(u) ∈ N_m(𝔸)` for every upper unitriangular `u ∈ GL_m(F_v)`. -/
theorem localPoint_mem_unipotentAdelic {m : ℕ} {v : FinitePlace F} {u : FiniteLocalGL F m v}
    (hu : IsUnitriangular (u : Matrix (Fin m) (Fin m) (FiniteCompletion F v))) :
    localPoint F m v u ∈ unipotentAdelic F m :=
  UnramifiedWhittaker.localPoint_mem_unipotentAdelic F v u hu

/-! ### Padding -/

theorem localProjection_padGL {m n : ℕ} (hle : m ≤ n) (w : FinitePlace F)
    (x : FiniteAdelicGL F m) :
    FiniteAdelicGL.localProjection F n w (padGL hle x) =
      padGL hle (FiniteAdelicGL.localProjection F m w x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [FiniteAdelicGL.localProjection_apply, padGL_apply, padGL_apply]
  split_ifs with hij
  · rfl
  · by_cases hij' : i = j
    · subst hij'
      (simp; rfl)
    · (simp [Matrix.one_apply_ne hij']; rfl)

theorem finite_padGL {m n : ℕ} (hle : m ≤ n) (x : AdelicGL F m) :
    AdelicGL.finite F n (padGL hle x) = padGL hle (AdelicGL.finite F m x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.finite_apply, padGL_apply, padGL_apply]
  split_ifs with hij
  · rfl
  · by_cases hij' : i = j
    · subst hij'
      simp
    · simp [Matrix.one_apply_ne hij']

theorem infinite_padGL {m n : ℕ} (hle : m ≤ n) (x : AdelicGL F m) :
    AdelicGL.infinite F n (padGL hle x) = padGL hle (AdelicGL.infinite F m x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.infinite_apply, padGL_apply, padGL_apply]
  split_ifs with hij
  · rfl
  · by_cases hij' : i = j
    · subst hij'
      simp
    · simp [Matrix.one_apply_ne hij']

theorem finiteComponent_pad {m n : ℕ} (hle : m ≤ n) (v : FinitePlace F) (g : Points F m) :
    finiteComponent F n v (pad F hle g) = padGL hle (finiteComponent F m v g) := by
  rw [finiteComponent, UnequalAnalytic.adelicEquiv_pad, finite_padGL, localProjection_padGL]
  rfl

/-- `diag(ι_v(h), 1) = ι_v(diag(h, 1))`. -/
theorem pad_localPoint {m n : ℕ} (hle : m ≤ n) (v : FinitePlace F) (h : FiniteLocalGL F m v) :
    pad F hle (localPoint F m v h) = localPoint F n v (padGL hle h) := by
  apply (E n).injective
  rw [UnequalAnalytic.adelicEquiv_pad, adelicEquiv_localPoint F, adelicEquiv_localPoint F]
  apply adelicGL_ext_infinite_finite
  · rw [infinite_padGL, infinite_ofFinite F, infinite_ofFinite F, map_one]
  · rw [finite_padGL, finite_ofFinite F, finite_ofFinite F]
    apply FiniteAdelicGL.ext_localProjection
    intro w
    rw [localProjection_padGL]
    by_cases hw : w = v
    · subst hw
      rw [FiniteAdelicGL.localProjection_localInclusion,
        FiniteAdelicGL.localProjection_localInclusion]
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F m v w hw,
        FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw, map_one]

/-- Padding preserves `GL(𝒪_v)`. -/
theorem padGL_mem_localIntegral {m n : ℕ} (hle : m ≤ n) {v : FinitePlace F}
    {k : FiniteLocalGL F m v} (hk : k ∈ FiniteAdelicGL.localIntegral F m v) :
    padGL hle k ∈ FiniteAdelicGL.localIntegral F n v := by
  rw [FiniteAdelicGL.mem_localIntegral] at hk ⊢
  have hinv : (padGL hle k)⁻¹ = padGL hle k⁻¹ := (map_inv _ _).symm
  have hone : ∀ i j : Fin n,
      (1 : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) i j ∈ v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [padGL_apply]
    split_ifs
    · exact hk.1 _ _
    · exact hone i j
  · rw [hinv, padGL_apply]
    split_ifs
    · exact hk.2 _ _
    · exact hone i j

/-! ### Torus conjugation -/

open GeneralLinear.Iwasawa in
/-- Conjugation by a torus element preserves upper unitriangularity. -/
theorem isUnitriangular_torus_conj {K : Type*} [Field K] {m : ℕ} (ϖ : Kˣ) (lam : Fin m → ℤ)
    {u : Matrix.GeneralLinearGroup (Fin m) K}
    (hu : IsUnitriangular (u : Matrix (Fin m) (Fin m) K)) :
    IsUnitriangular ((torus ϖ lam * u * (torus ϖ lam)⁻¹ : Matrix.GeneralLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K) := by
  rw [torus_inv]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [torus, diagonalUnits_mul_mul_apply, hu.1 hij, mul_zero, zero_mul]
  · rw [torus, diagonalUnits_mul_mul_apply, hu.2 i, mul_one, Units.mul_inv]

/-! ### The kernel -/

section Kernel

variable {r t : ℕ} (h : t < r) {W : Points F (r + 1) → ℂ} {W' : Points F (t + 1) → ℂ}
  {v : FinitePlace F} {φ : FiniteLocalGL F (r + 1) v → ℂ} {φ' : FiniteLocalGL F (t + 1) v → ℂ}

/-- If `W` and `W'` factor at `v` through `φ` and `φ'`, then so does the kernel at points with
`v`-component `1`. -/
theorem ordinaryKernel_mul_localPoint
    (hW : ∀ g : Points F (r + 1), finiteComponent F (r + 1) v g = 1 →
      ∀ k, W (g * localPoint F (r + 1) v k) = W g * φ k)
    (hW' : ∀ g : Points F (t + 1), finiteComponent F (t + 1) v g = 1 →
      ∀ k, W' (g * localPoint F (t + 1) v k) = W' g * φ' k)
    (s : ℂ) {g : Points F (t + 1)} (hg : finiteComponent F (t + 1) v g = 1)
    (k : FiniteLocalGL F (t + 1) v) :
    Unfolding.ordinaryKernel F h W W' s (g * localPoint F (t + 1) v k) =
      Unfolding.ordinaryKernel F h W W' s g *
        (φ (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) k) * φ' k *
          detPower F (t + 1) (localPoint F (t + 1) v k) (s - ((r - t : ℕ) : ℂ) / 2)) := by
  have hpad : finiteComponent F (r + 1) v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) = 1 := by
    rw [finiteComponent_pad, hg, map_one]
  unfold Unfolding.ordinaryKernel
  rw [UnequalAnalytic.pad_mul, pad_localPoint, hW _ hpad, hW' _ hg, Unfolding.detPower_mul]
  ring

/-- **Pointwise factorization of the kernel.** Let `g_v ∈ N_m(F_v) GL_m(𝒪_v)`, `m = t + 1`,
and let `d ∈ GL_m(F_v)` normalize the upper unitriangular group. If the kernel is left
`N_m(𝔸)`-invariant and `W`, `W'` factor at `v` through right `GL(𝒪_v)`-invariant functions
`φ`, `φ'` with `φ(1) = φ'(1) = 1`, then
`K(ι_v(d) g) = φ(diag(d, 1)) φ'(d) |det ι_v(d)|^(s - (r-t)/2) K(g)`. -/
theorem ordinaryKernel_localPoint_mul
    (hW : ∀ g : Points F (r + 1), finiteComponent F (r + 1) v g = 1 →
      ∀ k, W (g * localPoint F (r + 1) v k) = W g * φ k)
    (hW' : ∀ g : Points F (t + 1), finiteComponent F (t + 1) v g = 1 →
      ∀ k, W' (g * localPoint F (t + 1) v k) = W' g * φ' k)
    (hφ : ∀ x k, k ∈ FiniteAdelicGL.localIntegral F (r + 1) v → φ (x * k) = φ x)
    (hφ' : ∀ x k, k ∈ FiniteAdelicGL.localIntegral F (t + 1) v → φ' (x * k) = φ' x)
    (hφ1 : φ 1 = 1) (hφ'1 : φ' 1 = 1) (s : ℂ)
    (hN : ∀ n ∈ unipotentAdelic F (t + 1), ∀ x,
      Unfolding.ordinaryKernel F h W W' s (n * x) = Unfolding.ordinaryKernel F h W W' s x)
    (d : FiniteLocalGL F (t + 1) v)
    (hd : ∀ u : FiniteLocalGL F (t + 1) v,
      IsUnitriangular (u : Matrix (Fin (t + 1)) (Fin (t + 1)) (FiniteCompletion F v)) →
      IsUnitriangular ((d * u * d⁻¹ : FiniteLocalGL F (t + 1) v) :
        Matrix (Fin (t + 1)) (Fin (t + 1)) (FiniteCompletion F v)))
    {g : Points F (t + 1)} (hg : IsUnipotentIntegral F (t + 1) v (finiteComponent F (t + 1) v g)) :
    Unfolding.ordinaryKernel F h W W' s (localPoint F (t + 1) v d * g) =
      (φ (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) d) * φ' d *
          detPower F (t + 1) (localPoint F (t + 1) v d) (s - ((r - t : ℕ) : ℂ) / 2)) *
        Unfolding.ordinaryKernel F h W W' s g := by
  set hle := Nat.le_of_lt (Nat.succ_lt_succ h)
  set s' : ℂ := s - ((r - t : ℕ) : ℂ) / 2
  obtain ⟨k, hk, hdiag, hlow⟩ := hg
  set gv := finiteComponent F (t + 1) v g
  set u : FiniteLocalGL F (t + 1) v := gv * k
  have hu : IsUnitriangular (u : Matrix (Fin (t + 1)) (Fin (t + 1)) (FiniteCompletion F v)) :=
    ⟨fun i j hij => hlow i j hij, hdiag⟩
  set g' := (localPoint F (t + 1) v gv)⁻¹ * g
  have hg' : finiteComponent F (t + 1) v g' = 1 := by
    rw [finiteComponent_mul, ← WhittakerCell.localPoint_inv, finiteComponent_localPoint F, inv_mul_cancel]
  have hdecomp (e : FiniteLocalGL F (t + 1) v) :
      localPoint F (t + 1) v e * g =
        localPoint F (t + 1) v (e * u * e⁻¹) * (g' * localPoint F (t + 1) v (e * k⁻¹)) := by
    have e1 : e * u * e⁻¹ * (e * k⁻¹) = e * gv := by simp [u, mul_assoc]
    rw [← localPoint_mul_comm F (t + 1) v (e * k⁻¹) hg', ← mul_assoc, ← localPoint_mul F, e1,
      localPoint_mul F, mul_assoc, mul_inv_cancel_left]
  have key (e : FiniteLocalGL F (t + 1) v)
      (he : IsUnitriangular ((e * u * e⁻¹ : FiniteLocalGL F (t + 1) v) :
        Matrix (Fin (t + 1)) (Fin (t + 1)) (FiniteCompletion F v))) :
      Unfolding.ordinaryKernel F h W W' s (localPoint F (t + 1) v e * g) =
        Unfolding.ordinaryKernel F h W W' s g' *
          (φ (padGL hle e) * φ' e * (detPower F (t + 1) (localPoint F (t + 1) v e) s' *
            detPower F (t + 1) (localPoint F (t + 1) v k⁻¹) s')) := by
    rw [hdecomp e, hN _ (localPoint_mem_unipotentAdelic he),
      ordinaryKernel_mul_localPoint h hW hW' s hg', map_mul,
      hφ _ _ (padGL_mem_localIntegral hle (inv_mem hk)), hφ' _ _ (inv_mem hk), localPoint_mul F,
      Unfolding.detPower_mul]
  have k1 := key 1 (by simpa using hu)
  simp only [localPoint_one, one_mul, map_one, hφ1, hφ'1] at k1
  rw [key d (hd u hu), k1]
  have hD1 : detPower F (t + 1) (1 : Points F (t + 1)) s' = 1 := by
    simp [detPower, detNorm]
  rw [hD1]
  ring

end Kernel

end Langlands.Global.RankinSelbergGlobal
