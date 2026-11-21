import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.UnfoldingDualGL
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices
import Langlands.Representation.Whittaker.DualTransform

/-! # Unequal-rank local kernels at a class, from left equivariance

Over any field `K`, if `W` on `GL_(r+1)(K)` transforms on the left under the upper unitriangular
group by `χ(∑ u_(i,i+1))` and `W'` on `GL_(t+1)(K)` by the inverse character, then the integrand
of `Ψ(s; W, W')` and the dual block kernel of the Library's `ArchimedeanLocal` definitions,
evaluated at the class of `g`, may be computed with the representative `g` itself.
See the paired Markdown.
-/

noncomputable section
open Langlands.GeneralLinear
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnequalLocalKernels

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)

variable {K : Type*} [Field K] {r t : ℕ}

/-- `diag(u, I)` is upper unitriangular when `u` is. -/
theorem padGL_mem_upperUnipotent (hp : t + 1 ≤ r + 1) (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K) :
    padGL hp u.val ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) K := by
  constructor
  · intro i j hij
    change j < i at hij
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_eq_zero u hij
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_diag u _
    · exact Matrix.one_apply_eq i

/-- `diag(u, I)` as an element of the upper unitriangular group. -/
def padUnipotent (hp : t + 1 ≤ r + 1) (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K) :
    Langlands.GeneralLinear.upperUnipotent (r + 1) K :=
  ⟨padGL hp u.val, padGL_mem_upperUnipotent hp u⟩

/-- The superdiagonal sum of `diag(u, I)` is that of `u`. -/
theorem sum_padUnipotent (hp : t + 1 ≤ r + 1) (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K) :
    (∑ i : Fin r, (padUnipotent hp u).val i.castSucc i.succ) =
      ∑ i : Fin t, u.val i.castSucc i.succ :=
  Unfolding.sum_superdiag_padGL hp u.val

/-- An additive character into `ℂ` takes nonzero values. -/
theorem addChar_ne_zero (χ : AddChar K ℂ) (a : K) : χ a ≠ 0 := by
  intro h0
  have h1 := AddChar.map_zero_eq_one χ
  rw [← add_neg_cancel a, AddChar.map_add_eq_mul, h0, zero_mul] at h1
  exact zero_ne_one h1

/-- Left multiplication by a unitriangular matrix does not change `|det g|^s`. -/
theorem detPower_unipotent_mul (nabs : K → ℝ) {n : ℕ}
    (u : Langlands.GeneralLinear.upperUnipotent n K)
    (g : Langlands.GeneralLinear n K) (s : ℂ) :
    ArchimedeanLocal.detPower nabs (u.val * g) s = ArchimedeanLocal.detPower nabs g s := by
  have hu : Matrix.det u.val.val = 1 := by
    rw [Matrix.det_of_isUpperTriangular u.property.1]
    simp only [UpperUnipotent.entry_diag, Finset.prod_const_one]
  simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, hu, one_mul]

/-- Left multiplication of the leading block of the rectangular point. -/
theorem rectangularPoint_mul_left (h : t < r) (u g : Langlands.GeneralLinear (t + 1) K)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) K) :
    ArchimedeanLocal.rectangularPoint h (u * g) x =
      padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) u * ArchimedeanLocal.rectangularPoint h g x := by
  simp only [ArchimedeanLocal.rectangularPoint, GeneralLinear.lowerBlockLocalization,
    Unfolding.lowerBlockPair_mul_left, map_mul]
  rw [Unfolding.reindex_rankInclusion_rankInclusion]

/-- Left `χ`-equivariance on `GL_(n+1)(K)`: `W(u g) = χ(∑ u_(i,i+1)) W(g)`. -/
def IsLeftEquivariant (n : ℕ) (χ : AddChar K ℂ) (W : Langlands.GeneralLinear (n + 1) K → ℂ) :
    Prop :=
  ∀ (u : Langlands.GeneralLinear.upperUnipotent (n + 1) K) (g : Langlands.GeneralLinear (n + 1) K),
    W (u.val * g) = χ (∑ i : Fin n, u.val i.castSucc i.succ) * W g

/-- Left `χ⁻¹`-equivariance on `GL_(n+1)(K)`: `W(u g) = χ(∑ u_(i,i+1))⁻¹ W(g)`. -/
def IsLeftInverseEquivariant (n : ℕ) (χ : AddChar K ℂ)
    (W : Langlands.GeneralLinear (n + 1) K → ℂ) : Prop :=
  ∀ (u : Langlands.GeneralLinear.upperUnipotent (n + 1) K) (g : Langlands.GeneralLinear (n + 1) K),
    W (u.val * g) = (χ (∑ i : Fin n, u.val i.castSucc i.succ))⁻¹ * W g

/-- `w ᵗ(u g)⁻¹ = (w ᵗu⁻¹ w) · w ᵗg⁻¹`, with `w ᵗu⁻¹ w` the Library's reflected unipotent. -/
theorem dualArgument_left_unipotent {n : ℕ}
    (u : Langlands.GeneralLinear.upperUnipotent (n + 1) K)
    (g : Langlands.GeneralLinear (n + 1) K) :
    weylLong (n + 1) K * inverseTranspose (n + 1) K (u.val * g) =
      (Whittaker.reflectedUnipotent u).val *
        (weylLong (n + 1) K * inverseTranspose (n + 1) K g) := by
  simp only [map_mul, Whittaker.reflectedUnipotent_val]
  calc
    _ = (weylLong (n + 1) K * inverseTranspose (n + 1) K u.val) *
        ((weylLong (n + 1) K * weylLong (n + 1) K) * inverseTranspose (n + 1) K g) := by
      rw [weylLong_mul_self, one_mul, mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- The dual `W̃(g) = W(w ᵗg⁻¹)` of a left `χ`-equivariant function is left equivariant for
`u ↦ χ(-∑ u_(i,i+1))`. -/
theorem dualFunction_mul_left {n : ℕ} {χ : AddChar K ℂ}
    {W : Langlands.GeneralLinear (n + 1) K → ℂ}
    (hW : ∀ (u : Langlands.GeneralLinear.upperUnipotent (n + 1) K) g, W (u.val * g) =
      χ (∑ i : Fin n, u.val i.castSucc i.succ) * W g)
    (u : Langlands.GeneralLinear.upperUnipotent (n + 1) K) (g : Langlands.GeneralLinear (n + 1) K) :
    ArchimedeanLocal.dualFunction (n + 1) W (u.val * g) =
      χ (-(∑ i : Fin n, u.val i.castSucc i.succ)) *
        ArchimedeanLocal.dualFunction (n + 1) W g := by
  change W (weylLong (n + 1) K * inverseTranspose (n + 1) K (u.val * g)) =
    _ * W (weylLong (n + 1) K * inverseTranspose (n + 1) K g)
  rw [dualArgument_left_unipotent, hW, Whittaker.reflectedUnipotent_sum]

/-- The same for an inverse-equivariant function. -/
theorem dualFunction_mul_left_inv {n : ℕ} {χ : AddChar K ℂ}
    {W : Langlands.GeneralLinear (n + 1) K → ℂ}
    (hW : IsLeftInverseEquivariant n χ W)
    (u : Langlands.GeneralLinear.upperUnipotent (n + 1) K) (g : Langlands.GeneralLinear (n + 1) K) :
    ArchimedeanLocal.dualFunction (n + 1) W (u.val * g) =
      (χ (-(∑ i : Fin n, u.val i.castSucc i.succ)))⁻¹ *
        ArchimedeanLocal.dualFunction (n + 1) W g := by
  change W (weylLong (n + 1) K * inverseTranspose (n + 1) K (u.val * g)) =
    _ * W (weylLong (n + 1) K * inverseTranspose (n + 1) K g)
  rw [dualArgument_left_unipotent, hW, Whittaker.reflectedUnipotent_sum]

/-- A function invariant under left translation by `N_(t+1)(K)` may be evaluated at the
representative `(Quotient.mk g).out` or at `g`. -/
theorem apply_out_mk {A : Type*} (f : Langlands.GeneralLinear (t + 1) K → A)
    (hf : ∀ (u : Langlands.GeneralLinear.upperUnipotent (t + 1) K) g, f (u.val * g) = f g)
    (g : Langlands.GeneralLinear (t + 1) K) :
    f (Quotient.mk'' g : LeftUnipotentQuotient t K).out = f g := by
  let q : LeftUnipotentQuotient t K := Quotient.mk'' g
  have hq : (Quotient.mk'' q.out : LeftUnipotentQuotient t K) = Quotient.mk'' g :=
    Quotient.out_eq q
  have hu : q.out * g⁻¹ ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) K :=
    (LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hq.symm
  let u : Langlands.GeneralLinear.upperUnipotent (t + 1) K := ⟨q.out * g⁻¹, hu⟩
  have he : q.out = u.val * g := by dsimp [u]; group
  change f q.out = f g
  rw [he, hf]

/-- **The ordinary integrand at a class.** -/
theorem unequalIntegrand_mk (nabs : K → ℝ) (h : t < r) (χ : AddChar K ℂ)
    {W : Langlands.GeneralLinear (r + 1) K → ℂ} {W' : Langlands.GeneralLinear (t + 1) K → ℂ}
    (hW : IsLeftEquivariant r χ W) (hW' : IsLeftInverseEquivariant t χ W')
    (s : ℂ) (g : Langlands.GeneralLinear (t + 1) K) :
    ArchimedeanLocal.unequalIntegrand nabs h W W' s (Quotient.mk'' g) =
      W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * W' g *
        ArchimedeanLocal.detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2) := by
  refine apply_out_mk (fun g => W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * W' g *
    ArchimedeanLocal.detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2)) ?_ g
  intro u g
  have hp := hW (padUnipotent (Nat.le_of_lt (Nat.succ_lt_succ h)) u)
    (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g)
  rw [sum_padUnipotent] at hp
  have hne := addChar_ne_zero χ (∑ i : Fin t, u.val i.castSucc i.succ)
  rw [map_mul]
  change W ((padUnipotent (Nat.le_of_lt (Nat.succ_lt_succ h)) u).val *
    padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * W' (u.val * g) *
      ArchimedeanLocal.detPower nabs (u.val * g) _ = _
  rw [hp, hW' u g, detPower_unipotent_mul]
  field_simp

/-- **The dual block kernel at a class.** -/
theorem dualKernel_mk (nabs : K → ℝ) (h : t < r) (χ : AddChar K ℂ)
    {W : Langlands.GeneralLinear (r + 1) K → ℂ} {W' : Langlands.GeneralLinear (t + 1) K → ℂ}
    (hW : IsLeftEquivariant r χ W) (hW' : IsLeftInverseEquivariant t χ W')
    (s : ℂ) (g : Langlands.GeneralLinear (t + 1) K)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) K) :
    ArchimedeanLocal.blockKernel nabs h
        (ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h)
          (ArchimedeanLocal.dualFunction (r + 1) W))
        (ArchimedeanLocal.dualFunction (t + 1) W') s (Quotient.mk'' g) x =
      ArchimedeanLocal.dualFunction (r + 1) W
          (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h) *
        ArchimedeanLocal.dualFunction (t + 1) W' g *
        ArchimedeanLocal.detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2) := by
  refine apply_out_mk (fun g => ArchimedeanLocal.dualFunction (r + 1) W
      (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h) *
    ArchimedeanLocal.dualFunction (t + 1) W' g *
    ArchimedeanLocal.detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2)) ?_ g
  intro u g
  have hp := dualFunction_mul_left hW (padUnipotent (Nat.le_of_lt (Nat.succ_lt_succ h)) u)
    (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h)
  rw [sum_padUnipotent] at hp
  have hne := addChar_ne_zero χ (-(∑ i : Fin t, u.val i.castSucc i.succ))
  rw [rectangularPoint_mul_left, mul_assoc (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) u.val)]
  change ArchimedeanLocal.dualFunction (r + 1) W
      ((padUnipotent (Nat.le_of_lt (Nat.succ_lt_succ h)) u).val *
        (ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h)) *
    ArchimedeanLocal.dualFunction (t + 1) W' (u.val * g) *
      ArchimedeanLocal.detPower nabs (u.val * g) _ = _
  rw [hp, dualFunction_mul_left_inv hW' u g, detPower_unipotent_mul]
  field_simp

end Langlands.Global.RankinSelbergGlobal.UnequalLocalKernels
