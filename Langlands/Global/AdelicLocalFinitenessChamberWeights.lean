import Langlands.Global.AdelicIwasawaChamberBounds
import Mathlib.Analysis.Normed.Group.Constructions

/-! # Signed central weights in root and central log coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open AlgebraicGeometry CategoryTheory Module Set TensorProduct
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

/-- A finite integer basis of rational characters represents every real linear
form on their real dual by a real character parameter. -/
theorem realParameterPairing_surjective (F : Type u) [Field F] [NumberField F]
    (P : GroupScheme (Spec (CommRingCat.of F)))
    [Module.Free ℤ (GroupScheme.rationalCharacters P)]
    [Module.Finite ℤ (GroupScheme.rationalCharacters P)] :
    Function.Surjective (realParameterPairing F P) := by
  let J := Module.Free.ChooseBasisIndex ℤ (GroupScheme.rationalCharacters P)
  let : Fintype J := Fintype.ofFinite J
  let b := Module.Free.chooseBasis ℤ (GroupScheme.rationalCharacters P)
  let d (i : J) : RealCharacterDual F P :=
    { toFun := fun χ => (b.repr χ i : ℝ)
      map_zero' := by rw [map_zero, Finsupp.zero_apply, Int.cast_zero]
      map_add' := by intro x y; rw [map_add, Finsupp.add_apply, Int.cast_add] }
  have hd (H : RealCharacterDual F P) : (∑ i, H (b i) • d i) = H := by
    apply AddMonoidHom.ext
    intro χ
    let h : GroupScheme.rationalCharacters P →+ ℝ := H
    change (∑ i, (h (b i) • d i : GroupScheme.rationalCharacters P →+ ℝ)) χ = h χ
    rw [AddMonoidHom.finsetSum_apply]
    have he := map_sum h (fun i => b.repr χ i • b i) Finset.univ
    rw [b.sum_repr] at he
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans he.symm
    change h (b i) * (b.repr χ i : ℝ) = h (b.repr χ i • b i)
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  intro f
  refine ⟨∑ i, f (d i) ⊗ₜ[ℤ] b i, ?_⟩
  ext H
  calc
    _ = ∑ i, f (d i) * H (b i) := by
      simp only [map_sum, LinearMap.sum_apply, realParameterPairing_tmul]
    _ = f (∑ i, H (b i) • d i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = f H := congrArg f (hd H)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicSiegelFactors

open AdelicGroupPoints

variable {Δ : Type v} {J : Type w} [Fintype Δ] [Fintype J]

/-- The log weight has linear root terms and absolute central terms. -/
def localFinitenessLogWeight (A : Δ → ℝ) (B : J → ℝ)
    (x : (Δ → ℝ) × (J → ℝ)) : ℝ :=
  (∑ α, A α * x.1 α) + ∑ j, B j * |x.2 j|

theorem continuous_localFinitenessLogWeight (A : Δ → ℝ) (B : J → ℝ) :
    Continuous (localFinitenessLogWeight A B) := by
  have h₁ α : Continuous (fun x : (Δ → ℝ) × (J → ℝ) => A α * x.1 α) :=
    continuous_const.mul ((continuous_apply α).comp continuous_fst)
  have h₂ j : Continuous (fun x : (Δ → ℝ) × (J → ℝ) => B j * |x.2 j|) :=
    continuous_const.mul ((continuous_apply j).comp continuous_snd).abs
  exact (continuous_finsetSum Finset.univ fun α _ => h₁ α).add
    (continuous_finsetSum Finset.univ fun j _ => h₂ j)

/-- Arbitrarily large positive rates dominate the full norm on any chamber with
lower bounds on each root coordinate. -/
theorem localFinitenessLogWeight_norm_le (A τ : Δ → ℝ) (B : J → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hA : ∀ α, c ≤ A α) (hB : ∀ j, c ≤ B j)
    (x : (Δ → ℝ) × (J → ℝ)) (hx : ∀ α, τ α ≤ x.1 α) :
    c * ‖x‖ ≤ localFinitenessLogWeight A B x + ∑ α, 2 * A α * |τ α| := by
  have hsum₁ : 0 ≤ ∑ α, |x.1 α| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum₂ : 0 ≤ ∑ j, |x.2 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hn₁ : ‖x.1‖ ≤ ∑ α, |x.1 α| := by
    rw [pi_norm_le_iff_of_nonneg hsum₁]
    exact fun α => Finset.single_le_sum (fun i _ => abs_nonneg (x.1 i)) (Finset.mem_univ α)
  have hn₂ : ‖x.2‖ ≤ ∑ j, |x.2 j| := by
    rw [pi_norm_le_iff_of_nonneg hsum₂]
    exact fun j => Finset.single_le_sum (fun i _ => abs_nonneg (x.2 i)) (Finset.mem_univ j)
  have hn : ‖x‖ ≤ (∑ α, |x.1 α|) + ∑ j, |x.2 j| :=
    max_le (hn₁.trans (le_add_of_nonneg_right hsum₂)) (hn₂.trans (le_add_of_nonneg_left hsum₁))
  have hr (α : Δ) : c * |x.1 α| ≤ A α * x.1 α + 2 * A α * |τ α| := by
    have h := mul_le_mul_of_nonneg_right (hA α) (abs_nonneg (x.1 α))
    have hA₀ := hc.trans (hA α)
    by_cases hα : 0 ≤ x.1 α
    · rw [abs_of_nonneg hα] at h ⊢
      exact h.trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hA₀) (abs_nonneg _)))
    · have hτ : -x.1 α ≤ |τ α| := (neg_le_neg (hx α)).trans (neg_le_abs _)
      rw [abs_of_neg (lt_of_not_ge hα)] at h ⊢
      nlinarith [mul_le_mul_of_nonneg_left hτ hA₀]
  have h₁ := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) => hr α
  have h₂ : (∑ j, c * |x.2 j|) ≤ ∑ j, B j * |x.2 j| :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hB j) (abs_nonneg _)
  calc
    c * ‖x‖ ≤ c * ((∑ α, |x.1 α|) + ∑ j, |x.2 j|) := mul_le_mul_of_nonneg_left hn hc
    _ = (∑ α, c * |x.1 α|) + ∑ j, c * |x.2 j| := by rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    _ ≤ localFinitenessLogWeight A B x + ∑ α, 2 * A α * |τ α| := by
      rw [Finset.sum_add_distrib] at h₁
      unfold localFinitenessLogWeight
      linarith

/-- The log weight increases by the root rate under a positive unit root shift. -/
theorem localFinitenessLogWeight_add_root (A : Δ → ℝ) (B : J → ℝ)
    (x : (Δ → ℝ) × (J → ℝ)) (α : Δ) :
    localFinitenessLogWeight A B (x + (Pi.single α 1, 0)) =
      localFinitenessLogWeight A B x + A α := by
  simp only [localFinitenessLogWeight, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero,
    mul_add, Finset.sum_add_distrib]
  have h : (∑ i, A i * (Pi.single α 1 : Δ → ℝ) i) = A α := by
    simp [Pi.single_apply, mul_ite]
  rw [h]
  abel

/-- An outward unit shift in either central direction increases the log weight
by the same positive-side rate. This also covers the wall of the orthant. -/
theorem localFinitenessLogWeight_add_center (A : Δ → ℝ) (B : J → ℝ)
    (x : (Δ → ℝ) × (J → ℝ)) (j : J) (s : Bool)
    (hx : 0 ≤ if s then x.2 j else -x.2 j) :
    localFinitenessLogWeight A B (x + (0, Pi.single j (if s then 1 else -1))) =
      localFinitenessLogWeight A B x + B j := by
  have hj : |x.2 j + (if s then 1 else -1)| = |x.2 j| + 1 := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith : x.2 j ≤ 0)]
      ring
    · simp only [↓reduceIte] at hx ⊢
      rw [abs_of_nonneg (by linarith), abs_of_nonneg hx]
  have he (i : J) : |x.2 i + (Pi.single j (if s then 1 else -1) : J → ℝ) i| = |x.2 i| + (Pi.single j 1 : J → ℝ) i := by
    by_cases hi : i = j
    · subst i
      simpa only [Pi.single_eq_same] using hj
    · simp [Pi.single_eq_of_ne hi]
  simp only [localFinitenessLogWeight, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero, he,
    mul_add, Finset.sum_add_distrib, add_assoc]
  have h : (∑ i, B i * (Pi.single j 1 : J → ℝ) i) = B j := by
    simp [Pi.single_apply, mul_ite]
  rw [h]

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  [Module.Free ℤ (GroupScheme.rationalCharacters P)]
  [Module.Finite ℤ (GroupScheme.rationalCharacters P)]

/-- The log weight in given linear parabolic coordinates has a polynomial
exponential bound and bounded log displacement under compact right shifts. -/
def AdelicLocalFinitenessChamberWeightStatement {n : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin n))
    (e : RealCharacterDual F P ≃L[ℝ] ((Δ → ℝ) × (J → ℝ))) (A : Δ → ℝ) (B : J → ℝ) : Prop :=
  (∀ j, 0 ≤ B j) →
  let ell := localFinitenessLogWeight A B ∘ e
  Continuous ell ∧
    (0 < n → GroupScheme.IsClosedSubgroup rho →
      ∃ C t : ℝ, 0 < C ∧ 0 ≤ t ∧ ∀ x : AdelicGroupPoints F G,
        Real.exp (ell (hK.height x)) ≤ C * RepresentationGrowth.adelicHeight F G rho x ^ t) ∧
    (∀ (S : Set (AdelicGroupPoints F G)), IsCompact S →
      ∃ b : ℝ, 0 ≤ b ∧ ∀ (x : AdelicGroupPoints F G), ∀ a ∈ S,
        |ell (hK.height (x * a)) - ell (hK.height x)| ≤ b)

/-- The finite maximum of the corresponding signed character weights has the
required bounds on the whole adelic group. -/
theorem adelicLocalFinitenessChamberWeight {n : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin n))
    (e : RealCharacterDual F P ≃L[ℝ] ((Δ → ℝ) × (J → ℝ))) (A : Δ → ℝ) (B : J → ℝ) :
    AdelicLocalFinitenessChamberWeightStatement hK rho e A B := by
  intro hB
  let f₁ : RealCharacterDual F P →ₗ[ℝ] ℝ := ∑ α,
    A α • ((LinearMap.proj α).comp ((LinearMap.fst ℝ (Δ → ℝ) (J → ℝ)).comp e.toLinearEquiv.toLinearMap))
  let f₂ (j : J) : RealCharacterDual F P →ₗ[ℝ] ℝ :=
    B j • ((LinearMap.proj j).comp ((LinearMap.snd ℝ (Δ → ℝ) (J → ℝ)).comp e.toLinearEquiv.toLinearMap))
  obtain ⟨base, hbase⟩ := realParameterPairing_surjective F P f₁
  choose cent hcent using fun j => realParameterPairing_surjective F P (f₂ j)
  have he : localFinitenessLogWeight A B ∘ e = finiteMaximumLogWeight F P
      (Finset.univ : Finset (J → Bool)) Finset.univ_nonempty
        (fun s => base + ∑ j, if s j then cent j else -cent j) := by
    funext H
    rw [finiteMaximumLogWeight_signs, hbase]
    change (∑ α, A α * (e H).1 α) + ∑ j, B j * |(e H).2 j| =
      f₁ H + ∑ j, |realParameterPairing F P (cent j) H|
    rw [show f₁ H = ∑ α, A α * (e H).1 α from LinearMap.sum_apply _ _ _]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hcent j]
    change B j * |(e H).2 j| = |B j * (e H).2 j|
    rw [abs_mul, abs_of_nonneg (hB j)]
  dsimp only
  rw [he]
  exact hK.iwasawaFiniteMaximumWeight rho Finset.univ Finset.univ_nonempty _

end Langlands.Global.AdelicSiegelFactors
