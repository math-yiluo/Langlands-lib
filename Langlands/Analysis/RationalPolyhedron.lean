import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Extreme points and linear objectives of rational polyhedra -/

noncomputable section

open Matrix Set Filter
open scoped Matrix Topology

namespace Langlands

variable {m n : Type*} [Fintype n]

/-- The real polyhedron `A x ≤ b`, with rational coefficients and componentwise inequalities. -/
def rationalPolyhedron (A : Matrix m n ℚ) (b : m → ℚ) : Set (n → ℝ) :=
  {x | A.map (Rat.castHom ℝ) *ᵥ x ≤ fun i => (b i : ℝ)}

/-- A rational polyhedron is closed in real coordinate space. -/
theorem isClosed_rationalPolyhedron (A : Matrix m n ℚ) (b : m → ℚ) :
    IsClosed (rationalPolyhedron A b) := by
  have h (i : m) : Continuous (fun x : n → ℝ => ∑ j, (A i j : ℝ) * x j) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have he : rationalPolyhedron A b = ⋂ i, {x | ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)} := by
    ext x
    simp [rationalPolyhedron, Matrix.mulVec, dotProduct, Pi.le_def]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (h i) continuous_const

/-- A rational polyhedron is convex in real coordinate space. -/
theorem convex_rationalPolyhedron (A : Matrix m n ℚ) (b : m → ℚ) :
    Convex ℝ (rationalPolyhedron A b) := by
  intro x hx y hy s t hs ht hst i
  let M := A.map (Rat.castHom ℝ)
  change (M *ᵥ (s • x + t • y)) i ≤ (b i : ℝ)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hxi : (M *ᵥ x) i ≤ (b i : ℝ) := hx i
  have hyi : (M *ᵥ y) i ≤ (b i : ℝ) := hy i
  calc
    _ ≤ s * (b i : ℝ) + t * (b i : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hxi hs) (mul_le_mul_of_nonneg_left hyi ht)
    _ = _ := by rw [← add_mul, hst, one_mul]

private theorem injective_mulVec_tightRows [Finite m]
    (M : Matrix m n ℝ) (b : m → ℝ) {x : n → ℝ}
    (hx : x ∈ ({y | M *ᵥ y ≤ b} : Set (n → ℝ)).extremePoints ℝ) :
    Function.Injective (M.submatrix (fun i : {i // (M *ᵥ x) i = b i} => i.val) id).mulVec := by
  intro u v huv
  let K := M.submatrix (fun i : {i // (M *ᵥ x) i = b i} => i.val) id
  let d := u - v
  have hKd : K *ᵥ d = 0 := by rw [show d = u - v from rfl, mulVec_sub, huv, sub_self]
  have hrow (i : m) (hi : (M *ᵥ x) i = b i) : (M *ᵥ d) i = 0 :=
    congrFun hKd ⟨i, hi⟩
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ),
      (∀ i, ((M *ᵥ x) i + r * (M *ᵥ d) i ≤ b i) ∧
        ((M *ᵥ x) i - r * (M *ᵥ d) i ≤ b i)) := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : (M *ᵥ x) i = b i
    · simp [hi, hrow i hi]
    · have hlt : (M *ᵥ x) i < b i := lt_of_le_of_ne (hx.1 i) hi
      have hp : ContinuousAt (fun r : ℝ => (M *ᵥ x) i + r * (M *ᵥ d) i) 0 := by fun_prop
      have hm : ContinuousAt (fun r : ℝ => (M *ᵥ x) i - r * (M *ᵥ d) i) 0 := by fun_prop
      have hep := hp.eventually_lt (continuousAt_const (y := b i)) (by simpa using hlt)
      have hem := hm.eventually_lt (continuousAt_const (y := b i)) (by simpa using hlt)
      filter_upwards [hep, hem] with r hpr hmr
      exact ⟨hpr.le, hmr.le⟩
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.1 hsmall
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  have hdist : dist r 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact half_lt_self hδ
  have hplus : x + r • d ∈ ({y | M *ᵥ y ≤ b} : Set (n → ℝ)) := by
    intro i
    simpa only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      (hnear hdist i).1
  have hminus : x - r • d ∈ ({y | M *ᵥ y ≤ b} : Set (n → ℝ)) := by
    intro i
    simpa only [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      (hnear hdist i).2
  have h := hx.2 hplus hminus (mem_openSegment_add_sub x (r • d))
  have hd : d = 0 := by
    have hzero : r • d = 0 := add_left_cancel (h.trans (add_zero _).symm)
    exact (smul_eq_zero.mp hzero).resolve_left hr.ne'
  exact sub_eq_zero.mp hd

private theorem exists_ratCast_eq_of_mulVec_eq [Fintype m] (A : Matrix m n ℚ) (b : m → ℚ)
    {x : n → ℝ} (hx : A.map (Rat.castHom ℝ) *ᵥ x = fun i => (b i : ℝ))
    (hinj : Function.Injective (A.map (Rat.castHom ℝ)).mulVec) :
    ∃ q : n → ℚ, (fun i => (q i : ℝ)) = x := by
  classical
  let f := Rat.castHom ℝ
  let M := A.map f
  let G := Aᵀ * A
  have hG : G.map f = Mᵀ * M := by simp [G, M, Matrix.transpose_map]
  have hinjG : Function.Injective (G.map f).mulVec := by
    change Function.Injective (G.map f).mulVecLin
    rw [← LinearMap.ker_eq_bot, hG, ker_mulVecLin_transpose_mul_self, LinearMap.ker_eq_bot]
    exact hinj
  have hdetR : (G.map f).det ≠ 0 := isUnit_iff_ne_zero.mp
    ((G.map f).isUnit_iff_isUnit_det.mp (mulVec_injective_iff_isUnit.mp hinjG))
  have hdetQ : G.det ≠ 0 := by
    intro h0
    apply hdetR
    change (f.mapMatrix G).det = 0
    rw [← f.map_det, h0, map_zero]
  obtain ⟨q, hq⟩ := (mulVec_surjective_iff_isUnit.mpr
    (G.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdetQ))) (Aᵀ *ᵥ b)
  refine ⟨q, hinjG ?_⟩
  calc
    G.map f *ᵥ (fun i => (q i : ℝ)) = Mᵀ *ᵥ (fun i => (b i : ℝ)) := by
      ext i
      change (G.map f *ᵥ (f ∘ q)) i = (Mᵀ *ᵥ (f ∘ b)) i
      rw [← f.map_mulVec G q i, hq, f.map_mulVec Aᵀ b i, transpose_map]
    _ = G.map f *ᵥ x := by rw [hG, ← mulVec_mulVec, hx]

/-- Every extreme point of a rational polyhedron has rational coordinates. -/
theorem exists_ratCast_eq_of_mem_extremePoints_rationalPolyhedron [Fintype m]
    {A : Matrix m n ℚ} {b : m → ℚ} {x : n → ℝ}
    (hx : x ∈ (rationalPolyhedron A b).extremePoints ℝ) :
    ∃ q : n → ℚ, (fun i => (q i : ℝ)) = x := by
  classical
  let M := A.map (Rat.castHom ℝ)
  let I := {i : m // (M *ᵥ x) i = (b i : ℝ)}
  let C : Matrix I n ℚ := A.submatrix Subtype.val id
  let c : I → ℚ := fun i => b i.val
  have hCx : C.map (Rat.castHom ℝ) *ᵥ x = fun i => (c i : ℝ) := funext fun i => i.property
  have hinj : Function.Injective (C.map (Rat.castHom ℝ)).mulVec :=
    injective_mulVec_tightRows M (fun i => (b i : ℝ)) hx
  exact exists_ratCast_eq_of_mulVec_eq C c hCx hinj

/-- A continuous linear functional on a nonempty compact rational polyhedron attains its
maximum at a point with rational coordinates. The functional need not have rational coefficients. -/
theorem exists_ratCast_isMaxOn_rationalPolyhedron [Fintype m]
    {A : Matrix m n ℚ} {b : m → ℚ} (hc : IsCompact (rationalPolyhedron A b))
    (hne : (rationalPolyhedron A b).Nonempty) (f : (n → ℝ) →L[ℝ] ℝ) :
    ∃ q : n → ℚ, (fun i => (q i : ℝ)) ∈ rationalPolyhedron A b ∧
      ∀ y ∈ rationalPolyhedron A b, f y ≤ f (fun i => (q i : ℝ)) := by
  let C := rationalPolyhedron A b
  let D := f.toExposed C
  have hD : IsExposed ℝ C D := ContinuousLinearMap.toExposed.isExposed
  have hneD : D.Nonempty := by
    obtain ⟨x, hx, hm⟩ := hc.exists_isMaxOn hne f.continuous.continuousOn
    exact ⟨x, hx, fun y hy => hm hy⟩
  obtain ⟨x, hx⟩ := (hD.isCompact hc).extremePoints_nonempty hneD
  obtain ⟨q, rfl⟩ := exists_ratCast_eq_of_mem_extremePoints_rationalPolyhedron
    (hD.isExtreme.extremePoints_subset_extremePoints hx)
  exact ⟨q, hx.1.1, hx.1.2⟩

end Langlands
