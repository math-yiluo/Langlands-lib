import Langlands.Representation.Whittaker.Spherical
import Langlands.Global.RankinSelberg.UnfoldingDualGL
import Langlands.Group.GL.LowerTriangularBlockCoordinates

/-! # Support of spherical Whittaker functions on rectangular lower blocks

Over a valued field with ring of integers `𝒪`, a function `f` on `GL_(r+1)` which is
`θ`-equivariant on the left under the upper unitriangular group, for a character `θ` given
by an additive character `χ` of conductor exactly `𝒪` on the first superdiagonal, and
right invariant under `GL_(r+1)(𝒪)`, satisfies
`f([[g,0,0],[x,I,0],[0,0,1]]) = [x ∈ M(𝒪)] · f(diag(g, I))`.
See the paired Markdown.
-/

noncomputable section
open Matrix
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularSupport

open Langlands.Global.RankinSelbergGlobal Langlands.Global.RankinSelbergGlobal.Unfolding

section Ring

variable {R : Type*} [CommRing R]

/-- The matrix `[[g,0,0],[x,I_(r-t-1),0],[0,0,1]]` in `GL_(r+1)(R)`, with `g ∈ GL_(t+1)(R)`:
the coordinates of the Library's adelic `rectangularPoint`, over any commutative ring. -/
def rectGL {r t : ℕ} (h : t < r) (g : Matrix.GeneralLinearGroup (Fin (t + 1)) R)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) R) :
    Matrix.GeneralLinearGroup (Fin (r + 1)) R :=
  GeneralLinear.reindex
    (finCongr (congrArg (fun a : ℕ => a + 1) (Nat.add_sub_of_le (Nat.succ_le_of_lt h))))
    (GeneralLinear.lowerBlockLocalization 1 g x 1)

/-- The entries of `rectGL`. -/
theorem rectGL_apply {r t : ℕ} (h : t < r) (g : Matrix.GeneralLinearGroup (Fin (t + 1)) R)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) R) (i j : Fin (r + 1)) :
    rectGL h g x i j =
      if hj : (j : ℕ) < t + 1 then
        (if hi : (i : ℕ) < t + 1 then g ⟨i, hi⟩ ⟨j, hj⟩
        else if hi' : (i : ℕ) < r then x ⟨i - (t + 1), by omega⟩ ⟨j, hj⟩ else 0)
      else if i = j then 1 else 0 := by
  set e := finCongr (congrArg (fun a : ℕ => a + 1) (Nat.add_sub_of_le (Nat.succ_le_of_lt h)))
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  simp only [rectGL, GeneralLinear.reindex, MulEquiv.coe_mk, Units.coe_mapEquiv]
  change Matrix.reindex e e _ (e i') (e j') = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [e, finCongr_apply, Fin.val_cast, GeneralLinear.lowerBlockLocalization]
  refine Fin.addCases (fun i₁ => ?_) (fun i₃ => ?_) i' <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₃ => ?_) j'
  · refine Fin.addCases (fun i₀ => ?_) (fun i₂ => ?_) i₁ <;>
      refine Fin.addCases (fun j₀ => ?_) (fun j₂ => ?_) j₁ <;>
      (simp [GeneralLinear.rankInclusion, Matrix.one_apply, Fin.ext_iff]; try omega) <;>
      split_ifs <;> first | rfl | omega
  · refine Fin.addCases (fun i₀ => ?_) (fun i₂ => ?_) i₁ <;>
      (simp [GeneralLinear.rankInclusion, Fin.ext_iff]; try omega) <;>
      split_ifs <;> first | rfl | omega
  · refine Fin.addCases (fun j₀ => ?_) (fun j₂ => ?_) j₁ <;>
      (simp [GeneralLinear.rankInclusion, Fin.ext_iff]; try omega) <;>
      split_ifs <;> first | rfl | omega
  · simp [GeneralLinear.rankInclusion, Matrix.one_apply, Fin.ext_iff]
    intro; omega

/-- Product formula: `[[P,0,0],[z,I,0],[0,0,1]] * [[Q,0,0],[w,I,0],[0,0,1]] =
[[PQ,0,0],[zQ+w,I,0],[0,0,1]]`. -/
theorem rectGL_mul {r t : ℕ} (h : t < r) (P Q : Matrix.GeneralLinearGroup (Fin (t + 1)) R)
    (z w : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) R) :
    rectGL h P z * rectGL h Q w =
      rectGL h (P * Q) (z * (Q : Matrix (Fin (t + 1)) (Fin (t + 1)) R) + w) := by
  simp only [rectGL, GeneralLinear.lowerBlockLocalization]
  rw [← map_mul, ← map_mul, GeneralLinear.lowerBlockPair_mul_lowerBlockPair]
  simp

theorem rectGL_one_zero {r t : ℕ} (h : t < r) : rectGL (R := R) h 1 0 = 1 := by
  ext i j
  rw [rectGL_apply]
  simp only [Units.val_one, Matrix.one_apply, Matrix.zero_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- `[[Q,0,0],[0,I,0],[0,0,1]]` is the padding of `Q`. -/
theorem rectGL_zero {r t : ℕ} (h : t < r) (Q : Matrix.GeneralLinearGroup (Fin (t + 1)) R) :
    rectGL h Q 0 = padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) Q := by
  ext i j
  rw [rectGL_apply]
  set e := finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h)))
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  simp only [padGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    GeneralLinear.reindex, MulEquiv.coe_mk, Units.coe_mapEquiv, Units.coe_map]
  change _ = Matrix.reindex e e _ (e i') (e j')
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [e, finCongr_apply, Fin.val_cast, padMatrix, MonoidHom.coe_mk, OneHom.coe_mk]
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i' <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j' <;>
    (simp [Matrix.one_apply, Fin.ext_iff]; try omega) <;>
    split_ifs <;> first | rfl | omega

end Ring

section Valued

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀}

open Langlands.GeneralLinear.Iwasawa Langlands.Conductor

/-- `[[k,0,0],[z,I,0],[0,0,1]]` is integral when `k` and `z` are. -/
theorem rectGL_mem_integralSubgroup {r t : ℕ} (h : t < r)
    {k : Matrix.GeneralLinearGroup (Fin (t + 1)) F} (hk : k ∈ integralSubgroup v.integer t)
    {z : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F} (hz : ∀ i j, z i j ∈ v.integer) :
    rectGL h k z ∈ integralSubgroup v.integer r := by
  have hent : ∀ (k : Matrix.GeneralLinearGroup (Fin (t + 1)) F)
      (z : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F), (∀ i j, k i j ∈ v.integer) →
      (∀ i j, z i j ∈ v.integer) → ∀ i j, rectGL h k z i j ∈ v.integer := by
    intro k z hk hz i j
    rw [rectGL_apply]
    split_ifs
    all_goals first | exact hk _ _ | exact hz _ _ | exact zero_mem _ | exact one_mem _
  have hinv : (rectGL h k z)⁻¹ = rectGL h k⁻¹ (-(z * ((k⁻¹ : Matrix.GeneralLinearGroup
      (Fin (t + 1)) F) : Matrix (Fin (t + 1)) (Fin (t + 1)) F))) := by
    rw [inv_eq_iff_mul_eq_one, rectGL_mul, mul_inv_cancel, add_neg_cancel, rectGL_one_zero]
  have hk' := (mem_integralSubgroup v.integer t k).1 hk
  refine (mem_integralSubgroup v.integer r _).2 ⟨hent k z hk'.1 hz, ?_⟩
  rw [hinv]
  refine hent _ _ hk'.2 fun i j => ?_
  simp only [Matrix.neg_apply, Matrix.mul_apply]
  exact neg_mem (Subring.sum_mem _ fun l _ => mul_mem (hz _ _) (hk'.2 _ _))

/-- **The character trick.** Let `f` be `θ`-equivariant on the left under the upper
unitriangular group, where `θ` is `χ` of the first-superdiagonal sum, and right invariant
under `GL_(n+1)(𝒪)`. If row `p+1` of `g` is the standard basis row `e_(p+1)`, the column `c₀`
of `g` vanishes from row `p+1` down, and `g_(p,c₀) ∉ 𝒪`, then `f g = 0`, provided `χ` is
nontrivial on `𝒪 · z` for every `z ∉ 𝒪`. -/
theorem eq_zero_of_basisRow {n : ℕ} {θ : upperUnipotent (n + 1) F →* ℂˣ} {χ : F → ℂ}
    (hθ : ∀ u : upperUnipotent (n + 1) F,
      (θ u : ℂ) = χ (∑ i : Fin n,
        ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F) i.castSucc i.succ))
    (hχ : ∀ z ∉ v.integer, ∃ c ∈ v.integer, χ (c * z) ≠ 1)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g,
      f ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g) = θ u * f g)
    (hK : ∀ g, ∀ k ∈ integralSubgroup v.integer n, f (g * k) = f g)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (p : Fin n) (c₀ : Fin (n + 1))
    (hrow : ∀ j, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) p.succ j =
      if j = p.succ then 1 else 0)
    (hcol : ∀ j, p.succ ≤ j → (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) j c₀ = 0)
    (hbad : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) p.castSucc c₀ ∉ v.integer) :
    f g = 0 := by
  obtain ⟨c, hc, hχc⟩ := hχ _ hbad
  set G : Matrix (Fin (n + 1)) (Fin (n + 1)) F := (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    with hGdef
  have hGp : G p.succ c₀ = 0 := hcol p.succ le_rfl
  have hc₀ : c₀ ≠ p.succ := by
    intro he
    have h1 := hrow c₀
    rw [if_pos he, hGp] at h1
    exact zero_ne_one h1
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.of fun i j => if j = p.succ then c * G i c₀ else 0
  have hEE : E * E = 0 := by
    ext i j
    simp [E, Matrix.mul_apply, hGp]
  have h1 : (1 + E) * (1 - E) = 1 := by
    have : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  have h2 : (1 - E) * (1 + E) = 1 := by
    have : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  let N : Matrix.GeneralLinearGroup (Fin (n + 1)) F := ⟨1 + E, 1 - E, h1, h2⟩
  have hN : N ∈ upperUnipotent (n + 1) F := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · change (1 + E) i j = 0
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from ne_of_gt hji)]
      simp only [E, Matrix.of_apply]
      split_ifs with hj
      · subst hj
        rw [hcol i (le_of_lt hji), mul_zero, zero_add]
      · rw [zero_add]
    · change (1 + E) i i = 1
      simp only [Matrix.add_apply, E, Matrix.of_apply, Matrix.one_apply_eq]
      split_ifs with hi
      · subst hi
        rw [hGp, mul_zero, add_zero]
      · rw [add_zero]
  let u : upperUnipotent (n + 1) F := ⟨N, hN⟩
  have htr1 : Matrix.transvection c₀ p.succ c * Matrix.transvection c₀ p.succ (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same c₀ p.succ hc₀, add_neg_cancel,
      Matrix.transvection_zero]
  have htr2 : Matrix.transvection c₀ p.succ (-c) * Matrix.transvection c₀ p.succ c = 1 := by
    rw [Matrix.transvection_mul_transvection_same c₀ p.succ hc₀, neg_add_cancel,
      Matrix.transvection_zero]
  let k := ofInverse _ _ htr1 htr2
  have hk : k ∈ integralSubgroup v.integer n :=
    ofInverse_mem v _ _ htr1 htr2 (transvection_mem v _ _ hc) (transvection_mem v _ _ (neg_mem hc))
  have hgk : g * k = (u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g := by
    apply Units.ext
    ext i j
    change (G * Matrix.transvection c₀ p.succ c) i j = ((1 + E) * G) i j
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    have hEG : (E * G) i j = if j = p.succ then c * G i c₀ else 0 := by
      simp only [E, Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, hrow j, mul_ite, mul_one, mul_zero]
    rw [hEG]
    by_cases hj : j = p.succ
    · subst hj
      rw [Matrix.mul_transvection_apply_same, if_pos rfl]
    · rw [Matrix.mul_transvection_apply_of_ne c₀ p.succ i j hj c G, if_neg hj, add_zero]
  have hsum : (∑ i : Fin n, ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) i.castSucc i.succ) = c * G p.castSucc c₀ := by
    change (∑ i : Fin n, (1 + E) i.castSucc i.succ) = _
    rw [Finset.sum_eq_single p]
    · simp [E, Matrix.one_apply_ne (ne_of_lt p.castSucc_lt_succ)]
    · intro b _ hb
      simp only [Matrix.add_apply, E, Matrix.of_apply,
        Matrix.one_apply_ne (ne_of_lt b.castSucc_lt_succ), zero_add]
      rw [if_neg (fun h => hb (Fin.succ_inj.mp h))]
    · intro h; exact absurd (Finset.mem_univ p) h
  have heq : f g = χ (c * G p.castSucc c₀) * f g := by
    rw [← hsum, ← hθ u, ← hf u g, ← hgk, hK g k hk]
  have : (1 - χ (c * G p.castSucc c₀)) * f g = 0 := by
    rw [sub_mul, one_mul, ← heq, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hχc
  · exact h0

open Classical in
/-- **Support on rectangular blocks.** Under the hypotheses of `eq_zero_of_basisRow`,
`f([[Q,0,0],[z,I,0],[0,0,1]])` vanishes unless `z` is integral, and then equals
`f([[Q,0,0],[0,I,0],[0,0,1]])`. -/
theorem apply_rectGL {r t : ℕ} (h : t < r) {θ : upperUnipotent (r + 1) F →* ℂˣ} {χ : F → ℂ}
    (hθ : ∀ u : upperUnipotent (r + 1) F,
      (θ u : ℂ) = χ (∑ i : Fin r,
        ((u : Matrix.GeneralLinearGroup (Fin (r + 1)) F) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) F) i.castSucc i.succ))
    (hχ : ∀ z ∉ v.integer, ∃ c ∈ v.integer, χ (c * z) ≠ 1)
    {f : Matrix.GeneralLinearGroup (Fin (r + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (r + 1) F) g,
      f ((u : Matrix.GeneralLinearGroup (Fin (r + 1)) F) * g) = θ u * f g)
    (hK : ∀ g, ∀ k ∈ integralSubgroup v.integer r, f (g * k) = f g)
    (Q : Matrix.GeneralLinearGroup (Fin (t + 1)) F)
    (z : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F) :
    f (rectGL h Q z) = if ∀ i j, z i j ∈ v.integer then f (rectGL h Q 0) else 0 := by
  have hsplit : ∀ z₁ z₂ : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F,
      (∀ i j, z₂ i j ∈ v.integer) → f (rectGL h Q (z₁ + z₂)) = f (rectGL h Q z₁) := by
    intro z₁ z₂ hz₂
    have : rectGL h Q (z₁ + z₂) = rectGL h Q z₁ * rectGL h 1 z₂ := by
      rw [rectGL_mul, mul_one, Units.val_one, Matrix.mul_one]
    rw [this, hK _ _ (rectGL_mem_integralSubgroup h (one_mem _) hz₂)]
  split_ifs with hz
  · simpa using hsplit 0 z hz
  · push_neg at hz
    obtain ⟨i₁, j₁, h₁⟩ := hz
    let S := Finset.univ.filter (fun i => ∃ j, z i j ∉ v.integer)
    have hS : S.Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, j₁, h₁⟩⟩
    set i₀ := S.max' hS with hi₀def
    have hi₀ : i₀ ∈ S := S.max'_mem hS
    obtain ⟨j₀, hj₀⟩ := (Finset.mem_filter.1 hi₀).2
    have hgt : ∀ i, i₀ < i → ∀ j, z i j ∈ v.integer := by
      intro i hi j
      by_contra hc
      exact absurd (S.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hc⟩))
        (not_le.2 hi)
    let z₁ : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F :=
      Matrix.of fun i j => if i ≤ i₀ then z i j else 0
    let z₂ : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F :=
      Matrix.of fun i j => if i ≤ i₀ then 0 else z i j
    have hz12 : z = z₁ + z₂ := by
      ext i j
      simp only [z₁, z₂, Matrix.add_apply, Matrix.of_apply]
      split_ifs <;> simp
    have hz₂ : ∀ i j, z₂ i j ∈ v.integer := by
      intro i j
      simp only [z₂, Matrix.of_apply]
      split_ifs with hi
      · exact zero_mem _
      · exact hgt i (not_le.1 hi) j
    rw [hz12, hsplit z₁ z₂ hz₂]
    have hi₀r : t + 1 + (i₀ : ℕ) < r := by have := i₀.isLt; omega
    refine eq_zero_of_basisRow hθ hχ hf hK _ ⟨t + 1 + i₀, hi₀r⟩ ⟨j₀, by omega⟩ ?_ ?_ ?_
    · intro j
      rw [rectGL_apply]
      simp only [Fin.succ_mk, Fin.ext_iff, z₁, Matrix.of_apply, Fin.le_iff_val_le_val]
      split_ifs <;> first | rfl | omega
    · intro j hj
      rw [rectGL_apply]
      simp only [Fin.succ_mk, Fin.le_iff_val_le_val, Fin.ext_iff, z₁, Matrix.of_apply] at hj ⊢
      split_ifs <;> first | rfl | omega
    · rw [rectGL_apply]
      simp only [Fin.castSucc_mk, z₁, Matrix.of_apply]
      rw [dif_pos (show j₀.val < t + 1 from j₀.isLt), dif_neg (by omega), dif_pos hi₀r]
      have he : (⟨t + 1 + (i₀ : ℕ) - (t + 1), by omega⟩ : Fin (r - (t + 1))) = i₀ := by
        ext; simp
      rw [he, if_pos le_rfl]
      exact hj₀

/-- `[[k,0,0],[0,I,0],[0,0,1]]` is integral when `k` is. -/
theorem rectGL_zero_mem_integralSubgroup {r t : ℕ} (h : t < r)
    {k : Matrix.GeneralLinearGroup (Fin (t + 1)) F} (hk : k ∈ integralSubgroup v.integer t) :
    rectGL h k 0 ∈ integralSubgroup v.integer r :=
  rectGL_mem_integralSubgroup h hk fun _ _ => zero_mem _

/-- **Splitting off the padded factor.** Under the hypotheses of `apply_rectGL`, if moreover
`f 1 = 1`, then for `k ∈ GL_(t+1)(𝒪)`, `w ∈ GL_(r+1)(𝒪)` and every `x`,
`f(diag(P, I) · [[k,0,0],[x,I,0],[0,0,1]] · w) = f(diag(P, I)) · f([[k,0,0],[x,I,0],[0,0,1]] · w)`:
both sides vanish unless `x` is integral, and otherwise equal `f(diag(P, I))`. -/
theorem apply_rectGL_zero_mul {r t : ℕ} (h : t < r) {θ : upperUnipotent (r + 1) F →* ℂˣ}
    {χ : F → ℂ}
    (hθ : ∀ u : upperUnipotent (r + 1) F,
      (θ u : ℂ) = χ (∑ i : Fin r,
        ((u : Matrix.GeneralLinearGroup (Fin (r + 1)) F) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) F) i.castSucc i.succ))
    (hχ : ∀ z ∉ v.integer, ∃ c ∈ v.integer, χ (c * z) ≠ 1)
    {f : Matrix.GeneralLinearGroup (Fin (r + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (r + 1) F) g,
      f ((u : Matrix.GeneralLinearGroup (Fin (r + 1)) F) * g) = θ u * f g)
    (hK : ∀ g, ∀ k ∈ integralSubgroup v.integer r, f (g * k) = f g) (hf1 : f 1 = 1)
    (P : Matrix.GeneralLinearGroup (Fin (t + 1)) F)
    {k : Matrix.GeneralLinearGroup (Fin (t + 1)) F} (hk : k ∈ integralSubgroup v.integer t)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F)
    {w : Matrix.GeneralLinearGroup (Fin (r + 1)) F} (hw : w ∈ integralSubgroup v.integer r) :
    f (rectGL h P 0 * (rectGL h k x * w)) = f (rectGL h P 0) * f (rectGL h k x * w) := by
  classical
  have e1 : rectGL h P 0 * (rectGL h k x * w) = rectGL h (P * k) x * w := by
    rw [← mul_assoc, rectGL_mul, Matrix.zero_mul, zero_add]
  have e2 : rectGL h (P * k) 0 = rectGL h P 0 * rectGL h k 0 := by
    rw [rectGL_mul, Matrix.zero_mul, zero_add]
  rw [e1, hK _ _ hw, hK _ _ hw, apply_rectGL h hθ hχ hf hK (P * k) x,
    apply_rectGL h hθ hχ hf hK k x, e2, hK _ _ (rectGL_zero_mem_integralSubgroup h hk)]
  have e3 : rectGL h k 0 = 1 * rectGL h k 0 := (one_mul _).symm
  rw [e3, hK _ _ (rectGL_zero_mem_integralSubgroup h hk), hf1]
  split_ifs <;> simp

section Standard

variable [TopologicalSpace F]

open Langlands.GeneralLinear.Spherical Langlands.Whittaker HarmonicAnalysis

open Classical in
/-- `apply_rectGL` for the spherical Whittaker function of the standard character of an
additive character `ψ` that is trivial on `𝒪` and nontrivial on `𝒪 z` for every `z ∉ 𝒪`. -/
theorem sphericalWhittaker_standard_rectGL {r t : ℕ} (h : t < r) {ϖ : Fˣ}
    (hϖ : IsUniformizingElement v ϖ) {ψ : UnitaryAdditiveCharacter F}
    (hψ : ∀ y ∈ v.integer, ψ y = 1)
    (hχ : ∀ z ∉ v.integer, ∃ c ∈ v.integer, ψ.complex (c * z) ≠ 1) (q : ℕ)
    (a : Fin (r + 1) → ℂˣ) (Q : Matrix.GeneralLinearGroup (Fin (t + 1)) F)
    (z : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F) :
    sphericalWhittaker hϖ (standardCharacter ψ r) q a (rectGL h Q z) =
      if ∀ i j, z i j ∈ v.integer then
        sphericalWhittaker hϖ (standardCharacter ψ r) q a (rectGL h Q 0) else 0 :=
  apply_rectGL h (fun u => standardCharacter_apply ψ r u) hχ
    (fun u g => sphericalWhittaker_mem hϖ q a (isIntegrallyTrivial_standardCharacter hψ r) u g)
    (fun g _ hk => sphericalWhittaker_mul_integral hϖ q a
      (isIntegrallyTrivial_standardCharacter hψ r) g hk) Q z

open Classical in
/-- `apply_rectGL` for the spherical Whittaker function of the inverse standard character. -/
theorem sphericalWhittaker_inverseStandard_rectGL {r t : ℕ} (h : t < r) {ϖ : Fˣ}
    (hϖ : IsUniformizingElement v ϖ) {ψ : UnitaryAdditiveCharacter F}
    (hψ : ∀ y ∈ v.integer, ψ y = 1)
    (hχ : ∀ z ∉ v.integer, ∃ c ∈ v.integer, ψ.complex (c * z) ≠ 1) (q : ℕ)
    (a : Fin (r + 1) → ℂˣ) (Q : Matrix.GeneralLinearGroup (Fin (t + 1)) F)
    (z : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F) :
    sphericalWhittaker hϖ (inverseStandardCharacter ψ r) q a (rectGL h Q z) =
      if ∀ i j, z i j ∈ v.integer then
        sphericalWhittaker hϖ (inverseStandardCharacter ψ r) q a (rectGL h Q 0) else 0 :=
  apply_rectGL h (χ := fun y => (ψ.complex y)⁻¹) (fun u => inverseStandardCharacter_apply ψ r u)
    (fun z hz => by
      obtain ⟨c, hc, hne⟩ := hχ z hz
      exact ⟨c, hc, fun h1 => hne (inv_eq_one.mp h1)⟩)
    (fun u g => sphericalWhittaker_mem hϖ q a
      (isIntegrallyTrivial_inverseStandardCharacter hψ r) u g)
    (fun g _ hk => sphericalWhittaker_mul_integral hϖ q a
      (isIntegrallyTrivial_inverseStandardCharacter hψ r) g hk) Q z

/-- `apply_rectGL_zero_mul` for the spherical Whittaker function of the inverse standard
character. -/
theorem sphericalWhittaker_inverseStandard_rectGL_zero_mul {r t : ℕ} (h : t < r) {ϖ : Fˣ}
    (hϖ : IsUniformizingElement v ϖ) {ψ : UnitaryAdditiveCharacter F}
    (hψ : ∀ y ∈ v.integer, ψ y = 1)
    (hχ : ∀ z ∉ v.integer, ∃ c ∈ v.integer, ψ.complex (c * z) ≠ 1) (q : ℕ)
    (a : Fin (r + 1) → ℂˣ) (P : Matrix.GeneralLinearGroup (Fin (t + 1)) F)
    {k : Matrix.GeneralLinearGroup (Fin (t + 1)) F} (hk : k ∈ integralSubgroup v.integer t)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) F)
    {w : Matrix.GeneralLinearGroup (Fin (r + 1)) F} (hw : w ∈ integralSubgroup v.integer r) :
    sphericalWhittaker hϖ (inverseStandardCharacter ψ r) q a
        (rectGL h P 0 * (rectGL h k x * w)) =
      sphericalWhittaker hϖ (inverseStandardCharacter ψ r) q a (rectGL h P 0) *
        sphericalWhittaker hϖ (inverseStandardCharacter ψ r) q a (rectGL h k x * w) :=
  apply_rectGL_zero_mul h (χ := fun y => (ψ.complex y)⁻¹)
    (fun u => inverseStandardCharacter_apply ψ r u)
    (fun z hz => by
      obtain ⟨c, hc, hne⟩ := hχ z hz
      exact ⟨c, hc, fun h1 => hne (inv_eq_one.mp h1)⟩)
    (fun u g => sphericalWhittaker_mem hϖ q a
      (isIntegrallyTrivial_inverseStandardCharacter hψ r) u g)
    (fun g _ hk => sphericalWhittaker_mul_integral hϖ q a
      (isIntegrallyTrivial_inverseStandardCharacter hψ r) g hk)
    (sphericalWhittaker_one hϖ q a (isIntegrallyTrivial_inverseStandardCharacter hψ r))
    P hk x hw

end Standard

end Valued

end Langlands.GeneralLinear.RectangularSupport
