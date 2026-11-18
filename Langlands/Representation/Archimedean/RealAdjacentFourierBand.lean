import Langlands.Representation.Archimedean.RealCompactPolynomialFourierRelation
import Langlands.Representation.Archimedean.RealBlockFrobeniusDisjoint
import Langlands.Representation.Archimedean.RealSwapFLanding

/-! # The input band of an adjacent polynomial Fourier multiplier -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealAdjacentFourierBand

open Polynomial Complex RealOrthogonalUncertainty RealPolynomialFourierPropagation
  RealCompactPolynomialFourierRelation RealKTypeCount RealBlockFourierFinite

private theorem proj_pow_eq_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (v : W) (d : ℕ) (i : ℤ)
    (hv : ∀ j : ℤ, i - d ≤ j → j ≤ i + d → π j v = 0) :
    π i ((b ^ d) v) = 0 := by
  induction d generalizing i with
  | zero => simpa using hv i (by omega) (by omega)
  | succ d ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hsplit (w : W) :
          π i (b w) = (1 / 2 : ℂ) • (π i ((b - I • c) w) + π i ((b + I • c) w)) := by
        conv_lhs => rw [eq_half_raise_add_lower (b := b) (c := c)]
        rw [LinearMap.smul_apply, map_smul, LinearMap.add_apply, map_add]
      calc
        π i (b ((b ^ d) v)) =
            (1 / 2 : ℂ) •
              (π i ((b - I • c) ((b ^ d) v)) + π i ((b + I • c) ((b ^ d) v))) :=
          hsplit ((b ^ d) v)
        _ = 0 := by
          rw [hM.proj_apply_of_lie (lie_raise hab hca),
            hM.proj_apply_of_lie (lie_lower hab hca),
            ih (i - 1) (fun j hj hj' => hv j (by omega) (by omega)),
            ih (i - (-1)) (fun j hj hj' => hv j (by omega) (by omega)),
            map_zero, map_zero, add_zero, smul_zero]

/-- A polynomial in the adjacent generator uses only the indicated input band
for its output at mode `i`. -/
theorem proj_aeval_eq_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (v : W) (Q : ℂ[X]) (i : ℤ)
    (hv : ∀ j : ℤ, i - Q.natDegree ≤ j → j ≤ i + Q.natDegree → π j v = 0) :
    π i (aeval (-I • b) Q v) = 0 := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hd' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  rw [LinearMap.smul_apply, map_smul, smul_pow, LinearMap.smul_apply, map_smul,
    proj_pow_eq_zero hab hca hM v d i (fun j hj hj' => hv j (by omega) (by omega)),
    smul_zero, smul_zero]

theorem band_local {p q : ℕ} (hpq : q = 0 ∧ p = 1 ∨ q = 1 ∧ p = 0)
    {f g : Langlands.GeneralLinear 3 ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (Q : ℂ[X]) (i : ℤ)
    (hμ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 p j g x =
        Q.eval (j : ℂ) * blockFourierCoefficient 3 p j f x)
    (hband : ∀ j : ℤ, i - Q.natDegree ≤ j → j ≤ i + Q.natDegree →
      ∀ x ∈ unitaryCompact ℝ 3, blockFourierCoefficient 3 q j f x = 0) :
    ∀ x ∈ unitaryCompact ℝ 3, blockFourierCoefficient 3 q i g x = 0 := by
  have hp : p + 1 < 3 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hq : q + 1 < 3 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨Nf, hNf⟩ := exists_degreeLE hf hfK
  obtain ⟨Ng, hNg⟩ := exists_degreeLE hg hgK
  let N := max Nf Ng
  have hNf' : restrictLinear 3 f ∈ degreeLE 3 N := degreeLE_mono (le_max_left _ _) hNf
  have hNg' : restrictLinear 3 g ∈ degreeLE 3 N := degreeLE_mono (le_max_right _ _) hNg
  have heq := (relation_iff hp f g hNf' hNg' Q 1).mp
    (fun j x hx => by rw [hμ j x hx, eval_one, one_mul])
  rw [map_one, Module.End.one_apply] at heq
  obtain ⟨c, hab, _, hca⟩ := exists_relations N hpq hq hp
  have hz : proj N hq i (vector g hNg') = 0 := by
    rw [← heq]
    apply proj_aeval_eq_zero hab hca (isModeDecomposition N hq)
    intro j hj hj'
    apply Subtype.ext
    funext x
    rw [proj_restrict_apply hq j hNf', hband j hj hj' _ x.2, mul_zero]
    rfl
  intro x hx
  let κ : Matrix.unitaryGroup (Fin 3) ℝ := ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩
  have hx' := congrFun (congrArg Subtype.val hz) κ
  rw [proj_restrict_apply hq i hNg'] at hx'
  have hzero : blockFourierCoefficient 3 q i g (Unitary.toUnits κ) = 0 :=
    (mul_eq_zero.mp hx').resolve_left (inv_ne_zero two_pi_ne_zero)
  simpa only [κ, RealKTypeCount.toUnits_mk hx] using hzero

open RealOrthogonalBlock in
/-- The same input band controls an output mode on every ambient compact coset. -/
theorem band {n a r s : ℕ} (ha : a + 3 ≤ n)
    (hrs : s = 0 ∧ r = 1 ∨ s = 1 ∧ r = 0)
    {f g : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (Q : ℂ[X]) (i : ℤ)
    (hμ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (a + r) j g x =
        Q.eval (j : ℂ) * blockFourierCoefficient n (a + r) j f x)
    (hband : ∀ j : ℤ, i - Q.natDegree ≤ j → j ≤ i + Q.natDegree →
      ∀ x ∈ unitaryCompact ℝ n, blockFourierCoefficient n (a + s) j f x = 0) :
    ∀ x ∈ unitaryCompact ℝ n, blockFourierCoefficient n (a + s) i g x = 0 := by
  have hr : r + 1 < 3 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hs : s + 1 < 3 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  intro x hx
  have hloc := band_local hrs
    (continuous_restrictCoset a ha x hf) (continuous_restrictCoset a ha x hg)
    (restrictCoset_mem_kFiniteVectors a ha hx hfK)
    (restrictCoset_mem_kFiniteVectors a ha hx hgK) Q i
    (fun j k hk => by
      rw [blockFourierCoefficient_restrictCoset a ha hr, blockFourierCoefficient_restrictCoset a ha hr]
      exact hμ j _ ((unitaryCompact ℝ n).mul_mem (block_mem_unitaryCompact a ha hk) hx))
    (fun j hj hj' k hk => by
      rw [blockFourierCoefficient_restrictCoset a ha hs]
      exact hband j hj hj' _ ((unitaryCompact ℝ n).mul_mem (block_mem_unitaryCompact a ha hk) hx))
    1 (one_mem _)
  rw [blockFourierCoefficient_restrictCoset a ha hs] at hloc
  simpa only [map_one, one_mul] using hloc

open RealBlockJacquet RealBlockFrobeniusDisjoint RealSwapFLanding

local notation "Φ" => blockFourierCoefficient
local notation "G₄" => Langlands.GeneralLinear 4 ℝ
local notation "K₄" => unitaryCompact ℝ 4
local notation "CF₄" => kFiniteVectors (Whittaker.rightTranslation ℂ G₄) K₄

/-- Apply a second block coefficient to an equality of multiplier coefficients. -/
theorem coeff_multiplier {n p q : ℕ} {f g : Langlands.GeneralLinear n ℝ → ℂ}
    {μ : ℤ → ℂ}
    (hμ : ∀ i : ℤ, ∀ x ∈ unitaryCompact ℝ n, Φ n p i g x = μ i * Φ n p i f x)
    (i j : ℤ) {x : Langlands.GeneralLinear n ℝ} (hx : x ∈ unitaryCompact ℝ n) :
    Φ n q j (Φ n p i g) x = μ i * Φ n q j (Φ n p i f) x := by
  calc
    Φ n q j (Φ n p i g) x = Φ n q j (μ i • Φ n p i f) x :=
      blockFourierCoefficient_congr_on_compact (hμ i) hx j
    _ = _ := blockFourierCoefficient_smul q j _ _ _

theorem coeff_sub {n : ℕ} {f g : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (p : ℕ) (i : ℤ)
    (x : Langlands.GeneralLinear n ℝ) :
    Φ n p i (f - g) x = Φ n p i f x - Φ n p i g x := by
  rw [show f - g = f + (-1 : ℂ) • g by rw [neg_one_smul, sub_eq_add_neg]]
  rw [blockFourierCoefficient_add p i hf (hg.const_smul _),
    blockFourierCoefficient_smul]
  ring

/-- The double output coefficient uses only the rectangular input band for the
two disjoint outer rotations. -/
theorem rectangle {f g : G₄ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfK : f ∈ CF₄) (hgK : g ∈ CF₄) (Q : ℂ[X]) (i j : ℤ)
    (hμ : ∀ a : ℤ, ∀ x ∈ K₄, Φ 4 1 a g x = Q.eval (a : ℂ) * Φ 4 1 a f x)
    (hrect : ∀ a b : ℤ, i - Q.natDegree ≤ a → a ≤ i + Q.natDegree →
      j - Q.natDegree ≤ b → b ≤ j + Q.natDegree →
      ∀ x ∈ K₄, Φ 4 2 b (Φ 4 0 a f) x = 0) :
    ∀ x ∈ K₄, Φ 4 2 j (Φ 4 0 i g) x = 0 := by
  let μ : ℤ → ℂ := fun a =>
    if i - Q.natDegree ≤ a ∧ a ≤ i + Q.natDegree then 1 else 0
  obtain ⟨f', hf', hf'K, hcut⟩ := exists_multiplier (p := 0) (by decide) hf hfK μ
  obtain ⟨g', hg', hg'K, hpoly⟩ :=
    exists_multiplier (p := 1) (by decide) hf' hf'K (fun a => Q.eval (a : ℂ))
  have hdiff : ∀ x ∈ K₄, Φ 4 0 i g x = Φ 4 0 i g' x := by
    have hband := band (a := 0) (r := 1) (s := 0) (by decide) (Or.inl ⟨rfl, rfl⟩)
      (hf.sub hf') (hg.sub hg') (Submodule.sub_mem _ hfK hf'K)
      (Submodule.sub_mem _ hgK hg'K) Q i
      (fun a x hx => by
        simp only [Nat.zero_add, coeff_sub hf hf', coeff_sub hg hg', hμ a x hx,
          hpoly a x hx, mul_sub])
      (fun a ha ha' x hx => by
        have hcut₁ : μ a = 1 := by simp only [μ, ha, ha', and_self, ↓reduceIte]
        simp only [Nat.zero_add, coeff_sub hf hf', hcut a x hx, hcut₁,
          one_mul, sub_self])
    intro x hx
    exact sub_eq_zero.mp (by simpa only [Nat.zero_add, coeff_sub hg hg'] using hband x hx)
  have hd : (0 + 1 < (2 : ℕ)) ∨ 2 + 1 < 0 := Or.inl (by decide)
  have hzero : ∀ x ∈ K₄, Φ 4 2 j g' x = 0 := by
    apply band (a := 1) (r := 0) (s := 1) (by decide) (Or.inr ⟨rfl, rfl⟩)
      hf' hg' hf'K hg'K Q j hpoly
    intro b hb hb' x hx
    apply eq_zero_of_blockFourierCoefficient_eq_zero (p := 0) (by decide)
      (continuous_blockFourierCoefficient 2 b hf')
      (mem_kFiniteVectors_blockFourierCoefficient 2 b hf' hf'K) hx
    intro a
    rw [blockFourierCoefficient_comm hd hf', coeff_multiplier hcut a b hx]
    by_cases ha : i - Q.natDegree ≤ a ∧ a ≤ i + Q.natDegree
    · rw [hrect a b ha.1 ha.2 hb hb' x hx, mul_zero]
    · have hcut₀ : μ a = 0 := by simp only [μ, ha, ↓reduceIte]
      rw [hcut₀, zero_mul]
  intro x hx
  rw [blockFourierCoefficient_congr_on_compact hdiff hx j,
    ← blockFourierCoefficient_comm hd hg']
  exact (blockFourierCoefficient_congr_on_compact hzero hx i).trans
    (blockFourierCoefficient_zero_fun 0 i x)

end Langlands.Archimedean.RealAdjacentFourierBand

namespace Langlands.Archimedean

open Polynomial Complex RealBlockJacquet

/-- A polynomial multiplier on the middle rotation of `GL₄(ℝ)` uses only the
rectangular input band for a double Fourier coefficient on the outer rotations. -/
def RealAdjacentFourierBandStatement : Prop :=
  ∀ (f g : Langlands.GeneralLinear 4 ℝ → ℂ), Continuous f → Continuous g →
    f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 4 ℝ))
      (unitaryCompact ℝ 4) →
    g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 4 ℝ))
      (unitaryCompact ℝ 4) →
    ∀ (Q : ℂ[X]) (i j : ℤ),
    (∀ a : ℤ, ∀ x ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 1 a g x = Q.eval (a : ℂ) * blockFourierCoefficient 4 1 a f x) →
    (∀ a b : ℤ, i - Q.natDegree ≤ a → a ≤ i + Q.natDegree →
      j - Q.natDegree ≤ b → b ≤ j + Q.natDegree → ∀ x ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 2 b (blockFourierCoefficient 4 0 a f) x = 0) →
    ∀ x ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 2 j (blockFourierCoefficient 4 0 i g) x = 0

theorem realAdjacentFourierBand : RealAdjacentFourierBandStatement :=
  fun _ _ hf hg hfK hgK Q i j => RealAdjacentFourierBand.rectangle hf hg hfK hgK Q i j

end Langlands.Archimedean
