import Langlands.Representation.Unitary.CompactQuotientUnitaryInductionStatement
import Langlands.Representation.Unitary.RelativeQuotientMeasure
import Langlands.Representation.Induction.CompactIntegralForm
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Renard IV.2.3: unitarity of normalized induction from a cocompact closed subgroup -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped NNReal ComplexConjugate Pointwise

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.PositiveFunctional

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (χ : H →* ℝ≥0)

/-- Pointwise application of a map `Φ : ℂ → ℂ` commuting with multiplication by
nonnegative real numbers. -/
def pointwise (Φ : ℂ → ℂ)
    (hΦ : ∀ (r : ℝ≥0) (z : ℂ), Φ (((r : ℝ) : ℂ) * z) = ((r : ℝ) : ℂ) * Φ z)
    (f : space H χ) : space H χ :=
  ⟨LocallyConstant.map Φ f.val, by
    refine ⟨fun h x => ?_, ?_⟩
    · change Φ (f.val (h.val * x)) = ((χ h : ℝ) : ℂ) * Φ (f.val x)
      rw [f.property.1 h x, hΦ]
    · obtain ⟨K, hK, hs⟩ := f.property.2
      refine ⟨K, hK, fun x hx => hs fun h0 => hx ?_⟩
      change Φ (f.val x) = 0
      rw [h0]
      simpa using hΦ 0 0⟩

omit [IsTopologicalGroup G] in
theorem pointwise_apply (Φ : ℂ → ℂ)
    (hΦ : ∀ (r : ℝ≥0) (z : ℂ), Φ (((r : ℝ) : ℂ) * z) = ((r : ℝ) : ℂ) * Φ z)
    (f : space H χ) (x : G) :
    (pointwise H χ Φ hΦ f).val x = Φ (f.val x) := rfl

/-- The pointwise real part. -/
def rePart (f : space H χ) : space H χ :=
  pointwise H χ (fun z => (z.re : ℂ)) (fun r z => by simp) f

/-- The pointwise imaginary part. -/
def imPart (f : space H χ) : space H χ :=
  pointwise H χ (fun z => (z.im : ℂ)) (fun r z => by simp) f

/-- The pointwise absolute value. -/
def normPart (f : space H χ) : space H χ :=
  pointwise H χ (fun z => (‖z‖ : ℂ)) (fun r z => by simp) f

/-- The pointwise complex conjugate. -/
def conjPart (f : space H χ) : space H χ :=
  pointwise H χ (fun z => conj z) (fun r z => by simp) f

omit [IsTopologicalGroup G] in
theorem re_add_im (ψ : space H χ) :
    rePart H χ ψ + Complex.I • imPart H χ ψ = ψ := by
  apply Subtype.ext
  ext x
  change ((ψ.val x).re : ℂ) + Complex.I * ((ψ.val x).im : ℂ) = ψ.val x
  rw [mul_comm]
  exact Complex.re_add_im _

omit [IsTopologicalGroup G] in
theorem conjPart_eq (ψ : space H χ) :
    conjPart H χ ψ = rePart H χ ψ - Complex.I • imPart H χ ψ := by
  apply Subtype.ext
  ext x
  change conj (ψ.val x) = ((ψ.val x).re : ℂ) - Complex.I * ((ψ.val x).im : ℂ)
  apply Complex.ext <;> simp

variable {H χ}

/-- Nonnegative real values, the positivity notion of Renard II.3.9. -/
def IsNonneg (f : space H χ) : Prop :=
  ∀ x : G, (f.val x).im = 0 ∧ 0 ≤ (f.val x).re

omit [IsTopologicalGroup G] in
/-- A positive functional is real on real functions dominated by a nonnegative one,
and bounded by its value there. -/
theorem sandwich (ν : Module.Dual ℂ (space H χ))
    (hpos : ∀ f : space H χ, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (ψ M : space H χ) (hψ : ∀ x, (ψ.val x).im = 0) (hM : ∀ x, (M.val x).im = 0)
    (hle : ∀ x, |(ψ.val x).re| ≤ (M.val x).re) :
    (ν ψ).im = 0 ∧ |(ν ψ).re| ≤ (ν M).re := by
  have h₁ := hpos (M + ψ) fun x => by
    change (M.val x + ψ.val x).im = 0 ∧ 0 ≤ (M.val x + ψ.val x).re
    simp only [Complex.add_im, Complex.add_re, hM, hψ, add_zero, true_and]
    linarith [neg_abs_le (ψ.val x).re, hle x]
  have h₂ := hpos (M - ψ) fun x => by
    change (M.val x - ψ.val x).im = 0 ∧ 0 ≤ (M.val x - ψ.val x).re
    simp only [Complex.sub_im, Complex.sub_re, hM, hψ, sub_zero, true_and]
    linarith [le_abs_self (ψ.val x).re, hle x]
  rw [map_add] at h₁
  rw [map_sub] at h₂
  simp only [Complex.add_im, Complex.add_re, Complex.sub_im, Complex.sub_re] at h₁ h₂
  exact ⟨by linarith [h₁.1, h₂.1], abs_le.mpr ⟨by linarith [h₁.2], by linarith [h₂.2]⟩⟩

omit [IsTopologicalGroup G] in
theorem im_apply_rePart (ν : Module.Dual ℂ (space H χ))
    (hpos : ∀ f : space H χ, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (ψ : space H χ) : (ν (rePart H χ ψ)).im = 0 :=
  (sandwich ν hpos (rePart H χ ψ) (normPart H χ ψ)
    (fun x => by simp [rePart, pointwise_apply])
    (fun x => by simp [normPart, pointwise_apply])
    (fun x => by simpa [rePart, normPart, pointwise_apply] using
      Complex.abs_re_le_norm (ψ.val x))).1

omit [IsTopologicalGroup G] in
theorem im_apply_imPart (ν : Module.Dual ℂ (space H χ))
    (hpos : ∀ f : space H χ, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (ψ : space H χ) : (ν (imPart H χ ψ)).im = 0 :=
  (sandwich ν hpos (imPart H χ ψ) (normPart H χ ψ)
    (fun x => by simp [imPart, pointwise_apply])
    (fun x => by simp [normPart, pointwise_apply])
    (fun x => by simpa [imPart, normPart, pointwise_apply] using
      Complex.abs_im_le_norm (ψ.val x))).1

omit [IsTopologicalGroup G] in
/-- A positive functional commutes with complex conjugation. -/
theorem apply_conjPart (ν : Module.Dual ℂ (space H χ))
    (hpos : ∀ f : space H χ, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (ψ : space H χ) : ν (conjPart H χ ψ) = conj (ν ψ) := by
  have ha := im_apply_rePart ν hpos ψ
  have hb := im_apply_imPart ν hpos ψ
  conv_rhs => rw [← re_add_im H χ ψ]
  rw [conjPart_eq, map_sub, map_add, map_smul]
  simp only [smul_eq_mul]
  apply Complex.ext <;> simp [ha, hb]

/-- Every element of the space is dominated by finitely many right translates of a
nonnegative element that does not vanish. -/
theorem exists_dominating (F ψ : space H χ) (hF : IsNonneg F) (x₀ : G)
    (hx₀ : F.val x₀ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ s : Finset G,
      ∀ x : G, ‖ψ.val x‖ ≤ C * ∑ g ∈ s, (F.val (x * g)).re := by
  classical
  have ha : 0 < (F.val x₀).re := by
    rcases (hF x₀).2.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext (by simpa using h.symm) (by simpa using (hF x₀).1)) hx₀
  obtain ⟨K, hK, hsK⟩ := ψ.property.2
  have hO : IsOpen {y : G | F.val y = F.val x₀} := F.val.isLocallyConstant.isOpen_fiber _
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun g : G => (fun y => y * g) ⁻¹' {y : G | F.val y = F.val x₀})
    (fun g => hO.preimage (continuous_id.mul continuous_const))
    (fun k _ => Set.mem_iUnion.mpr ⟨k⁻¹ * x₀, by
      change F.val (k * (k⁻¹ * x₀)) = F.val x₀
      rw [mul_inv_cancel_left]⟩)
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn ψ.val.continuous.continuousOn
  have hC : 0 ≤ max S 0 / (F.val x₀).re := div_nonneg (le_max_right _ _) ha.le
  refine ⟨max S 0 / (F.val x₀).re, hC, t, fun x => ?_⟩
  have hsum : 0 ≤ ∑ g ∈ t, (F.val (x * g)).re := Finset.sum_nonneg fun g _ => (hF _).2
  by_cases hx : ψ.val x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg hC hsum
  obtain ⟨h, hh, k, hk, rfl⟩ := hsK hx
  obtain ⟨g, hg, hkg⟩ : ∃ g ∈ t, F.val (k * g) = F.val x₀ := by
    have hmem := ht hk
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨g, hg, hkg⟩ := hmem
    exact ⟨g, hg, hkg⟩
  have hψx : ψ.val (h * k) = ((χ ⟨h, hh⟩ : ℝ) : ℂ) * ψ.val k := ψ.property.1 ⟨h, hh⟩ k
  have hFx : F.val (h * k * g) = ((χ ⟨h, hh⟩ : ℝ) : ℂ) * F.val x₀ := by
    rw [mul_assoc, ← hkg]
    exact F.property.1 ⟨h, hh⟩ (k * g)
  calc ‖ψ.val (h * k)‖ = (χ ⟨h, hh⟩ : ℝ) * ‖ψ.val k‖ := by
        rw [hψx, norm_mul, Complex.norm_of_nonneg (NNReal.coe_nonneg _)]
    _ ≤ (χ ⟨h, hh⟩ : ℝ) * max S 0 :=
        mul_le_mul_of_nonneg_left ((hS k hk).trans (le_max_left _ _)) (NNReal.coe_nonneg _)
    _ = max S 0 / (F.val x₀).re * (F.val (h * k * g)).re := by
        rw [hFx, Complex.re_ofReal_mul]
        field_simp
    _ ≤ max S 0 / (F.val x₀).re * ∑ g ∈ t, (F.val (h * k * g)).re :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun g => (F.val (h * k * g)).re)
            (fun g _ => (hF _).2) hg) hC

/-- Evaluation at a point, as a linear functional. -/
def evalAt (x : G) : space H χ →ₗ[ℂ] ℂ where
  toFun f := f.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A positive invariant functional vanishing on one nonzero nonnegative element vanishes. -/
theorem eq_zero_of_apply_eq_zero (ν : Module.Dual ℂ (space H χ))
    (hinv : ∀ (g : G) (f : space H χ), ν (rightAction H χ g f) = ν f)
    (hpos : ∀ f : space H χ, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (F : space H χ) (hF : IsNonneg F) (x₀ : G) (hx₀ : F.val x₀ ≠ 0) (h0 : ν F = 0) :
    ν = 0 := by
  refine LinearMap.ext fun ψ => ?_
  rw [LinearMap.zero_apply]
  obtain ⟨C, hC, s, hdom⟩ := exists_dominating F ψ hF x₀ hx₀
  let M : space H χ := (C : ℂ) • ∑ g ∈ s, rightAction H χ g F
  have hMx : ∀ x, M.val x = (C : ℂ) * ∑ g ∈ s, F.val (x * g) := by
    intro x
    change evalAt x M = _
    simp only [M, map_smul, map_sum, smul_eq_mul]
    rfl
  have hMre : ∀ x, (M.val x).re = C * ∑ g ∈ s, (F.val (x * g)).re := by
    intro x
    rw [hMx, Complex.re_ofReal_mul, Complex.re_sum]
  have hMim : ∀ x, (M.val x).im = 0 := by
    intro x
    rw [hMx, Complex.im_ofReal_mul, Complex.im_sum]
    simp [(hF _).1]
  have hνM : ν M = 0 := by
    simp only [M, map_smul, map_sum, hinv, h0, Finset.sum_const_zero, smul_zero]
  have hre := sandwich ν hpos (rePart H χ ψ) M (fun x => by simp [rePart, pointwise_apply])
    hMim (fun x => by
      rw [hMre]
      simpa [rePart, pointwise_apply] using (Complex.abs_re_le_norm _).trans (hdom x))
  have him := sandwich ν hpos (imPart H χ ψ) M (fun x => by simp [imPart, pointwise_apply])
    hMim (fun x => by
      rw [hMre]
      simpa [imPart, pointwise_apply] using (Complex.abs_im_le_norm _).trans (hdom x))
  rw [hνM, Complex.zero_re] at hre him
  have h1 : ν (rePart H χ ψ) = 0 := Complex.ext (abs_nonpos_iff.mp hre.2) hre.1
  have h2 : ν (imPart H χ ψ) = 0 := Complex.ext (abs_nonpos_iff.mp him.2) him.1
  rw [← re_add_im H χ ψ, map_add, map_smul, h1, h2, smul_zero, add_zero]

/-- Strict positivity: a nonzero positive invariant functional does not vanish on a
nonzero nonnegative element. -/
theorem apply_ne_zero (ν : Module.Dual ℂ (space H χ)) (hν : ν ≠ 0)
    (hinv : ∀ (g : G) (f : space H χ), ν (rightAction H χ g f) = ν f)
    (hpos : ∀ f : space H χ, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (F : space H χ) (hF : IsNonneg F) (x₀ : G) (hx₀ : F.val x₀ ≠ 0) : ν F ≠ 0 :=
  fun h0 => hν (eq_zero_of_apply_eq_zero ν hinv hpos F hF x₀ hx₀ h0)

end Langlands.HarmonicAnalysis.HomogeneousFunctions.PositiveFunctional

namespace Langlands.Renard.CompactRepresentation.UnitaryInduction

open Langlands.Induction Langlands.HarmonicAnalysis.HomogeneousFunctions
open Langlands.HarmonicAnalysis.HomogeneousFunctions.PositiveFunctional

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))

/-- The two published forms of `δ_{H\G}` agree. -/
theorem relativeModular_eq [LocallyCompactSpace H] (h : H) :
    relativeModular H hH h = ((relativePositiveModulus H h : ℝ≥0ˣ) : ℝ≥0) := by
  simp only [relativeModular, MonoidHom.coe_mk, OneHom.coe_mk,
    Langlands.HarmonicAnalysis.Distribution.renardModular_eq_inv, relativePositiveModulus,
    MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, Subgroup.coe_subtype, div_eq_mul_inv]
  rw [inv_inv, mul_comm]

/-- A compact set `K ⊆ G` with `G = H K`. -/
theorem exists_compact_cover [CompactSpace (LeftQuotient H)] :
    ∃ K : Set G, IsCompact K ∧ ∀ x : G, x ∈ (H : Set G) * K := by
  obtain ⟨K₀, hK₀c, -⟩ := Langlands.compactOpenSubgroupBasis G Set.univ Filter.univ_mem
  obtain ⟨t, ht⟩ := exists_finset_doubleCoset_cover H K₀
  refine ⟨(t : Set G) * (K₀ : Set G), t.finite_toSet.isCompact.mul hK₀c, fun x => ?_⟩
  obtain ⟨i, hi, p, hp, k, hk, rfl⟩ := ht x
  exact ⟨p, hp, i * k, ⟨i, hi, k, hk, rfl⟩, (mul_assoc _ _ _).symm⟩

theorem core_inner_smul_right {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (b : InnerProductSpace.Core ℂ V) (v w : V) (c : ℂ) :
    b.inner v (c • w) = c * b.inner v w := by
  rw [← b.conj_inner_symm, b.smul_left, map_mul, Complex.conj_conj, b.conj_inner_symm]

section Pairing

variable [CompactSpace (LeftQuotient H)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
  (b : InnerProductSpace.Core ℂ V)
  (hcov : ∀ (h : H) (v w : V),
    b.inner (ρ h v) (ρ h w) = ((relativeModular H hH h : ℝ) : ℂ) * b.inner v w)

/-- The function (IV.2.3.2) of two compactly induced functions, in `𝒟(G, H, δ_{H\G})`. -/
def pairing (f₁ f₂ : CompactFunctions H ρ) : renardSpace H hH :=
  ⟨⟨fun x => b.inner (eval H ρ f₁.1 x) (eval H ρ f₂.1 x),
      pairing_isLocallyConstant H ρ b f₁.1 f₂.1⟩, by
    refine ⟨fun h x => ?_, ?_⟩
    · change b.inner (eval H ρ f₁.1 (h.val * x)) (eval H ρ f₂.1 (h.val * x)) = _
      rw [eval_covariant, eval_covariant, hcov]
      rfl
    · obtain ⟨K, hK, hKG⟩ := exists_compact_cover H
      exact ⟨K, hK, fun x _ => hKG x⟩⟩

theorem pairing_apply (f₁ f₂ : CompactFunctions H ρ) (x : G) :
    (pairing H hH ρ b hcov f₁ f₂).val x = b.inner (eval H ρ f₁.1 x) (eval H ρ f₂.1 x) :=
  rfl

theorem pairing_add_left (f₁ f₂ f₃ : CompactFunctions H ρ) :
    pairing H hH ρ b hcov (f₁ + f₂) f₃ =
      pairing H hH ρ b hcov f₁ f₃ + pairing H hH ρ b hcov f₂ f₃ := by
  apply Subtype.ext
  ext x
  exact b.add_left _ _ _

theorem pairing_smul_left (f₁ f₂ : CompactFunctions H ρ) (c : ℂ) :
    pairing H hH ρ b hcov (c • f₁) f₂ = conj c • pairing H hH ρ b hcov f₁ f₂ := by
  apply Subtype.ext
  ext x
  exact b.smul_left _ _ _

theorem pairing_swap (f₁ f₂ : CompactFunctions H ρ) :
    pairing H hH ρ b hcov f₂ f₁ =
      conjPart H (relativeModular H hH) (pairing H hH ρ b hcov f₁ f₂) := by
  apply Subtype.ext
  ext x
  exact (b.conj_inner_symm _ _).symm

theorem pairing_translate (g : G) (f₁ f₂ : CompactFunctions H ρ) :
    pairing H hH ρ b hcov (compactInduced H ρ g f₁) (compactInduced H ρ g f₂) =
      rightAction H (relativeModular H hH) g (pairing H hH ρ b hcov f₁ f₂) := by
  apply Subtype.ext
  ext x
  rfl

theorem pairing_self_nonneg (f : CompactFunctions H ρ) :
    IsNonneg (pairing H hH ρ b hcov f f) := by
  intro x
  refine ⟨?_, b.re_inner_nonneg _⟩
  exact Complex.conj_eq_iff_im.mp (b.conj_inner_symm _ _)

theorem pairing_self_ne_zero {f : CompactFunctions H ρ} (hf : f ≠ 0) :
    ∃ x₀ : G, (pairing H hH ρ b hcov f f).val x₀ ≠ 0 := by
  by_contra hne
  push Not at hne
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact b.definite _ (hne x)

/-- The form `⟨f₁, f₂⟩ = ν(g ↦ ⟨f₁(g), f₂(g)⟩)` (IV.2.3.1) for a positive invariant
functional `ν` which is strictly positive on nonzero nonnegative elements. -/
def formOfFunctional (ν : Module.Dual ℂ (renardSpace H hH))
    (hinv : ∀ (g : G) (f : renardSpace H hH),
      ν (rightAction H (relativeModular H hH) g f) = ν f)
    (hpos : ∀ f : renardSpace H hH, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re)
    (hstrict : ∀ f : renardSpace H hH, IsNonneg f → ∀ x₀ : G, f.val x₀ ≠ 0 → ν f ≠ 0) :
    InvariantPositiveForm (compactInduced H ρ) where
  inner f₁ f₂ := ν (pairing H hH ρ b hcov f₁ f₂)
  conj_inner_symm f₁ f₂ := by
    change conj (ν (pairing H hH ρ b hcov f₂ f₁)) = ν (pairing H hH ρ b hcov f₁ f₂)
    rw [pairing_swap H hH ρ b hcov f₁ f₂, apply_conjPart ν hpos, Complex.conj_conj]
  re_inner_nonneg f := (hpos _ (pairing_self_nonneg H hH ρ b hcov f)).2
  add_left f₁ f₂ f₃ := by
    change ν (pairing H hH ρ b hcov (f₁ + f₂) f₃) = _
    rw [pairing_add_left, map_add]
  smul_left f₁ f₂ c := by
    change ν (pairing H hH ρ b hcov (c • f₁) f₂) = _
    rw [pairing_smul_left, map_smul, smul_eq_mul]
  definite f hf := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := pairing_self_ne_zero H hH ρ b hcov hne
    exact hstrict _ (pairing_self_nonneg H hH ρ b hcov f) x₀ hx₀ hf
  invariant g f₁ f₂ := by
    change ν (pairing H hH ρ b hcov (compactInduced H ρ g f₁) (compactInduced H ρ g f₂)) =
      ν (pairing H hH ρ b hcov f₁ f₂)
    rw [pairing_translate, hinv]

end Pairing

/-- A positive right-invariant functional on `𝒟(G, H, δ_{H\G})` which is strictly
positive on nonzero nonnegative elements, from the published relative-modulus
integral. -/
theorem exists_invariantFunctional [T2Space G] [LocallyCompactSpace H]
    [CompactSpace (LeftQuotient H)] :
    ∃ ν : Module.Dual ℂ (renardSpace H hH),
      (∀ (g : G) (f : renardSpace H hH),
        ν (rightAction H (relativeModular H hH) g f) = ν f) ∧
      (∀ f : renardSpace H hH, IsNonneg f → (ν f).im = 0 ∧ 0 ≤ (ν f).re) ∧
      (∀ f : renardSpace H hH, IsNonneg f → ∀ x₀ : G, f.val x₀ ≠ 0 → ν f ≠ 0) := by
  borelize G
  obtain ⟨μ, hμpos, hscalar⟩ := exists_compactQuotient_relativeMeasure H hH
  have hφ : ∀ (f : renardSpace H hH) (g : G),
      Integrable (fun k : (⊤ : Subgroup G) => f.val ((k : G) * g)) μ ∧
        (∫ k : (⊤ : Subgroup G), f.val ((k : G) * g) ∂μ) =
          ∫ k : (⊤ : Subgroup G), f.val (k : G) ∂μ := by
    intro f
    refine hscalar f.val f.val.isLocallyConstant fun q x => ?_
    rw [f.property.1 q x, relativeModular_eq]
  have hint : ∀ f : renardSpace H hH,
      Integrable (fun k : (⊤ : Subgroup G) => f.val (k : G)) μ := by
    intro f
    simpa only [mul_one] using (hφ f 1).1
  let ν : Module.Dual ℂ (renardSpace H hH) :=
    { toFun := fun f => ∫ k : (⊤ : Subgroup G), f.val (k : G) ∂μ
      map_add' := fun f₁ f₂ => integral_add (hint f₁) (hint f₂)
      map_smul' := fun c f => integral_const_mul c _ }
  have hν : ∀ f, ν f = ∫ k : (⊤ : Subgroup G), f.val (k : G) ∂μ := fun _ => rfl
  refine ⟨ν, fun g f => (hφ f g).2, ?_, ?_⟩
  · intro f hf
    rw [hν]
    constructor
    · have h := integral_im (hint f)
      simp only [RCLike.im_to_complex, (hf _).1, integral_zero] at h
      exact h.symm
    · have h := integral_re (hint f)
      simp only [RCLike.re_to_complex] at h
      rw [← h]
      exact integral_nonneg fun k => (hf _).2
  · intro f hf x₀ hx₀ h0
    have ha : 0 < (f.val x₀).re := by
      rcases (hf x₀).2.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by simpa using h.symm) (by simpa using (hf x₀).1)) hx₀
    have hF : (∫ k : (⊤ : Subgroup G), f.val ((k : G) * x₀) ∂μ) = 0 := by
      rw [(hφ f x₀).2]
      exact h0
    have hre : (∫ k : (⊤ : Subgroup G), (f.val ((k : G) * x₀)).re ∂μ) = 0 := by
      have h := integral_re (hφ f x₀).1
      simp only [RCLike.re_to_complex] at h
      rw [h, hF, Complex.zero_re]
    rw [integral_eq_zero_iff_of_nonneg (fun k => (hf _).2) (hφ f x₀).1.re] at hre
    let U : Set (⊤ : Subgroup G) := {k | f.val ((k : G) * x₀) = f.val x₀}
    have hUo : IsOpen U :=
      (f.val.isLocallyConstant.isOpen_fiber _).preimage
        (continuous_subtype_val.mul continuous_const)
    have hU1 : (1 : (⊤ : Subgroup G)) ∈ U := by
      change f.val (((1 : (⊤ : Subgroup G)) : G) * x₀) = f.val x₀
      rw [OneMemClass.coe_one, one_mul]
    have hμU : μ U = 0 := by
      apply measure_mono_null _ (ae_iff.mp hre)
      intro k hk
      change ¬ (f.val ((k : G) * x₀)).re = 0
      change f.val ((k : G) * x₀) = f.val x₀ at hk
      rw [hk]
      exact ha.ne'
    exact (hμpos U hUo hU1).ne' hμU

end Langlands.Renard.CompactRepresentation.UnitaryInduction

namespace Langlands.Renard.CompactRepresentation

open Langlands.Induction Langlands.HarmonicAnalysis.HomogeneousFunctions
open Langlands.HarmonicAnalysis.HomogeneousFunctions.PositiveFunctional
open Langlands.Renard.CompactRepresentation.UnitaryInduction

universe uG v

/-- Renard IV.2.3: normalized induction from a closed cocompact subgroup preserves
unitarity, with the explicit form (IV.2.3.1)–(IV.2.3.2). -/
theorem compactQuotientUnitaryInduction :
    CompactQuotientUnitaryInductionStatement.{uG, v} := by
  intro G _ _ _ _ _ H hH _ _ δ D R χ hχpos hχsq τ b σ I ev π
  have hδ : ∀ h : H, (χ.toMonoidHom h : ℂ) * (χ.toMonoidHom h : ℂ) =
      ((relativeModular H hH h : ℝ) : ℂ) := by
    intro h
    have h2 : (χ.toMonoidHom h : ℂ) ^ 2 =
        ((Hecke.Homomorphism.relativeModularCharacter H.subtype
          continuous_subtype_val).toMonoidHom h : ℂ) := hχsq h
    rw [← complexCharacter_relativePositiveModulus H] at h2
    rw [relativeModular_eq]
    simpa only [pow_two, Jacquet.complexCharacter_apply] using h2
  have hreal : ∀ h : H, conj (χ.toMonoidHom h : ℂ) = (χ.toMonoidHom h : ℂ) := by
    intro h
    obtain ⟨r, _, hr⟩ := hχpos h
    rw [hr, Complex.conj_ofReal]
  have hcov : ∀ (h : H) (v w : τ), b.inner (σ h v) (σ h w) =
      ((relativeModular H hH h : ℝ) : ℂ) * b.inner v w := by
    intro h v w
    change b.inner ((χ.toMonoidHom h : ℂ) • τ.representation h v)
      ((χ.toMonoidHom h : ℂ) • τ.representation h w) = _
    rw [b.smul_left, core_inner_smul_right b.toInnerProductCore, b.invariant, hreal,
      ← mul_assoc, hδ]
  refine ⟨⟨pairing H hH σ b.toInnerProductCore hcov, fun f₁ f₂ g => rfl, ?_⟩, ?_⟩
  · intro ν hν hinv hpos
    exact ⟨formOfFunctional H hH σ b.toInnerProductCore hcov ν hinv hpos
      (fun f hf x₀ hx₀ => apply_ne_zero ν hν hinv hpos f hf x₀ hx₀), fun _ _ => rfl⟩
  · obtain ⟨ν, hinv, hpos, hstrict⟩ := exists_invariantFunctional H hH
    exact ⟨formOfFunctional H hH σ b.toInnerProductCore hcov ν hinv hpos hstrict⟩

end Langlands.Renard.CompactRepresentation
