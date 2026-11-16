import Langlands.Global.RankinSelberg.EqualUnfoldingFiber

/-! # The counting and fiber hypotheses for `GL_n` in the equal-rank unfolding -/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalCountSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalCountSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Determinant

theorem detNorm_inv_eq (n : ℕ) (x : Points F n) : detNorm F n x⁻¹ = (detNorm F n x)⁻¹ := by
  have h := detNorm_mul F n x x⁻¹
  rw [mul_inv_cancel, detNorm_of_mem_rationalSubgroup F n (Subgroup.one_mem _)] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The slab `{g : 1 ≤ |det g| < e^n}` in `GL_n(𝔸)`. -/
def slabSet (n : ℕ) : Set (Points F n) :=
  {g | 1 ≤ detNorm F n g ∧ detNorm F n g < Real.exp n}

theorem slabSet_eq_preimage (n : ℕ) :
    slabSet F n = detNorm F n ⁻¹' Ico 1 (Real.exp n) := rfl

theorem measurableSet_slabSet (n : ℕ) : MeasurableSet (slabSet F n) := by
  rw [slabSet_eq_preimage]
  exact (continuous_detNorm F n).measurable measurableSet_Ico

end Determinant

variable (r : ℕ)

section Cosets

/-- Representatives `γ_q ∈ GL_n(F) ⊆ GL_n(𝔸)` of the cosets `P'_n(F) \ GL_n(F)`, the
summation index of the Eisenstein series. -/
def eisensteinCosetRep (q : LeftCosetSpace (eisensteinParabolic F r)) : Points F (r + 1) :=
  rationalPoint F (r + 1) q.out

theorem eisensteinCosetRep_mem (q : LeftCosetSpace (eisensteinParabolic F r)) :
    eisensteinCosetRep F r q ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)) :=
  rationalPoint_mem_rationalSubgroup F _ _

theorem rationalPoint_mem_eisensteinRationalImage_iff (g : RationalGL F (r + 1)) :
    rationalPoint F (r + 1) g ∈ eisensteinRationalImage F r ↔ g ∈ eisensteinParabolic F r := by
  constructor
  · rintro ⟨h, hh, he⟩
    rwa [← rationalPoint_injective F _ he]
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- Every `γ ∈ GL_n(F)` lies in exactly one coset `P'_n(F) γ_q`. -/
theorem existsUnique_eisensteinCosetRep {k : Points F (r + 1)}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1))) :
    ∃! q : LeftCosetSpace (eisensteinParabolic F r),
      k * (eisensteinCosetRep F r q)⁻¹ ∈ eisensteinRationalImage F r := by
  obtain ⟨g, rfl⟩ := exists_rationalPoint_eq F (r + 1) hk
  have key : ∀ q : LeftCosetSpace (eisensteinParabolic F r),
      rationalPoint F (r + 1) g * (eisensteinCosetRep F r q)⁻¹ ∈ eisensteinRationalImage F r ↔
        LeftCosetSpace.mk _ g = q := by
    intro q
    have hq : LeftCosetSpace.mk (eisensteinParabolic F r) q.out = q := Quotient.out_eq q
    rw [eisensteinCosetRep, ← rationalPoint_inv, ← rationalPoint_mul,
      rationalPoint_mem_eisensteinRationalImage_iff]
    conv_rhs => rw [← hq]
    rw [LeftCosetSpace.mk_eq_mk_iff]
    constructor
    · intro h
      simpa [mul_inv_rev] using Subgroup.inv_mem _ h
    · intro h
      simpa [mul_inv_rev] using Subgroup.inv_mem _ h
  exact ⟨LeftCosetSpace.mk _ g, (key _).mpr rfl, fun q hq => ((key q).mp hq).symm⟩

instance countable_eisensteinCosets : Countable (LeftCosetSpace (eisensteinParabolic F r)) :=
  (LeftCosetSpace.mk_surjective (eisensteinParabolic F r)).countable

/-- The strict fundamental domain `D' = ⋃_q γ_q D` of `P'_n(F)`, with `D` the chosen
fundamental domain of `GL_n(F)`. -/
def eisensteinDomain : Set (Points F (r + 1)) :=
  ⋃ q, eisensteinCosetRep F r q • LeftCosetSpace.fundamentalDomain
    (AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)))
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F (r + 1)))

theorem measurableSet_eisensteinDomain : MeasurableSet (eisensteinDomain F r) :=
  MeasurableSet.iUnion fun _ =>
    (LeftCosetSpace.measurableSet_fundamentalDomain _ _).const_smul _

theorem existsUnique_mem_eisensteinDomain (x : Points F (r + 1)) :
    ∃! l : eisensteinRationalImage F r, (l : Points F (r + 1)) * x ∈ eisensteinDomain F r :=
  existsUnique_mem_iUnion_smul (eisensteinRationalImage_le F r)
    (LeftCosetSpace.fundamentalDomain_unique _ _) (eisensteinCosetRep F r)
    (eisensteinCosetRep_mem F r) (fun _ hk => existsUnique_eisensteinCosetRep F r hk) x

end Cosets

section Counting

theorem detNorm_scalarPoint_mul_inv_mul {b : Points F 1}
    (hb : b ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
    {p : Points F (r + 1)} (hp : p ∈ mirabolicRationalImage F r) (w : Points F (r + 1)) :
    detNorm F (r + 1) (scalarPoint F r b * (p⁻¹ * w)) = detNorm F (r + 1) w := by
  rw [detNorm_mul, detNorm_mul, detNorm_scalarPoint, detNorm_of_mem_rationalSubgroup F 1 hb,
    detNorm_of_mem_rationalSubgroup F (r + 1) (mirabolicRationalImage_le F r (Subgroup.inv_mem _ hp)),
    one_pow, one_mul, one_mul]

/-- The counting identity: for a set `T` of norms, the translates
`diag(b, …, b) p⁻¹ w` (`b ∈ GL_1(F)`, `p ∈ P_n(F)`) lie in `D' ∩ {|det| ∈ T}` exactly once
when `|det w| ∈ T`, and never otherwise. -/
theorem tsum_indicator_eisensteinDomain (T : Set ℝ) (w : Points F (r + 1)) :
    ∑' b : AdelicGroupPoints.rationalSubgroup F (Scheme F 1), ∑' p : mirabolicRationalImage F r,
      (eisensteinDomain F r ∩ detNorm F (r + 1) ⁻¹' T).indicator
        (1 : Points F (r + 1) → ℝ≥0∞) (scalarPoint F r b * ((p : Points F (r + 1))⁻¹ * w)) =
      (detNorm F (r + 1) ⁻¹' T).indicator 1 w := by
  by_cases hw : w ∈ detNorm F (r + 1) ⁻¹' T
  · rw [indicator_of_mem hw]
    obtain ⟨l, hl, hlu⟩ := existsUnique_mem_eisensteinDomain F r w
    obtain ⟨b₀, hb₀, p₀, hp₀, he⟩ := exists_scalarPoint_mul_inv F r l.property
    have hmemT : ∀ (b : AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
        (p : mirabolicRationalImage F r),
        scalarPoint F r b * ((p : Points F (r + 1))⁻¹ * w) ∈ detNorm F (r + 1) ⁻¹' T := by
      intro b p
      rw [mem_preimage, detNorm_scalarPoint_mul_inv_mul F r b.property p.property]
      exact hw
    have hzero : ∀ (b : AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
        (p : mirabolicRationalImage F r), (b ≠ ⟨b₀, hb₀⟩ ∨ p ≠ ⟨p₀, hp₀⟩) →
        (eisensteinDomain F r ∩ detNorm F (r + 1) ⁻¹' T).indicator
          (1 : Points F (r + 1) → ℝ≥0∞) (scalarPoint F r b * ((p : Points F (r + 1))⁻¹ * w)) = 0 := by
      intro b p hbp
      rw [indicator_of_notMem]
      rintro ⟨hD, -⟩
      have hΛ : scalarPoint F r b * (p : Points F (r + 1))⁻¹ ∈ eisensteinRationalImage F r :=
        Subgroup.mul_mem _ (scalarPoint_mem_eisensteinRationalImage F r b.property)
          (mirabolicRationalImage_le_eisensteinRationalImage F r (Subgroup.inv_mem _ p.property))
      have h1 := hlu ⟨_, hΛ⟩ (show scalarPoint F r b * (p : Points F (r + 1))⁻¹ * w ∈
        eisensteinDomain F r by rw [mul_assoc]; exact hD)
      have h2 : scalarPoint F r b * (p : Points F (r + 1))⁻¹ = scalarPoint F r b₀ * p₀⁻¹ := by
        rw [he]
        exact congrArg Subtype.val h1
      obtain ⟨hb, hp⟩ := scalarPoint_mul_inv_injective F r b.property hb₀ p.property hp₀ h2
      rcases hbp with hbp | hbp
      · exact hbp (Subtype.ext hb)
      · exact hbp (Subtype.ext hp)
    rw [tsum_eq_single ⟨b₀, hb₀⟩ fun b hb =>
        ENNReal.tsum_eq_zero.mpr fun p => hzero b p (Or.inl hb),
      tsum_eq_single ⟨p₀, hp₀⟩ fun p hp => hzero _ p (Or.inr hp)]
    rw [indicator_of_mem]
    · rfl
    refine ⟨?_, hmemT _ _⟩
    change scalarPoint F r b₀ * (p₀⁻¹ * w) ∈ eisensteinDomain F r
    rw [← mul_assoc, he]
    exact hl
  · rw [indicator_of_notMem hw]
    refine ENNReal.tsum_eq_zero.mpr fun b => ENNReal.tsum_eq_zero.mpr fun p => ?_
    rw [indicator_of_notMem]
    rintro ⟨-, hT⟩
    apply hw
    rw [mem_preimage, ← detNorm_scalarPoint_mul_inv_mul F r b.property p.property]
    exact hT

/-- The slice of the slab: `{z : 1 ≤ |det((a)⁻¹ x)| < e^n}` is the band
`{c < |a| ≤ e c}` with `c = |det x|^(1/n) / e`. -/
theorem setOf_scalarPoint_inv_mul_mem_slabSet (x : Points F (r + 1)) :
    {z : Points F 1 | (scalarPoint F r z)⁻¹ * x ∈ slabSet F (r + 1)} =
      {z | Real.exp (Real.log (detNorm F (r + 1) x) / ((r + 1 : ℕ) : ℝ) - 1) < detNorm F 1 z ∧
        detNorm F 1 z ≤
          Real.exp 1 * Real.exp (Real.log (detNorm F (r + 1) x) / ((r + 1 : ℕ) : ℝ) - 1)} := by
  have hN : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  ext z
  simp only [slabSet, mem_ofPred_eq]
  rw [detNorm_mul, ← map_inv, detNorm_scalarPoint, detNorm_inv_eq]
  have ht := detNorm_pos F 1 z
  have hd := detNorm_pos F (r + 1) x
  generalize detNorm F 1 z = t at ht ⊢
  generalize detNorm F (r + 1) x = d at hd ⊢
  obtain ⟨u, rfl⟩ : ∃ u, Real.exp u = t := ⟨Real.log t, Real.exp_log ht⟩
  obtain ⟨L, rfl⟩ : ∃ L, Real.exp L = d := ⟨Real.log d, Real.exp_log hd⟩
  have e0 : ((Real.exp u)⁻¹) ^ (r + 1) * Real.exp L =
      Real.exp (L - ((r + 1 : ℕ) : ℝ) * u) := by
    rw [Real.exp_sub, Real.exp_nat_mul, inv_pow, div_eq_mul_inv, mul_comm]
  have e1 : Real.exp 1 * Real.exp (L / ((r + 1 : ℕ) : ℝ) - 1) =
      Real.exp (L / ((r + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e0, Real.log_exp, e1, Real.one_le_exp_iff, Real.exp_lt_exp, Real.exp_lt_exp,
    Real.exp_le_exp]
  have k1 : L / ((r + 1 : ℕ) : ℝ) - 1 < u ↔ L - ((r + 1 : ℕ) : ℝ) * u < ((r + 1 : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hN]
    constructor <;> intro h <;> linarith
  have k2 : u ≤ L / ((r + 1 : ℕ) : ℝ) ↔ 0 ≤ L - ((r + 1 : ℕ) : ℝ) * u := by
    rw [le_div_iff₀ hN]
    constructor <;> intro h <;> linarith
  rw [k1, k2, and_comm]

/-- The fiber mass: if the bands `{c < |a| ≤ e c}` in a set `D₁ ⊆ GL_1(𝔸)` have measure one,
then so do the slices `{z ∈ D₁ : diag(a, …, a)⁻¹ x ∈ S}` of the slab `S`. -/
theorem measure_inter_scalarPoint_inv_mul_mem_slabSet (ν : Measure (Points F 1))
    {D₁ : Set (Points F 1)}
    (hslab : ∀ c : ℝ, 0 < c →
      ν (D₁ ∩ {z | c < detNorm F 1 z ∧ detNorm F 1 z ≤ Real.exp 1 * c}) = 1)
    (x : Points F (r + 1)) :
    ν (D₁ ∩ {z | (scalarPoint F r z)⁻¹ * x ∈ slabSet F (r + 1)}) = 1 := by
  rw [setOf_scalarPoint_inv_mul_mem_slabSet]
  exact hslab _ (Real.exp_pos _)

end Counting

section Fiber

instance countable_rationalSubgroup (n : ℕ) :
    Countable (AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :=
  LeftCosetSpace.countable_of_isDiscrete _ (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n))

instance countable_mirabolicRationalImage : Countable (mirabolicRationalImage F r) :=
  LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_mirabolicRationalImage F r)

/-- The chosen fundamental domain of `GL_1(F)` in `GL_1(𝔸)`. -/
abbrev ideleDomain : Set (Points F 1) :=
  LeftCosetSpace.fundamentalDomain (AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F 1))

/-- The chosen fundamental domain of `P_n(F)` in `GL_n(𝔸)`. -/
abbrev mirabolicDomain : Set (Points F (r + 1)) :=
  LeftCosetSpace.fundamentalDomain (mirabolicRationalImage F r)
    (isDiscrete_mirabolicRationalImage F r)

/-- The fiber computation for `GL_n`: for a measurable left `P_n(F)`-invariant `K`
integrable on the fundamental domain of `P_n(F)`, `(x, a) ↦ K(diag(a, …, a) x)` is
integrable on `(D' ∩ S) × 𝔸^×` with the same integral. The band masses are a hypothesis. -/
theorem integrable_and_integral_slabFiber
    (hslab : ∀ c : ℝ, 0 < c → ideleMeasure F (ideleDomain F ∩
      {z | c < detNorm F 1 z ∧ detNorm F 1 z ≤ Real.exp 1 * c}) = 1)
    {K : Points F (r + 1) → ℂ} (hK : Measurable K)
    (hKP : ∀ p ∈ mirabolicRationalImage F r, ∀ x, K (p * x) = K x)
    (hint : IntegrableOn K (mirabolicDomain F r) Measure.haar) :
    Integrable (fun q : Points F (r + 1) × Points F 1 => K (scalarPoint F r q.2 * q.1))
        (((Measure.haar : Measure (Points F (r + 1))).restrict
          (eisensteinDomain F r ∩ slabSet F (r + 1))).prod (ideleMeasure F)) ∧
      ∫ q, K (scalarPoint F r q.2 * q.1) ∂(((Measure.haar : Measure (Points F (r + 1))).restrict
          (eisensteinDomain F r ∩ slabSet F (r + 1))).prod (ideleMeasure F)) =
        ∫ x in mirabolicDomain F r, K x ∂Measure.haar := by
  refine integrable_and_integral_fiber (Measure.haar : Measure (Points F (r + 1)))
    (ideleMeasure F) (AdelicGroupPoints.rationalSubgroup F (Scheme F 1))
    (mirabolicRationalImage F r) (continuous_scalarPoint F r).measurable
    (scalarPoint_commute F r)
    (LeftCosetSpace.isFundamentalDomain _
      (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F 1)) _)
    (LeftCosetSpace.isFundamentalDomain _ (isDiscrete_mirabolicRationalImage F r) _)
    ((measurableSet_eisensteinDomain F r).inter (measurableSet_slabSet F (r + 1)))
    (measurableSet_slabSet F (r + 1)) ?_ ?_ hK (fun p x => hKP p p.property x) hint
  · intro w
    rw [slabSet_eq_preimage]
    exact tsum_indicator_eisensteinDomain F r _ w
  · exact measure_inter_scalarPoint_inv_mul_mem_slabSet F r (ideleMeasure F) hslab

end Fiber

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
