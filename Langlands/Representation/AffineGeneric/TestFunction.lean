import Langlands.Representation.AffineGeneric.Genericity
import Langlands.BaseChange.CuspForm

/-!
# The test functions `1_{I⁺} · ψ(λ_r)` and their vanishing constant terms

For `ϖ : Fˣ`, an additive character `ψ` of the residue field `k` and
`r : Fin (m + 1) → k`, the test function `f = 1_{I⁺} · ψ(λ_r)` takes the value
`ψ(λ_r(g))` on `I⁺` and is zero off `I⁺`. It is locally constant with compact support.

For a uniformizer `ϖ`, its restriction `ψ ∘ λ_r` to `I⁺` is a character. For `z ∈ I⁺`,
both `f(z g)` and `f(g z)` equal `ψ(λ_r(z)) f(g)`. When `ψ` is nontrivial and every
`r_i` is nonzero, the integrals along all proper standard block unipotent radicals vanish
after any two-sided translation. In that case the character on `I⁺` is affine generic
when `m ≥ 1`, as described in `Genericity`. For `m = 0` the character factors through
the principal-unit map `1 + 𝔭 → k`, and there are no proper standard block parabolics.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear HarmonicAnalysis

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {m : ℕ}

/-! ### Local constancy of the coordinates -/

theorem groupCoord_eventuallyEq (ϖ : Fˣ) (g : GeneralLinear (m + 1) F) (i : Fin (m + 1)) :
    ∀ᶠ h in 𝓝 g, groupCoord ϖ h i = groupCoord ϖ g i := by
  unfold groupCoord coord
  have hc : Continuous fun h : GeneralLinear (m + 1) F =>
      weight ϖ i * ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) i (finRotate (m + 1) i) := by
    simp only [Matrix.sub_apply]
    exact continuous_const.mul ((GeneralLinear.entry i _).continuous.sub continuous_const)
  exact (hc.tendsto g).eventually (resOf_eventuallyEq _)

theorem affineForm_eventuallyEq (ϖ : Fˣ) (r : Fin (m + 1) → Residue F)
    (g : GeneralLinear (m + 1) F) :
    ∀ᶠ h in 𝓝 g, affineForm ϖ r h = affineForm ϖ r g := by
  filter_upwards [Filter.eventually_all.2 fun i => groupCoord_eventuallyEq ϖ g i] with h hh
  unfold affineForm
  simp only [hh]

/-! ### The test function -/

variable (ϖ : Fˣ) (ψ : AddChar (Residue F) ℂ) (r : Fin (m + 1) → Residue F)

/-- The test function `1_{I⁺} · ψ(λ_r)` takes the value `ψ(λ_r(g))` on `I⁺` and is zero off
`I⁺`. For a uniformizer `ϖ`, its restriction to `I⁺` is a character. -/
def testFunction : GeneralLinear (m + 1) F → ℂ :=
  (iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F)).indicator
    fun g => ψ (affineForm ϖ r g)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem testFunction_of_mem {g : GeneralLinear (m + 1) F} (hg : g ∈ iwahoriRadical m) :
    testFunction ϖ ψ r g = ψ (affineForm ϖ r g) :=
  Set.indicator_of_mem (s := (iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F))) hg _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem testFunction_of_not_mem {g : GeneralLinear (m + 1) F} (hg : g ∉ iwahoriRadical m) :
    testFunction ϖ ψ r g = 0 :=
  Set.indicator_of_notMem (s := (iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F))) hg _

theorem isLocallyConstant_testFunction : IsLocallyConstant (testFunction ϖ ψ r) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hg : g ∈ iwahoriRadical m
  · filter_upwards [isOpen_iwahoriRadical.mem_nhds hg, affineForm_eventuallyEq ϖ r g]
      with h hh hlam
    rw [testFunction_of_mem ϖ ψ r hh, testFunction_of_mem ϖ ψ r hg, hlam]
  · have hc : IsOpen ((iwahoriRadical (F := F) m : Set (GeneralLinear (m + 1) F))ᶜ) :=
      (Subgroup.isClosed_of_isOpen _ isOpen_iwahoriRadical).isOpen_compl
    filter_upwards [hc.mem_nhds hg] with h hh
    rw [testFunction_of_not_mem ϖ ψ r hh, testFunction_of_not_mem ϖ ψ r hg]

theorem hasCompactSupport_testFunction : HasCompactSupport (testFunction ϖ ψ r) :=
  HasCompactSupport.intro' isCompact_iwahoriRadical
    (Subgroup.isClosed_of_isOpen _ isOpen_iwahoriRadical)
    fun _ hg => testFunction_of_not_mem ϖ ψ r hg

/-- The test function `1_{I⁺} · ψ(λ_r)` as an element of `C_c^∞(GL_{m+1}(F))`. -/
def affineGenericTest : SchwartzBruhat (GeneralLinear (m + 1) F) :=
  ⟨testFunction ϖ ψ r, isLocallyConstant_testFunction ϖ ψ r,
    hasCompactSupport_testFunction ϖ ψ r⟩

@[simp] theorem affineGenericTest_apply (g : GeneralLinear (m + 1) F) :
    affineGenericTest ϖ ψ r g = testFunction ϖ ψ r g := rfl

/-! ### Translation by `I⁺` -/

variable {ϖ} (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
include hϖ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem testFunction_mul_left {z : GeneralLinear (m + 1) F} (hz : z ∈ iwahoriRadical m)
    (g : GeneralLinear (m + 1) F) :
    testFunction ϖ ψ r (z * g) = ψ (affineForm ϖ r z) * testFunction ϖ ψ r g := by
  by_cases hg : g ∈ iwahoriRadical m
  · rw [testFunction_of_mem ϖ ψ r (mul_mem hz hg), testFunction_of_mem ϖ ψ r hg,
      affineForm_mul hϖ r hz hg, AddChar.map_add_eq_mul]
  · have hzg : z * g ∉ iwahoriRadical m := fun h =>
      hg (by simpa using mul_mem (inv_mem hz) h)
    rw [testFunction_of_not_mem ϖ ψ r hzg, testFunction_of_not_mem ϖ ψ r hg, mul_zero]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem testFunction_mul_right {z : GeneralLinear (m + 1) F} (hz : z ∈ iwahoriRadical m)
    (g : GeneralLinear (m + 1) F) :
    testFunction ϖ ψ r (g * z) = testFunction ϖ ψ r g * ψ (affineForm ϖ r z) := by
  by_cases hg : g ∈ iwahoriRadical m
  · rw [testFunction_of_mem ϖ ψ r (mul_mem hg hz), testFunction_of_mem ϖ ψ r hg,
      affineForm_mul hϖ r hg hz, AddChar.map_add_eq_mul]
  · have hgz : g * z ∉ iwahoriRadical m := fun h =>
      hg (by simpa using mul_mem h (inv_mem hz))
    rw [testFunction_of_not_mem ϖ ψ r hgz, testFunction_of_not_mem ϖ ψ r hg, zero_mul]

/-! ### Vanishing constant terms -/

/-- **Cuspidality.** For a uniformizer `ϖ`, nontrivial `ψ` and all `r_i ≠ 0`, the test
function `1_{I⁺} · ψ(λ_r)` has vanishing constant terms along every proper standard block
parabolic after any two-sided translation. -/
theorem hasVanishingConstantTerms_testFunction (hψ : ψ ≠ 1) (hr : ∀ i, r i ≠ 0) :
    BaseChange.HasVanishingConstantTerms (testFunction ϖ ψ r) := by
  let _ : MeasurableSpace (GeneralLinear (m + 1) F) := borel _
  have _ : BorelSpace (GeneralLinear (m + 1) F) := ⟨rfl⟩
  intro B hB μ hμ
  let U := B.unipotentSubgroup F
  let φ := affineGenericTest ϖ ψ r
  have hint : ∀ x y : GeneralLinear (m + 1) F,
      Integrable (fun u : U => testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y)) μ := by
    intro x y
    let t := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)
    have ht : Topology.IsClosedEmbedding (fun u : U => t u.val) :=
      t.isClosedEmbedding.comp (B.isClosed_unipotentSubgroup F).isClosedEmbedding_subtypeVal
    exact (φ.continuous.comp ht.continuous).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.comp_isClosedEmbedding ht)
  refine ⟨hint, fun x y => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext _ _ fun s => by rw [h s, AddChar.one_apply])
  obtain ⟨u0, hu0, hz, hlam⟩ := exists_unipotent_affineForm_eq hϖ r hr t x B hB
  change ∫ u : U, testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y) ∂μ = 0
  have key : ∫ u : U, testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y) ∂μ =
      ψ t * ∫ u : U, testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y) ∂μ := by
    calc ∫ u : U, testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y) ∂μ
        = ∫ u : U, testFunction ϖ ψ r
            (x * ((⟨u0, hu0⟩ * u : U) : GeneralLinear (m + 1) F) * y) ∂μ :=
          (integral_mul_left_eq_self
            (fun u : U => testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y))
            ⟨u0, hu0⟩).symm
      _ = ∫ u : U, ψ t * testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y) ∂μ := by
          congr 1
          funext u
          have he : x * ((⟨u0, hu0⟩ * u : U) : GeneralLinear (m + 1) F) * y =
              (x * u0 * x⁻¹) * (x * (u : GeneralLinear (m + 1) F) * y) := by
            simp only [Subgroup.coe_mul]
            group
          rw [he, testFunction_mul_left ψ r hϖ hz, hlam]
      _ = _ := integral_const_mul _ _
  have h0 : (1 - ψ t) *
      ∫ u : U, testFunction ϖ ψ r (x * (u : GeneralLinear (m + 1) F) * y) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h).symm ht
  · exact h

end Langlands.AffineGeneric
