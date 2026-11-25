import Langlands.BaseChange.NearIdentityMatchingStatement
import Langlands.BaseChange.NearIdentityConcordance

/-!
# Matching of test functions near the identity for cyclic base change

Proof of `NearIdentityMatchingStatement` (`nearIdentityMatching`), with the two directions in a
sharper form, with an explicit radius and an explicit formula for the transferred function:
`exists_concordant_ordinary_of_support_normCongruence` (from `GL_n(E)` to `GL_n(F)`) and
`exists_concordant_twisted_of_support_normCongruence` (from `GL_n(F)` to `GL_n(E)`). Both rest on
`areConcordant_of_integral_eq` for the spectral congruence subgroup of radius `r < ‖l‖`. See the
paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set _root_.Topology
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands
open Langlands.HarmonicAnalysis Langlands.GeneralLinear

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section Generic

/-- A function equal to a locally constant `a ∘ p⁻¹` on the open image of a compact set under a
continuous map, and to zero elsewhere, is a Schwartz–Bruhat function (source `sb_of_push`). -/
private theorem mem_schwartzBruhat_of_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {U : Set X} (hU : IsCompact U) {p : X → Y}
    (hp : Continuous p) (ho : IsOpen (p '' U)) {a : X → ℂ} (ha : IsLocallyConstant a)
    {f : Y → ℂ} (h1 : ∀ u ∈ U, f (p u) = a u) (h2 : ∀ y, y ∉ p '' U → f y = 0) :
    f ∈ schwartzBruhatSubmodule Y := by
  refine ⟨fun s => ?_, HasCompactSupport.intro (hU.image hp) h2⟩
  rw [← isClosed_compl_iff, ← Set.preimage_compl]
  generalize sᶜ = t
  have hc : IsClosed (a ⁻¹' t) := by
    rw [← isOpen_compl_iff, ← Set.preimage_compl]
    exact ha _
  have e : f ⁻¹' t = p '' (U ∩ a ⁻¹' t) ∪ ((p '' U)ᶜ ∩ {_y | (0 : ℂ) ∈ t}) := by
    ext y
    by_cases hy : y ∈ p '' U
    · obtain ⟨u, hu, rfl⟩ := hy
      constructor
      · intro h
        exact Or.inl ⟨u, ⟨hu, by rwa [Set.mem_preimage, h1 u hu] at h⟩, rfl⟩
      · rintro (⟨u', ⟨hu', h⟩, e⟩ | ⟨h, -⟩)
        · rw [Set.mem_preimage, ← e, h1 u' hu']
          exact h
        · exact absurd ⟨u, hu, rfl⟩ h
    · rw [Set.mem_preimage, h2 y hy]
      constructor
      · exact fun h => Or.inr ⟨hy, h⟩
      · rintro (⟨u', ⟨hu', -⟩, e⟩ | ⟨-, h⟩)
        · exact absurd ⟨u', hu', e⟩ hy
        · exact h
  rw [e]
  exact ((hU.inter_right hc).image hp).isClosed.union (ho.isClosed_compl.inter isClosed_const)

/-- The average `u ↦ ∫_K φ (κ⁻¹ u θ(κ)) dμ` of a locally constant `φ` over a compact set is
locally constant (source `avg_locConst`). -/
private theorem isLocallyConstant_setIntegral {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] (μ : Measure G) {θ : G → G} (hθ : Continuous θ)
    {K : Set G} (hK : IsCompact K) (hm : MeasurableSet K) {φ : G → ℂ}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant fun u => ∫ κ in K, φ (κ⁻¹ * u * θ κ) ∂μ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have h : ∀ᶠ u in nhds u₀, ∀ κ ∈ K, φ (κ⁻¹ * u * θ κ) = φ (κ⁻¹ * u₀ * θ κ) := by
    refine hK.eventually_forall_of_forall_eventually fun κ _ => ?_
    have h1 := (hφ.comp_continuous (f := fun z : G × G => z.2⁻¹ * z.1 * θ z.2)
      (by fun_prop)).eventually_eq (u₀, κ)
    have h2 := (hφ.comp_continuous (f := fun z : G × G => z.2⁻¹ * u₀ * θ z.2)
      (by fun_prop)).eventually_eq (u₀, κ)
    filter_upwards [h1, h2] with z hz1 hz2
    exact hz1.trans hz2.symm
  filter_upwards [h] with u hu
  exact setIntegral_congr_fun hm hu

/-- Left translation by an element of a subgroup preserves set integrals over it
(source `set_left`). -/
private theorem setIntegral_mul_left_of_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (K : Subgroup G) (hm : MeasurableSet (K : Set G)) (F : G → ℂ)
    {z : G} (hz : z ∈ K) :
    ∫ κ in (K : Set G), F (z * κ) ∂μ = ∫ κ in (K : Set G), F κ ∂μ := by
  rw [← integral_indicator hm, ← integral_indicator hm,
    ← integral_mul_left_eq_self ((K : Set G).indicator F) z]
  congr 1
  funext κ
  by_cases h : κ ∈ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (K.mul_mem hz h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem fun h' => h ((K.mul_mem_cancel_left hz).1 h')]

end Generic


section Spectral

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [Algebra F E] [FiniteDimensional F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E]

/-- **From `GL_n(E)` to `GL_n(F)` near the identity, with an explicit radius** (source
`nearDown`): for `0 < r < ‖l‖`, every Schwartz–Bruhat function `φ` on `GL_n(E)` supported in the
spectral congruence neighbourhood of radius `r ‖l‖` has a concordant Schwartz–Bruhat function `f`
on `GL_n(F)`, namely `f (u^l) = μF(K_F)⁻¹ ∫_K φ (κ⁻¹ u κ^σ) dμE` for `u` in `K_F`
(`K`, `K_F` the congruence neighbourhoods of radius `r` of `GL_n(E)`, `GL_n(F)`) and `f = 0` off
the congruence neighbourhood of radius `r ‖l‖` of `GL_n(F)`. -/
theorem exists_concordant_ordinary_of_support_normCongruence {σ : E ≃ₐ[F] E} {l n : ℕ}
    (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure] {r : ℝ} (hr₀ : 0 < r) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.finiteExtensionNormedField F E
    r < ‖(l : F)‖ → ∀ φ : SchwartzBruhat (GeneralLinear n E),
      Function.support φ ⊆ normCongruence E n (r * ‖(l : F)‖) →
      ∃ f : SchwartzBruhat (GeneralLinear n F), AreConcordant σ l μF μE φ f ∧
        (∀ u ∈ normCongruence F n r, f (u ^ l) =
          (((μF (normCongruence F n r)).toReal⁻¹ : ℝ) : ℂ) *
            ∫ κ in normCongruence E n r,
              φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) ∂μE) ∧
        (∀ γ, γ ∉ normCongruence F n (r * ‖(l : F)‖) → f γ = 0) := by
  classical
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.localNormedField_complete F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let := LocalGalois.finiteExtensionNormedField F E
  let := LocalGalois.finiteExtensionNormedField_ultrametric F E
  let := LocalGalois.finiteExtensionNormedField_properSpace F E
  intro hr φ hφ
  have hl1 : ‖(l : F)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one F l
  have hl0 : 0 < ‖(l : F)‖ := hr₀.trans hr
  have hr1 : r < 1 := hr.trans_le hl1
  have hθ : Continuous fun g : GeneralLinear n E => entrywiseAut σ n g :=
    continuous_entrywiseAut σ n
  let K := normCongruenceSubgroup E n hr₀.le hr1
  have hKo : IsOpen (K : Set (GeneralLinear n E)) := isOpen_normCongruence hr₀
  have hKc : IsCompact (K : Set (GeneralLinear n E)) := isCompact_normCongruence hr₀.le hr1
  have hK : IsTwistedDescentSubgroup F σ l K :=
    isTwistedDescentSubgroup_normCongruence hσ hr₀.le hr1 hr
  have hmemK : ∀ u : GeneralLinear n F, baseChange F E n u ∈ K ↔ u ∈ normCongruence F n r :=
    fun u => baseChange_mem_normCongruence_iff r u
  have hKF : (K.comap (baseChange F E n) : Set (GeneralLinear n F)) = normCongruence F n r := by
    ext γ
    exact hmemK γ
  have hKFo : IsOpen (normCongruence F n r) := isOpen_normCongruence hr₀
  have hKFc : IsCompact (normCongruence F n r) := isCompact_normCongruence hr₀.le hr1
  let A : GeneralLinear n E → ℂ := fun g =>
    ∫ κ in (K : Set (GeneralLinear n E)), φ (κ⁻¹ * g * entrywiseAut σ n κ) ∂μE
  have hA : IsLocallyConstant A :=
    isLocallyConstant_setIntegral μE hθ hKc hKo.measurableSet φ.locallyConstant
  have hAconj : ∀ u κ : GeneralLinear n F, κ ∈ normCongruence F n r →
      A (baseChange F E n (κ⁻¹ * u * κ)) = A (baseChange F E n u) := by
    intro u κ hκ
    simp only [A]
    have hκK : baseChange F E n κ ∈ K := (hmemK κ).mpr hκ
    rw [← setIntegral_mul_left_of_mem μE K hKo.measurableSet
      (fun x => φ (x⁻¹ * baseChange F E n u * entrywiseAut σ n x)) hκK]
    refine setIntegral_congr_fun hKo.measurableSet fun κ' _ => ?_
    simp only [map_mul, map_inv, entrywiseAut_baseChange, mul_inv_rev]
    group
  have hμ0 : (μF (normCongruence F n r)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hKFo.measure_ne_zero μF ⟨1, one_mem_normCongruence hr₀.le⟩,
      hKFc.measure_lt_top.ne⟩
  let c : ℂ := (((μF (normCongruence F n r)).toReal⁻¹ : ℝ) : ℂ)
  let fF : GeneralLinear n F → ℂ := fun γ =>
    if h : ∃ u ∈ normCongruence F n r, u ^ l = γ then c * A (baseChange F E n h.choose) else 0
  have h1 : ∀ u ∈ normCongruence F n r, fF (u ^ l) = c * A (baseChange F E n u) := by
    intro u hu
    have h : ∃ u' ∈ normCongruence F n r, u' ^ l = u ^ l := ⟨u, hu, rfl⟩
    simp only [fF, dite_eq_left h]
    rw [eq_of_pow_eq hr₀.le hr h.choose_spec.1 hu h.choose_spec.2]
  have himage := pow_image_normCongruence (F := F) (n := n) (l := l) hr₀.le hr
  have h2 : ∀ γ, γ ∉ normCongruence F n (r * ‖(l : F)‖) → fF γ = 0 := by
    intro γ hγ
    refine dite_eq_right fun h => hγ ?_
    obtain ⟨u, hu, e⟩ := h
    rw [← himage]
    exact ⟨u, hu, e⟩
  have hSB : fF ∈ schwartzBruhatSubmodule (GeneralLinear n F) := by
    refine mem_schwartzBruhat_of_image hKFc (continuous_pow l) ?_
      (a := fun u => c * A (baseChange F E n u))
      ((hA.comp_continuous (hσ.isClosedEmbedding_baseChange n).continuous).comp
        fun z => c * z) h1 fun γ hγ => h2 γ (by rwa [← himage])
    rw [himage]
    exact isOpen_normCongruence (mul_pos hr₀ hl0)
  let f : SchwartzBruhat (GeneralLinear n F) := ⟨fF, hSB⟩
  refine ⟨f, ?_, h1, h2⟩
  refine areConcordant_of_integral_eq hσ μF μE K hKo hKc hK φ f ?_ ?_ ?_
  · intro g hg
    have hg' : g ∈ normCongruence E n (r * ‖(l : F)‖) := hφ hg
    obtain ⟨κ, hκ, u, hu, e⟩ :=
      exists_twistedConj_baseChange_mul_eq hσ hr₀.le hr (one_mem_normCongruence hr₀.le) hg'
    refine ⟨κ, hκ, u, (hmemK u).mpr hu, ?_⟩
    simpa only [map_one, one_mul] using e
  · intro γ hγ
    by_contra h
    have hγ' : γ ∈ normCongruence F n (r * ‖(l : F)‖) := by
      by_contra h'
      exact hγ (h2 γ h')
    rw [← himage] at hγ'
    obtain ⟨u, hu, e⟩ := hγ'
    exact h ⟨u, (hmemK u).mpr hu, e.symm⟩
  · intro u hu
    have hu' : u ∈ normCongruence F n r := (hmemK u).mp hu
    rw [hKF]
    have hconst : ∀ κ ∈ normCongruence F n r,
        f (κ⁻¹ * u ^ l * κ) = c * A (baseChange F E n u) := by
      intro κ hκ
      have hc : κ⁻¹ * u ^ l * κ = (κ⁻¹ * u * κ) ^ l := by
        have := conj_pow (a := κ⁻¹) (b := u) (i := l)
        rw [inv_inv] at this
        exact this.symm
      have hmem : κ⁻¹ * u * κ ∈ normCongruence F n r :=
        mul_mem_normCongruence hr₀.le hr1.le
          (mul_mem_normCongruence hr₀.le hr1.le (inv_mem_normCongruence hr₀.le hr1 hκ) hu') hκ
      change fF (κ⁻¹ * u ^ l * κ) = _
      rw [hc, h1 _ hmem, hAconj u κ hκ]
    rw [setIntegral_congr_fun hKFo.measurableSet hconst, setIntegral_const, Complex.real_smul,
      measureReal_def]
    simp only [c, ← mul_assoc]
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hμ0), one_mul]


/-- **From `GL_n(F)` to `GL_n(E)` near the identity, with an explicit radius** (source
`nearUp`): for `0 < r < ‖l‖`, every Schwartz–Bruhat function `f` on `GL_n(F)` supported in the
congruence neighbourhood of radius `r ‖l‖` has a concordant Schwartz–Bruhat function `φ` on
`GL_n(E)`, namely `φ (κ⁻¹ u κ^σ) = μE(K)⁻¹ ∫_{K_F} f (κ'⁻¹ u^l κ') dμF` for `κ ∈ K`, `u ∈ K_F`
(`K`, `K_F` the congruence neighbourhoods of radius `r`), and `φ = 0` off these σ-conjugates. -/
theorem exists_concordant_twisted_of_support_normCongruence {σ : E ≃ₐ[F] E} {l n : ℕ}
    (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure] {r : ℝ} (hr₀ : 0 < r) :
    letI := LocalGalois.localNormedField F
    letI := LocalGalois.finiteExtensionNormedField F E
    r < ‖(l : F)‖ → ∀ f : SchwartzBruhat (GeneralLinear n F),
      Function.support f ⊆ normCongruence F n (r * ‖(l : F)‖) →
      ∃ φ : SchwartzBruhat (GeneralLinear n E), AreConcordant σ l μF μE φ f ∧
        (∀ κ ∈ normCongruence E n r, ∀ u ∈ normCongruence F n r,
          φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) =
            (((μE (normCongruence E n r)).toReal⁻¹ : ℝ) : ℂ) *
              ∫ κ' in normCongruence F n r, f (κ'⁻¹ * u ^ l * κ') ∂μF) ∧
        (∀ g, (¬ ∃ κ ∈ normCongruence E n r, ∃ u ∈ normCongruence F n r,
          g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) → φ g = 0) := by
  classical
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.localNormedField_complete F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let := LocalGalois.finiteExtensionNormedField F E
  let := LocalGalois.finiteExtensionNormedField_ultrametric F E
  let := LocalGalois.finiteExtensionNormedField_properSpace F E
  intro hr f hf
  have hl1 : ‖(l : F)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one F l
  have hl0 : 0 < ‖(l : F)‖ := hr₀.trans hr
  have hr1 : r < 1 := hr.trans_le hl1
  have hθ : Continuous fun g : GeneralLinear n E => entrywiseAut σ n g :=
    continuous_entrywiseAut σ n
  have hbc : Continuous (baseChange F E n) := (hσ.isClosedEmbedding_baseChange n).continuous
  let K := normCongruenceSubgroup E n hr₀.le hr1
  let KF := normCongruenceSubgroup F n hr₀.le hr1
  have hKo : IsOpen (K : Set (GeneralLinear n E)) := isOpen_normCongruence hr₀
  have hKc : IsCompact (K : Set (GeneralLinear n E)) := isCompact_normCongruence hr₀.le hr1
  have hK : IsTwistedDescentSubgroup F σ l K :=
    isTwistedDescentSubgroup_normCongruence hσ hr₀.le hr1 hr
  have hmemK : ∀ u : GeneralLinear n F, baseChange F E n u ∈ K ↔ u ∈ normCongruence F n r :=
    fun u => baseChange_mem_normCongruence_iff r u
  have hKF : (K.comap (baseChange F E n) : Set (GeneralLinear n F)) = normCongruence F n r := by
    ext γ
    exact hmemK γ
  have hKFo : IsOpen (normCongruence F n r) := isOpen_normCongruence hr₀
  have hKFc : IsCompact (normCongruence F n r) := isCompact_normCongruence hr₀.le hr1
  have himage := pow_image_normCongruence (F := F) (n := n) (l := l) hr₀.le hr
  let AF : GeneralLinear n F → ℂ := fun γ =>
    ∫ κ in normCongruence F n r, f (κ⁻¹ * γ * id κ) ∂μF
  have hAF : IsLocallyConstant AF :=
    isLocallyConstant_setIntegral μF continuous_id hKFc hKFo.measurableSet f.locallyConstant
  have hAFconj : ∀ γ x : GeneralLinear n F, x ∈ normCongruence F n r →
      AF (x⁻¹ * γ * x) = AF γ := by
    intro γ x hx
    simp only [AF, id]
    rw [show normCongruence F n r = (KF : Set (GeneralLinear n F)) from rfl,
      ← setIntegral_mul_left_of_mem μF KF hKFo.measurableSet
      (fun y => f (y⁻¹ * γ * y)) (show x ∈ KF from hx)]
    refine setIntegral_congr_fun hKFo.measurableSet fun κ _ => ?_
    simp only [mul_inv_rev]
    group
  have hμ0 : (μE (normCongruence E n r)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hKo.measure_ne_zero μE ⟨1, one_mem_normCongruence hr₀.le⟩,
      hKc.measure_lt_top.ne⟩
  let c : ℂ := (((μE (normCongruence E n r)).toReal⁻¹ : ℝ) : ℂ)
  let p : GeneralLinear n E × GeneralLinear n F → GeneralLinear n E := fun z =>
    z.1⁻¹ * baseChange F E n z.2 * entrywiseAut σ n z.1
  have hp : Continuous p :=
    (continuous_fst.inv.mul (hbc.comp continuous_snd)).mul (hθ.comp continuous_fst)
  let U : Set (GeneralLinear n E × GeneralLinear n F) := normCongruence E n r ×ˢ normCongruence F n r
  let a : GeneralLinear n E × GeneralLinear n F → ℂ := fun z => c * AF (z.2 ^ l)
  have wd : ∀ z ∈ U, ∀ z' ∈ U, p z = p z' → a z = a z' := by
    rintro ⟨κ, u⟩ ⟨hκ, hu⟩ ⟨κ', u'⟩ ⟨hκ', hu'⟩ e
    have e1 : (κ * κ'⁻¹)⁻¹ * baseChange F E n u * entrywiseAut σ n (κ * κ'⁻¹) =
        baseChange F E n u' := by
      rw [map_mul, map_inv]
      calc (κ * κ'⁻¹)⁻¹ * baseChange F E n u * (entrywiseAut σ n κ * (entrywiseAut σ n κ')⁻¹)
          = κ' * (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) * (entrywiseAut σ n κ')⁻¹ := by
            group
        _ = κ' * (κ'⁻¹ * baseChange F E n u' * entrywiseAut σ n κ') *
            (entrywiseAut σ n κ')⁻¹ := by
            rw [show κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ =
              κ'⁻¹ * baseChange F E n u' * entrywiseAut σ n κ' from e]
        _ = baseChange F E n u' := by group
    obtain ⟨x, hx⟩ := hK.rational_of_twistedConj u u' ((hmemK u).mpr hu) ((hmemK u').mpr hu')
      (κ * κ'⁻¹) e1
    have hxK : x ∈ normCongruence F n r := by
      rw [← hmemK, hx]
      exact K.mul_mem hκ (K.inv_mem hκ')
    rw [← hx, entrywiseAut_baseChange, ← map_inv, ← map_mul, ← map_mul] at e1
    have e2 := baseChange_injective e1
    change c * AF (u ^ l) = c * AF (u' ^ l)
    have e3 : u' ^ l = x⁻¹ * u ^ l * x := by
      have hc := conj_pow (a := x⁻¹) (b := u) (i := l)
      rw [inv_inv] at hc
      rw [← e2, hc]
    rw [e3, hAFconj _ x hxK]
  let φF : GeneralLinear n E → ℂ := fun g => if h : ∃ z ∈ U, p z = g then a h.choose else 0
  have h1 : ∀ z ∈ U, φF (p z) = a z := fun z hz => by
    have h : ∃ z' ∈ U, p z' = p z := ⟨z, hz, rfl⟩
    simp only [φF, dite_eq_left h]
    exact wd _ h.choose_spec.1 _ hz h.choose_spec.2
  have h2 : ∀ g, g ∉ p '' U → φF g = 0 := fun g h => dite_eq_right h
  have hpU : p '' U = {g : GeneralLinear n E | ∃ κ ∈ normCongruence E n r,
      ∃ u ∈ normCongruence F n r, g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ} := by
    ext g
    constructor
    · rintro ⟨⟨κ, u⟩, ⟨hκ, hu⟩, rfl⟩
      exact ⟨κ, hκ, u, hu, rfl⟩
    · rintro ⟨κ, hκ, u, hu, rfl⟩
      exact ⟨(κ, u), ⟨hκ, hu⟩, rfl⟩
  have ho : IsOpen (p '' U) := by
    rw [hpU]
    exact isOpen_twistedConj_normCongruence hσ hr₀ hr
  have hSB : φF ∈ schwartzBruhatSubmodule (GeneralLinear n E) :=
    mem_schwartzBruhat_of_image (hKc.prod hKFc) hp ho
      ((hAF.comp_continuous (continuous_snd.pow l)).comp fun z => c * z) h1 h2
  let φ : SchwartzBruhat (GeneralLinear n E) := ⟨φF, hSB⟩
  have hφval : ∀ κ ∈ normCongruence E n r, ∀ u ∈ normCongruence F n r,
      φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) = c * AF (u ^ l) :=
    fun κ hκ u hu => h1 (κ, u) ⟨hκ, hu⟩
  refine ⟨φ, ?_, hφval, fun g hg => h2 g (by rwa [hpU])⟩
  refine areConcordant_of_integral_eq hσ μF μE K hKo hKc hK φ f ?_ ?_ ?_
  · intro g hg
    by_contra h
    apply hg
    refine h2 g fun hg' => h ?_
    rw [hpU] at hg'
    obtain ⟨κ, hκ, u, hu, e⟩ := hg'
    exact ⟨κ, hκ, u, (hmemK u).mpr hu, e⟩
  · intro γ hγ
    have hγ' : γ ∈ normCongruence F n (r * ‖(l : F)‖) := hf hγ
    rw [← himage] at hγ'
    obtain ⟨u, hu, e⟩ := hγ'
    exact ⟨u, (hmemK u).mpr hu, e.symm⟩
  · intro u hu
    have hu' : u ∈ normCongruence F n r := (hmemK u).mp hu
    rw [hKF, setIntegral_congr_fun hKo.measurableSet (fun κ hκ => hφval κ hκ u hu'),
      setIntegral_const, Complex.real_smul, measureReal_def, coe_normCongruenceSubgroup]
    simp only [c, ← mul_assoc]
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hμ0), one_mul]
    rfl

end Spectral


/-- **Matching near the identity** for a cyclic extension of fields: the neighbourhoods are the
spectral congruence neighbourhoods of radius `r ‖l‖` with `r = ‖l‖ / 2`. -/
theorem nearIdentityMatching : NearIdentityMatchingStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _
  let : FiniteDimensional F E := hσ.1
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_ultrametric F
  let := LocalGalois.finiteExtensionNormedField F E
  let := LocalGalois.finiteExtensionNormedField_ultrametric F E
  have hl0 : 0 < ‖(l : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hσ.pos.ne')
  have hr₀ : 0 < ‖(l : F)‖ / 2 := half_pos hl0
  have hr : ‖(l : F)‖ / 2 < ‖(l : F)‖ := half_lt_self hl0
  have hs : 0 < ‖(l : F)‖ / 2 * ‖(l : F)‖ := mul_pos hr₀ hl0
  refine ⟨⟨normCongruence E n (‖(l : F)‖ / 2 * ‖(l : F)‖),
    (isOpen_normCongruence hs).mem_nhds (one_mem_normCongruence hs.le), fun φ hφ => ?_⟩,
    ⟨normCongruence F n (‖(l : F)‖ / 2 * ‖(l : F)‖),
    (isOpen_normCongruence hs).mem_nhds (one_mem_normCongruence hs.le), fun f hf => ?_⟩⟩
  · obtain ⟨f, hf, -⟩ :=
      exists_concordant_ordinary_of_support_normCongruence hσ μF μE hr₀ hr φ hφ
    exact ⟨f, hf⟩
  · obtain ⟨φ, hφ, -⟩ :=
      exists_concordant_twisted_of_support_normCongruence hσ μF μE hr₀ hr f hf
    exact ⟨φ, hφ⟩

end Langlands.BaseChange
