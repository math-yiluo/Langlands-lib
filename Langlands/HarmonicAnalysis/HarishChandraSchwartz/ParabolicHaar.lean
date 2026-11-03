import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntegration
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure

/-! # The Haar measure `dm du` of `P = M U` and the open-cell formula in coordinates

Waldspurger 2003, I.1 (2): the measure `dm du` on `P = M U`, in the coordinates
`(m, u) ↦ m u`, is a left Haar measure of `P`, and right translation by `m₀ u₀` multiplies it
by `δ_P(m₀)`. With the open-cell formula of `OpenCellIntegration` this gives the second
formula of (2) in Waldspurger's coordinates,
`∫_G f = γ(P)⁻¹ ∫_{U × M × Ū} f(u m ū) δ_P(m)⁻¹ dū dm du`, and the value
`γ(P) = ∫_Ū δ_P(m_P(ū)) dū`. This module proves these facts for abstract data.
-/

noncomputable section

open scoped ENNReal NNReal Pointwise
open MeasureTheory Measure Topology

namespace Langlands.HarishChandraSchwartz

section Coordinates

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M U P : Subgroup G} (hP : ∀ x : M × U, leviUnipotentMul x ∈ P)

/-- The coordinates `(m, u) ↦ m u` of `P = M U`, as a map into `P`. -/
def leviUnipotentCoord (x : M × U) : P :=
  ⟨leviUnipotentMul x, hP x⟩

theorem continuous_leviUnipotentCoord : Continuous (leviUnipotentCoord hP) :=
  continuous_leviUnipotentMul.subtype_mk _

end Coordinates

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {M U P : Subgroup G} [SecondCountableTopology U]
  (hMU : M ≤ Subgroup.normalizer (U : Set G)) (hP : ∀ x : M × U, leviUnipotentMul x ∈ P)
  (μM : Measure M) [SFinite μM] [μM.IsMulLeftInvariant]
  (μU : Measure U) [SFinite μU] [μU.IsMulLeftInvariant]

/-- The measure `dm du` on `P`: the image of `μ_M × μ_U` under `(m, u) ↦ m u`. -/
def leviUnipotentMeasure : Measure P :=
  (μM.prod μU).map (leviUnipotentCoord hP)

include hMU in
/-- If `(m, u) ↦ m u` maps `M × U` onto `P`, then `dm du` is left invariant on `P`. -/
theorem leviUnipotentMeasure_isMulLeftInvariant (hsurj : Function.Surjective (leviUnipotentCoord hP)) :
    (leviUnipotentMeasure hP μM μU).IsMulLeftInvariant := ⟨fun p₀ => by
  obtain ⟨x₀, hx₀⟩ := hsurj p₀⁻¹
  have hcomp : (fun p => p₀ * p) ∘ leviUnipotentCoord hP =
      leviUnipotentCoord hP ∘ leviUnipotentShift hMU x₀ := by
    funext x
    apply Subtype.ext
    have h0 : (leviUnipotentMul x₀ : G) = ((p₀⁻¹ : P) : G) := congrArg Subtype.val hx₀
    simp only [Function.comp, leviUnipotentCoord, Subgroup.coe_mul]
    rw [leviUnipotentMul_shift hMU x₀ x, h0]
    simp
  unfold leviUnipotentMeasure
  rw [Measure.map_map (measurable_const_mul p₀) (continuous_leviUnipotentCoord hP).measurable, hcomp,
    ← Measure.map_map (continuous_leviUnipotentCoord hP).measurable
      (measurePreserving_leviUnipotentShift (μM := μM) (μU := μU) hMU x₀).measurable,
    (measurePreserving_leviUnipotentShift (μM := μM) (μU := μU) hMU x₀).map_eq]⟩

omit [μM.IsMulLeftInvariant] [μU.IsMulLeftInvariant] in
include hMU in
/-- Right translation by `m₀ u₀` multiplies `dm du` by `δ(m₀)`, when `μ_M` and `μ_U` are also
right invariant and `μ_U(m S m⁻¹) = δ(m) μ_U(S)` (`IsConjModulus`). -/
theorem map_mul_right_leviUnipotentMeasure [μM.IsMulRightInvariant] [μU.IsMulRightInvariant]
    {δ : M →* ℝ≥0ˣ} (hν : IsConjModulus hMU μU δ) (x₀ : M × U) :
    (leviUnipotentMeasure hP μM μU).map (· * leviUnipotentCoord hP x₀) =
      (δ x₀.1 : ℝ≥0) • leviUnipotentMeasure hP μM μU := by
  set τ : M × U → M × U :=
    Prod.map (· * x₀.1) (fun u => conjUnipotent hMU x₀.1⁻¹ u * x₀.2) with hτdef
  have hg : Measurable fun u => conjUnipotent hMU x₀.1⁻¹ u * x₀.2 :=
    (measurable_mul_const x₀.2).comp (continuous_conjUnipotent hMU _).measurable
  have hτ : Measurable τ := (measurable_mul_const x₀.1).prodMap hg
  have hcomp : (· * leviUnipotentCoord hP x₀) ∘ leviUnipotentCoord hP = leviUnipotentCoord hP ∘ τ := by
    funext x
    apply Subtype.ext
    simp only [Function.comp, leviUnipotentCoord, leviUnipotentMul, τ, Prod.map, conjUnipotent,
      Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  have hU : μU.map (fun u => conjUnipotent hMU x₀.1⁻¹ u * x₀.2) = (δ x₀.1 : ℝ≥0) • μU := by
    have hfun : (fun u => conjUnipotent hMU x₀.1⁻¹ u * x₀.2) =
        (· * x₀.2) ∘ conjUnipotent hMU x₀.1⁻¹ := rfl
    rw [hfun, ← Measure.map_map (measurable_mul_const x₀.2)
      (continuous_conjUnipotent hMU _).measurable, hν, Measure.map_smul, map_mul_right_eq_self,
      map_inv, Units.val_inv_eq_inv_val, inv_inv]
    exact (measurable_mul_const x₀.2).aemeasurable
  unfold leviUnipotentMeasure
  rw [Measure.map_map (measurable_mul_const _) (continuous_leviUnipotentCoord hP).measurable, hcomp,
    ← Measure.map_map (continuous_leviUnipotentCoord hP).measurable hτ, hτdef,
    ← Measure.map_prod_map μM μU (measurable_mul_const _) hg, map_mul_right_eq_self, hU,
    Measure.prod_smul_right, Measure.map_smul]
  exact (continuous_leviUnipotentCoord hP).measurable.aemeasurable

omit [μM.IsMulLeftInvariant] [μU.IsMulLeftInvariant] in
include hMU in
/-- The right translation law in the form `μ_P((· p₀)⁻¹ S) = δ(m₀) μ_P(S)` for `p₀ = m₀ u₀`. -/
theorem leviUnipotentMeasure_preimage_mul_right [μM.IsMulRightInvariant] [μU.IsMulRightInvariant]
    {δ : M →* ℝ≥0ˣ} (hν : IsConjModulus hMU μU δ) (x₀ : M × U) {S : Set P}
    (hS : MeasurableSet S) :
    leviUnipotentMeasure hP μM μU ((fun p => p * leviUnipotentCoord hP x₀) ⁻¹' S) =
      ((δ x₀.1 : ℝ≥0) : ℝ≥0∞) * leviUnipotentMeasure hP μM μU S := by
  rw [← Measure.map_apply (measurable_mul_const _) hS,
    map_mul_right_leviUnipotentMeasure hMU hP μM μU hν x₀, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]

omit [SFinite μM] [μM.IsMulLeftInvariant] [μU.IsMulLeftInvariant] in
/-- If `m u ∈ K ↔ m ∈ K ∧ u ∈ K`, then `μ_P(P ∩ K) = μ_M(M ∩ K) μ_U(U ∩ K)`. -/
theorem leviUnipotentMeasure_inter {K : Subgroup G} (hK : MeasurableSet (K : Set G))
    (hPK : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K) :
    leviUnipotentMeasure hP μM μU {p : P | (p : G) ∈ K} =
      μM {m : M | (m : G) ∈ K} * μU {u : U | (u : G) ∈ K} := by
  have hKP : MeasurableSet {p : P | (p : G) ∈ K} := measurable_subtype_coe hK
  unfold leviUnipotentMeasure
  rw [Measure.map_apply (continuous_leviUnipotentCoord hP).measurable hKP]
  have hpre : leviUnipotentCoord hP ⁻¹' {p : P | (p : G) ∈ K} =
      {m : M | (m : G) ∈ K} ×ˢ {u : U | (u : G) ∈ K} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, leviUnipotentCoord, leviUnipotentMul,
      Set.mem_prod]
    exact hPK x.1 x.2
  rw [hpre, Measure.prod_prod]

omit [μM.IsMulLeftInvariant] [μU.IsMulLeftInvariant] in
include hMU in
/-- If `(m, u) ↦ m u` is a homeomorphism of `M × U` onto `P` and `μ_M`, `μ_U` are Haar measures,
then `dm du` is a Haar measure of `P`. -/
theorem leviUnipotentMeasure_isHaarMeasure [IsHaarMeasure μM] [IsHaarMeasure μU]
    (hhomeo : IsHomeomorph (leviUnipotentCoord hP)) :
    (leviUnipotentMeasure hP μM μU).IsHaarMeasure := by
  set e := hhomeo.homeomorph (leviUnipotentCoord hP)
  have he : (e.toMeasurableEquiv : M × U → P) = leviUnipotentCoord hP := rfl
  have hmap : leviUnipotentMeasure hP μM μU = (μM.prod μU).map e.toMeasurableEquiv := by
    rw [he]; rfl
  have hinv := leviUnipotentMeasure_isMulLeftInvariant hMU hP μM μU hhomeo.bijective.2
  exact
    { lt_top_of_isCompact := fun S hS => by
        rw [hmap, MeasurableEquiv.map_apply]
        exact (e.isCompact_preimage.mpr hS).measure_lt_top
      map_mul_left_eq_self := hinv.map_mul_left_eq_self
      open_pos := fun S hS hne => by
        rw [hmap, MeasurableEquiv.map_apply]
        refine (hS.preimage e.continuous).measure_ne_zero _ ?_
        obtain ⟨p, hp⟩ := hne
        exact ⟨e.symm p, by simpa using hp⟩ }

omit [SecondCountableTopology U] [μM.IsMulLeftInvariant]
  [SFinite μM] [SFinite μU] [μU.IsMulLeftInvariant] in
/-- Waldspurger's order of the coordinates: if `μ_U(m S m⁻¹) = δ(m) μ_U(S)`, then
`∫_M ∫_U Φ(m u) du dm = ∫_M δ(m)⁻¹ ∫_U Φ(u m) du dm` for every `Φ ≥ 0`. -/
theorem lintegral_levi_unipotent_eq {δ : M →* ℝ≥0ˣ} (hν : IsConjModulus hMU μU δ)
    (Φ : G → ℝ≥0∞) :
    ∫⁻ m, ∫⁻ u, Φ ((m : G) * u) ∂μU ∂μM =
      ∫⁻ m, (((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ u, Φ ((u : G) * m) ∂μU ∂μM := by
  refine lintegral_congr fun m => ?_
  rw [← hν.lintegral_comp m (fun v : U => Φ ((v : G) * m))]
  refine lintegral_congr fun u => ?_
  simp only [conjUnipotent]
  congr 1
  group

omit [μM.IsMulLeftInvariant] [μU.IsMulLeftInvariant] in
include hMU in
/-- The value of `γ` for `dm du`: if `μ_M`, `μ_U` are right invariant, `IsConjModulus` holds,
`m u ∈ K ↔ m ∈ K ∧ u ∈ K`, `μ_M(M ∩ K) = μ_U(U ∩ K) = 1`, and `ℓ(v) = (m(v), u(v))` gives the
`P`-component `m(v) u(v)` of `v⁻¹` in `G = P K`, then `γ = ∫_V δ(m(v)) dμ_V`. For Waldspurger's
data, with `ū = v⁻¹`, this is `γ(P) = ∫_Ū δ_P(m_P(ū)) dū`. -/
theorem openCellConstant_leviUnipotentMeasure {V : Subgroup G} (μV : Measure V)
    (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    [μM.IsMulRightInvariant] [μU.IsMulRightInvariant] {δ : M →* ℝ≥0ˣ}
    (hν : IsConjModulus hMU μU δ) {K : Subgroup G} (hK : MeasurableSet (K : Set G))
    (hPK : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (hUK : μU {u : U | (u : G) ∈ K} = 1)
    (ℓ : V → M × U) (hℓ : ∀ v : V, (leviUnipotentMul (ℓ v))⁻¹ * (v : G)⁻¹ ∈ K) :
    openCellConstant (leviUnipotentMeasure hP μM μU) μV K =
      ∫⁻ v, ((δ (ℓ v).1 : ℝ≥0) : ℝ≥0∞) ∂μV := by
  set e := hhomeo.homeomorph (leviUnipotentCoord hP)
  have he : ∀ x, e x = leviUnipotentCoord hP x := fun _ => rfl
  rw [openCellConstant_eq_lintegral (leviUnipotentMeasure hP μM μU) μV
    (d := fun p => ((δ (e.symm p).1 : ℝ≥0) : ℝ≥0∞))
    (fun p₀ S hS => by
      have h := leviUnipotentMeasure_preimage_mul_right hMU hP μM μU hν (e.symm p₀) hS
      rwa [← he, e.apply_symm_apply] at h)
    (measurable_subtype_coe hK)
    (by rw [leviUnipotentMeasure_inter hP μM μU hK hPK, hMK, hUK, one_mul])
    (fun v => leviUnipotentCoord hP (ℓ v)) hℓ]
  refine lintegral_congr fun v => ?_
  rw [← he, e.symm_apply_apply]

end Haar

section OpenCell

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {M U P V : Subgroup G} [SecondCountableTopology U]
  (hMU : M ≤ Subgroup.normalizer (U : Set G)) (hP : ∀ x : M × U, leviUnipotentMul x ∈ P)
  [LocallyCompactSpace P] [LocallyCompactSpace V] [SecondCountableTopology P]
  [SecondCountableTopology V]
  (μ : Measure G) [IsHaarMeasure μ] [μ.IsMulRightInvariant]
  (μM : Measure M) [IsHaarMeasure μM] [SFinite μM]
  (μU : Measure U) [IsHaarMeasure μU] [SFinite μU] (μV : Measure V) [IsHaarMeasure μV]

include hMU in
/-- Waldspurger I.1 (2), second formula, in the coordinates `(m, u, v) ↦ m u v⁻¹`: under the
hypotheses of `lintegral_eq_openCellConstant_inv_mul`, with `dm du` as the Haar measure of `P`
(`(m, u) ↦ m u` a homeomorphism `M × U ≅ P`),
`∫_G F dμ = μ(K) γ⁻¹ ∫_M ∫_U ∫_V F(m u v⁻¹) dμ_V dμ_U dμ_M`. -/
theorem lintegral_eq_openCell_levi_unipotent (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F g ∂μ = μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹ *
      ∫⁻ m, ∫⁻ u, ∫⁻ v, F ((m : G) * u * (v : G)⁻¹) ∂μV ∂μU ∂μM := by
  have := leviUnipotentMeasure_isHaarMeasure hMU hP μM μU hhomeo
  obtain ⟨-, -, h⟩ := lintegral_eq_openCellConstant_inv_mul μ (leviUnipotentMeasure hP μM μU) μV
    hι hnull hK hK0 hKtop
  rw [h F hF]
  congr 1
  have hφ : Measurable fun p : P => ∫⁻ v, F ((p : G) * (v : G)⁻¹) ∂μV := by
    have : Measurable fun x : P × V => F ((x.1 : G) * (x.2 : G)⁻¹) :=
      hF.comp ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd).inv).measurable
    exact this.lintegral_prod_right'
  unfold leviUnipotentMeasure
  rw [lintegral_map hφ (continuous_leviUnipotentCoord hP).measurable,
    lintegral_prod (fun a : M × U => ∫⁻ v, F (((leviUnipotentCoord hP a : P) : G) * (v : G)⁻¹) ∂μV)
      (hφ.comp (continuous_leviUnipotentCoord hP).measurable).aemeasurable]
  rfl

/-- The open-cell coordinates `((m, u), v) ↦ m u v⁻¹` of `G`. -/
def openCellCoord (x : (M × U) × V) : G :=
  (x.1.1 : G) * x.1.2 * (x.2 : G)⁻¹

include hMU in
/-- The open-cell formula as an identity of measures: `μ = μ(K) γ⁻¹ · (dm du dv)` pushed forward
by `((m, u), v) ↦ m u v⁻¹`, under the hypotheses of `lintegral_eq_openCell_levi_unipotent`.
Integrals of complex functions can be computed from it by `integral_map`. -/
theorem eq_smul_map_openCellCoord (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤) :
    μ = (μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹) •
      ((μM.prod μU).prod μV).map (openCellCoord (M := M) (U := U) (V := V)) := by
  have hφ : Measurable (openCellCoord (M := M) (U := U) (V := V)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd).inv).measurable
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_eq_openCell_levi_unipotent hMU hP μ μM μU μV hhomeo hι hnull hK hK0 hKtop F hF,
    lintegral_smul_measure, lintegral_map hF hφ, smul_eq_mul,
    lintegral_prod (fun z : (M × U) × V => F (openCellCoord z)) (hF.comp hφ).aemeasurable,
    lintegral_prod (fun x : M × U => ∫⁻ v, F (openCellCoord (x, v)) ∂μV)
      (hF.comp hφ).lintegral_prod_right'.aemeasurable]
  rfl

include hMU in
/-- The measure of a subgroup with an open-cell factorization (Waldspurger's
`mes(H) = γ(P)⁻¹ mes(U ∩ H) mes(M ∩ H) mes(Ū ∩ H)` in the proof of Remark (3)): if
`m u v⁻¹ ∈ H ↔ m ∈ H ∧ u ∈ H ∧ v ∈ H` for `m ∈ M`, `u ∈ U`, `v ∈ V`, then
`μ(H) = μ(K) γ⁻¹ μ_M(M ∩ H) μ_U(U ∩ H) μ_V(V ∩ H)`. -/
theorem measure_eq_of_openCell_factor (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤)
    {H : Subgroup G} (hH : MeasurableSet (H : Set G))
    (hHf : ∀ (m : M) (u : U) (v : V),
      (m : G) * u * (v : G)⁻¹ ∈ H ↔ (m : G) ∈ H ∧ (u : G) ∈ H ∧ (v : G) ∈ H) :
    μ H = μ K * (openCellConstant (leviUnipotentMeasure hP μM μU) μV K)⁻¹ *
      (μM {m : M | (m : G) ∈ H} * (μU {u : U | (u : G) ∈ H} * μV {v : V | (v : G) ∈ H})) := by
  have hm : Measurable ((H : Set G).indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hH
  have h := lintegral_eq_openCell_levi_unipotent hMU hP μ μM μU μV hhomeo hι hnull hK hK0 hKtop
    _ hm
  rw [lintegral_indicator_one hH] at h
  rw [h]
  congr 1
  have hMH : MeasurableSet {m : M | (m : G) ∈ H} := measurable_subtype_coe hH
  have hUH : MeasurableSet {u : U | (u : G) ∈ H} := measurable_subtype_coe hH
  have hVH : MeasurableSet {v : V | (v : G) ∈ H} := measurable_subtype_coe hH
  have hpt : ∀ (m : M) (u : U) (v : V), (H : Set G).indicator (1 : G → ℝ≥0∞) ((m : G) * u * (v : G)⁻¹) =
      {m : M | (m : G) ∈ H}.indicator 1 m *
        ({u : U | (u : G) ∈ H}.indicator 1 u * {v : V | (v : G) ∈ H}.indicator 1 v) := by
    intro m u v
    by_cases hmH : (m : G) ∈ H <;> by_cases huH : (u : G) ∈ H <;> by_cases hvH : (v : G) ∈ H <;>
      simp [Set.indicator, hHf, hmH, huH, hvH]
  set A : M → ℝ≥0∞ := {m : M | (m : G) ∈ H}.indicator 1
  set B : U → ℝ≥0∞ := {u : U | (u : G) ∈ H}.indicator 1
  set C : V → ℝ≥0∞ := {v : V | (v : G) ∈ H}.indicator 1
  have hA : Measurable A := measurable_one.indicator hMH
  have hB : Measurable B := measurable_one.indicator hUH
  have hC : Measurable C := measurable_one.indicator hVH
  calc ∫⁻ m, ∫⁻ u, ∫⁻ v, (H : Set G).indicator 1 ((m : G) * u * (v : G)⁻¹) ∂μV ∂μU ∂μM
      = ∫⁻ m, ∫⁻ u, A m * (B u * μV {v : V | (v : G) ∈ H}) ∂μU ∂μM := by
        refine lintegral_congr fun m => lintegral_congr fun u => ?_
        simp_rw [hpt]
        rw [lintegral_const_mul _ (hC.const_mul _), lintegral_const_mul _ hC,
          lintegral_indicator_one hVH]
    _ = ∫⁻ m, A m * (μU {u : U | (u : G) ∈ H} * μV {v : V | (v : G) ∈ H}) ∂μM := by
        refine lintegral_congr fun m => ?_
        rw [lintegral_const_mul _ (hB.mul_const _), lintegral_mul_const _ hB,
          lintegral_indicator_one hUH]
    _ = _ := by
        rw [lintegral_mul_const _ hA, lintegral_indicator_one hMH]

include hMU in
/-- Waldspurger's expression of `γ(P)` in the proof of Remark (3): for a measurable subgroup
`H ≤ K` of finite index with the open-cell factorization of `measure_eq_of_openCell_factor`,
`γ = [K : H] μ_M(M ∩ H) μ_U(U ∩ H) μ_V(V ∩ H)`. With `μ_X(X ∩ K) = 1` each factor
`μ_X(X ∩ H)` is `[X ∩ K : X ∩ H]⁻¹` (`measure_eq_inv_relIndex`). -/
theorem openCellConstant_eq_relIndex_mul (hhomeo : IsHomeomorph (leviUnipotentCoord hP))
    (hι : IsOpenEmbedding (openCellMap (P := P) (V := V)))
    (hnull : μ (Set.range (openCellMap (P := P) (V := V)))ᶜ = 0)
    {K : Subgroup G} (hK : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤)
    {H : Subgroup G} (hH : MeasurableSet (H : Set G)) (hHK : H ≤ K) (hKH : H.relIndex K ≠ 0)
    (hHf : ∀ (m : M) (u : U) (v : V),
      (m : G) * u * (v : G)⁻¹ ∈ H ↔ (m : G) ∈ H ∧ (u : G) ∈ H ∧ (v : G) ∈ H) :
    openCellConstant (leviUnipotentMeasure hP μM μU) μV K =
      (H.relIndex K : ℝ≥0∞) *
        (μM {m : M | (m : G) ∈ H} * (μU {u : U | (u : G) ∈ H} * μV {v : V | (v : G) ∈ H})) := by
  have := leviUnipotentMeasure_isHaarMeasure hMU hP μM μU hhomeo
  obtain ⟨hγ0, hγtop, -⟩ := lintegral_eq_openCellConstant_inv_mul μ
    (leviUnipotentMeasure hP μM μU) μV hι hnull hK hK0 hKtop
  set γ := openCellConstant (leviUnipotentMeasure hP μM μU) μV K
  set X := μM {m : M | (m : G) ∈ H} * (μU {u : U | (u : G) ∈ H} * μV {v : V | (v : G) ∈ H})
  have hA := measure_eq_of_openCell_factor hMU hP μ μM μU μV hhomeo hι hnull hK hK0 hKtop hH hHf
  have hKeq := measure_eq_relIndex_mul μ hHK hH hKH
  have hH0 : μ H ≠ 0 := by
    intro h; rw [h, mul_zero] at hKeq; exact hK0 hKeq
  have hHtop : μ H ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono hHK)
  have h1 : μ H * 1 = μ H * ((H.relIndex K : ℝ≥0∞) * γ⁻¹ * X) := by
    rw [mul_one]
    calc μ H = μ K * γ⁻¹ * X := hA
      _ = (H.relIndex K : ℝ≥0∞) * μ H * γ⁻¹ * X := by rw [hKeq]
      _ = μ H * ((H.relIndex K : ℝ≥0∞) * γ⁻¹ * X) := by ring
  have h2 := (ENNReal.mul_right_inj hH0 hHtop).mp h1
  calc γ = γ * 1 := (mul_one γ).symm
    _ = γ * ((H.relIndex K : ℝ≥0∞) * γ⁻¹ * X) := by rw [h2]
    _ = (H.relIndex K : ℝ≥0∞) * X * (γ * γ⁻¹) := by ring
    _ = (H.relIndex K : ℝ≥0∞) * X := by rw [ENNReal.mul_inv_cancel hγ0 hγtop, mul_one]

end OpenCell

section Index

variable {X : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
  [ν.IsMulLeftInvariant]

/-- For measurable `Z ≤ Y` of finite index with `ν(Y) = 1`: `ν(Z) = [Y : Z]⁻¹` (Waldspurger's
`mes(U ∩ H) = [U ∩ K : U ∩ H]⁻¹`). -/
theorem measure_eq_inv_relIndex {Z Y : Subgroup X} (hZY : Z ≤ Y)
    (hZ : MeasurableSet (Z : Set X)) (hfin : Z.relIndex Y ≠ 0) (hY : ν Y = 1) :
    ν Z = ((Z.relIndex Y : ℝ≥0∞))⁻¹ := by
  have h := measure_eq_relIndex_mul ν hZY hZ hfin
  rw [hY] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

end Index

end Langlands.HarishChandraSchwartz
