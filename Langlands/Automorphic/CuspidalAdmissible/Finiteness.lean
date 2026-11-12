import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Global.ArchimedeanConvolution

/-! # Finite dimension of reproduced cuspidal vectors with a central law -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Topology NumberField
open scoped Pointwise

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Automorphic.CuspidalL2 ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local instance cuspidalAdmAddCommGroupRationalInvariant :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmAddCommGroupContinuousRational :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmAddCommGroupFiniteSmoothRational :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmAddCommGroupAutomorphicForms :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalAdmAddCommGroupStableAutomorphic :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmAddCommGroupSpace : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F n) in
/-- The central archimedean element `e^t · 1`, the same real scalar at every infinite place. -/
def centralTorus (t : ℝ) : AdelicGL F n :=
  AdelicGL.ofInfinite F n (torInf F n fun _ => t)

variable (F n) in
theorem centralTorus_commute (t : ℝ) (g : AdelicGL F n) :
    centralTorus F n t * g = g * centralTorus F n t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralTorus, ofInfinite_torInf_val]
  have : (Matrix.diagonal fun _ : Fin n => realScale F (Real.exp t)) =
      Matrix.scalar (Fin n) (realScale F (Real.exp t)) := rfl
  rw [this]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

variable (F n) in
theorem absDet_centralTorus (t : ℝ) :
    absDet F n (centralTorus F n t) = Real.exp (n * t) ^ Module.finrank ℚ F := by
  rw [centralTorus, absDet_ofInfinite_torInf]
  simp

/-- The weight `‖f(g)‖ · |det g|^{-c}`. -/
def weight (c : ℝ) (f : S.Space) (g : AdelicGL F n) : ℝ :=
  ‖evaluate F n (S.toContinuous f) g‖ * absDet F n g ^ (-c)

theorem weight_nonneg (c : ℝ) (f : S.Space) (g : AdelicGL F n) : 0 ≤ S.weight c f g :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (absDet_pos F n g).le _)

theorem norm_eq_weight_mul (c : ℝ) (f : S.Space) (g : AdelicGL F n) :
    ‖evaluate F n (S.toContinuous f) g‖ = S.weight c f g * absDet F n g ^ c := by
  rw [weight, mul_assoc, ← Real.rpow_add (absDet_pos F n g), neg_add_cancel, Real.rpow_zero,
    mul_one]

theorem weight_rational (c : ℝ) (f : S.Space) (γ : RationalGL F n) (g : AdelicGL F n) :
    S.weight c f (AdelicGL.rational F n γ * g) = S.weight c f g := by
  rw [weight, weight, evaluate_rational, absDet_rational_mul]


/-! ### Deep cusp absorption -/

variable (F n) in
/-- **Deep cusp absorption.** Deep in the cusp along a maximal block, a left block-unipotent
translate of `torInf x * q` (`q` in a compact set) equals, up to a rational left translation and
a right translation by the open subgroup `L`, a right archimedean translate of `torInf x * q` by
an element of a prescribed open neighbourhood `U` of `1`. -/
theorem exists_deep_absorption {a b : ℕ} (h : a + b = n)
    (L : Subgroup (FiniteAdelicGL F n)) (hL : IsOpen (L : Set (FiniteAdelicGL F n)))
    {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) {U : Set (InfiniteAdelicGL F n)}
    (hU : IsOpen U) (hU1 : (1 : InfiniteAdelicGL F n) ∈ U) :
    ∃ ℓ₀ : ℝ, ∀ (x : Fin n → ℝ) (ℓ : ℝ), ℓ₀ ≤ ℓ →
      (∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
        x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
      ∀ q ∈ Q, ∀ Y : Matrix (Fin a) (Fin b) (Adeles F),
        ∃ (γ : RationalGL F n) (u : InfiniteAdelicGL F n) (l : FiniteAdelicGL F n),
          u ∈ U ∧ l ∈ L ∧
          GeneralLinear.blockUnipotent h Y * (AdelicGL.ofInfinite F n (torInf F n x) * q) =
            AdelicGL.rational F n γ * (AdelicGL.ofInfinite F n (torInf F n x) * q *
              AdelicGL.ofInfinite F n u) * AdelicGL.ofFinite F n l := by
  have hQf : IsCompact (AdelicGL.finite F n '' Q) :=
    hQ.image (map_continuous (AdelicGL.finite F n))
  have hQi : IsCompact (AdelicGL.infinite F n '' Q) :=
    hQ.image (map_continuous (AdelicGL.infinite F n))
  obtain ⟨δ, hδ, hδL⟩ := exists_nsmul_conj_blockUnipotent_mem F n h L hL hQf
  set D : Set (InfiniteAdeles F) :=
    (fun z => (δ : InfiniteAdeles F) * z) '' archimedeanFundamentalSet F with hDdef
  have hD : IsCompact D :=
    (isCompact_archimedeanFundamentalSet F).image (continuous_const.mul continuous_id)
  set 𝒲 := scaledBlockSet F (a := a) (b := b) D with h𝒲def
  have h𝒲 : IsCompact 𝒲 := isCompact_scaledBlockSet hD
  -- The conjugated rescaled unipotent, as a continuous function of the scale.
  set Ψ : ℝ × (Matrix (Fin a) (Fin b) (InfiniteAdeles F) × InfiniteAdelicGL F n) →
      InfiniteAdelicGL F n := fun p =>
    p.2.2⁻¹ * GeneralLinear.blockUnipotent h
      (PositiveRealIdeles.infiniteRealEmbedding F p.1 • p.2.1) * p.2.2 with hΨdef
  have hΨ : Continuous Ψ :=
    ((continuous_snd.comp continuous_snd).inv.mul ((GeneralLinear.continuous_blockUnipotent h).comp
      (((PositiveRealIdeles.continuous_infiniteRealEmbedding F).comp continuous_fst).smul
        (continuous_fst.comp continuous_snd)))).mul (continuous_snd.comp continuous_snd)
  have hsub : ({0} : Set ℝ) ×ˢ (𝒲 ×ˢ (AdelicGL.infinite F n '' Q)) ⊆ Ψ ⁻¹' U := by
    rintro ⟨s, Z, k⟩ ⟨hs, -⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simp only [Set.mem_preimage, hΨdef, map_zero, zero_smul, GeneralLinear.blockUnipotent_zero,
      mul_one, inv_mul_cancel]
    exact hU1
  obtain ⟨u₀, v₀, hu₀, -, h0u₀, htv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (h𝒲.prod hQi) (hU.preimage hΨ) hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu₀ 0 (h0u₀ rfl)
  refine ⟨-Real.log (ε / 2), fun x ℓ hℓ hgap q hq Y => ?_⟩
  set e := finSumFinEquiv.trans (finCongr h) with he
  set qi := AdelicGL.infinite F n q with hqi
  set qf := AdelicGL.finite F n q with hqf
  have hq_dec : q = AdelicGL.ofInfinite F n qi * AdelicGL.ofFinite F n qf :=
    AdelicGL.eq_ofInfinite_mul_ofFinite F n q
  obtain ⟨ξ, W, hW, rfl⟩ := exists_matrix_decomposition F hδ Y
  set Wi : Matrix (Fin a) (Fin b) (InfiniteAdeles F) :=
    ((δ : Adeles F) • W).map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)) with hWi
  set Wf : Matrix (Fin a) (Fin b) (FiniteAdeles F) :=
    ((δ : Adeles F) • W).map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeles F)) with hWf
  have hWfδ : Wf = δ • W.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeles F)) := by
    refine Matrix.ext fun p r => ?_
    change ((δ : Adeles F) * W p r).2 = δ • (W p r).2
    rw [Prod.snd_mul, Prod.snd_natCast, nsmul_eq_mul]
  have hWiD : ∀ p r, Wi p r ∈ D := fun p r => ⟨(W p r).1, (hW p r).1, by
    change (δ : InfiniteAdeles F) * (W p r).1 = ((δ : Adeles F) * W p r).1
    rw [Prod.fst_mul, Prod.fst_natCast]⟩
  have hLmem : qf⁻¹ * GeneralLinear.blockUnipotent h Wf * qf ∈ L := by
    rw [hWfδ]
    exact hδL _ (fun p r => (hW p r).2) qf ⟨q, hq, rfl⟩
  set Y' : Matrix (Fin a) (Fin b) (InfiniteAdeles F) := Matrix.of fun p r =>
    PositiveRealIdeles.infiniteRealEmbedding F
      (Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p)))) * Wi p r with hY'
  have htor : GeneralLinear.blockUnipotent h Wi * torInf F n x =
      torInf F n x * GeneralLinear.blockUnipotent h Y' := by
    rw [hY', ← torInf_inv_mul_blockUnipotent_mul]
    simp only [mul_assoc, mul_inv_cancel_left]
  set Y'' : Matrix (Fin a) (Fin b) (InfiniteAdeles F) := Matrix.of fun p r =>
    PositiveRealIdeles.infiniteRealEmbedding F
      (Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p)) + ℓ)) * Wi p r with hY''
  have hY'Y'' : Y' = PositiveRealIdeles.infiniteRealEmbedding F (Real.exp (-ℓ)) • Y'' := by
    ext p r
    rw [hY', hY'', Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, smul_eq_mul,
      ← mul_assoc, ← map_mul, ← Real.exp_add]
    congr 3
    ring
  have hY''mem : Y'' ∈ 𝒲 := by
    refine mem_scaledBlockSet _ (fun p r => ⟨(Real.exp_pos _).le, ?_⟩) _ hWiD
    rw [Real.exp_le_one_iff]
    linarith [hgap p r]
  have hsmall : Real.exp (-ℓ) ∈ u₀ := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-ℓ) ≤ Real.exp (Real.log (ε / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = ε / 2 := Real.exp_log (by positivity)
      _ < ε := by linarith
  have hmemU : qi⁻¹ * GeneralLinear.blockUnipotent h Y' * qi ∈ U := by
    have := huv (show (Real.exp (-ℓ), (Y'', qi)) ∈ u₀ ×ˢ v₀ from
      ⟨hsmall, htv (show (Y'', qi) ∈ 𝒲 ×ˢ (AdelicGL.infinite F n '' Q) from
        ⟨hY''mem, q, hq, rfl⟩)⟩)
    simpa only [Set.mem_preimage, hΨdef, hY'Y''] using this
  refine ⟨GeneralLinear.blockUnipotent h ξ, qi⁻¹ * GeneralLinear.blockUnipotent h Y' * qi,
    qf⁻¹ * GeneralLinear.blockUnipotent h Wf * qf, hmemU, hLmem, ?_⟩
  have hWi' : GeneralLinear.blockUnipotent h Wi =
      torInf F n x * GeneralLinear.blockUnipotent h Y' * (torInf F n x)⁻¹ := by
    rw [← htor]
    group
  have key : AdelicGL.ofInfinite F n (GeneralLinear.blockUnipotent h Wi) *
      AdelicGL.ofFinite F n (GeneralLinear.blockUnipotent h Wf) *
      (AdelicGL.ofInfinite F n (torInf F n x) * q) =
      AdelicGL.ofInfinite F n (torInf F n x) * q *
        AdelicGL.ofInfinite F n (qi⁻¹ * GeneralLinear.blockUnipotent h Y' * qi) *
        AdelicGL.ofFinite F n (qf⁻¹ * GeneralLinear.blockUnipotent h Wf * qf) := by
    refine AdelicGL.ext_infinite_finite F n ?_ ?_
    · simp only [map_mul, AdelicGL.infinite_ofInfinite, AdelicGL.infinite_ofFinite, mul_one,
        ← hqi]
      rw [hWi']
      group
    · simp only [map_mul, AdelicGL.finite_ofInfinite, AdelicGL.finite_ofFinite, one_mul,
        mul_one, ← hqf]
      group
  rw [GeneralLinear.blockUnipotent_add, ← Langlands.Automorphic.rational_blockUnipotent,
    AdelicGL.blockUnipotent_eq F n h ((δ : Adeles F) • W), ← hWi, ← hWf,
    mul_assoc (AdelicGL.rational F n _), key]
  simp only [mul_assoc]


/-! ### Uniform continuity of compactly supported kernels -/

omit [NumberField F] in
/-- A continuous compactly supported function on a locally compact group is uniformly
continuous for right translations. -/
theorem exists_nhds_one_norm_sub_lt {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] {κ : G → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ∀ h ∈ U, ∀ z, ‖κ (z * h) - κ z‖ < ε := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hCc : IsCompact (tsupport κ * V⁻¹) := hκc.mul hVc.inv
  set N : Set (G × G) := {p | ‖κ (p.1 * p.2) - κ p.1‖ < ε} with hNdef
  have hN : IsOpen N := isOpen_lt
    ((hκ.comp continuous_mul).sub (hκ.comp continuous_fst)).norm continuous_const
  have hsub : (tsupport κ * V⁻¹) ×ˢ ({1} : Set G) ⊆ N := by
    rintro ⟨z, w⟩ ⟨-, hw⟩
    rw [Set.mem_singleton_iff] at hw
    change w = 1 at hw
    subst hw
    simpa [hNdef] using hε
  obtain ⟨u, v, -, hv, hCu, h1v, huv⟩ :=
    generalized_tube_lemma hCc isCompact_singleton hN hsub
  refine ⟨v ∩ interior V, hv.inter isOpen_interior,
    ⟨h1v rfl, mem_interior_iff_mem_nhds.mpr hV1⟩, fun h hh z => ?_⟩
  by_cases hz : z ∈ tsupport κ * V⁻¹
  · exact huv (show (z, h) ∈ u ×ˢ v from ⟨hCu hz, hh.1⟩)
  · have h0 : κ z = 0 := image_eq_zero_of_notMem_tsupport fun hz' =>
      hz ⟨z, hz', 1, by simpa using mem_of_mem_nhds hV1, mul_one z⟩
    have h1 : κ (z * h) = 0 := image_eq_zero_of_notMem_tsupport fun hz' =>
      hz ⟨z * h, hz', h⁻¹, by simpa using interior_subset hh.2, by group⟩
    rw [h0, h1, sub_self, norm_zero]
    exact hε

/-! ### The modulus of the reproducing kernel -/

theorem continuous_absDet_ofInfinite_rpow (c : ℝ) :
    Continuous fun z : InfiniteAdelicGL F n => absDet F n (AdelicGL.ofInfinite F n z) ^ c :=
  ((continuous_absDet F n).comp (map_continuous (AdelicGL.ofInfinite F n))).rpow_const
    fun _ => Or.inl (absDet_pos F n _).ne'

omit [NumberField F] in
theorem hasCompactSupport_kernel_translate {κ : InfiniteAdelicGL F n → ℂ}
    (hκc : HasCompactSupport κ) (h : InfiniteAdelicGL F n) :
    HasCompactSupport fun z : InfiniteAdelicGL F n => κ (z⁻¹ * h) :=
  hκc.comp_homeomorph ((Homeomorph.inv (InfiniteAdelicGL F n)).trans (Homeomorph.mulRight h))

section Modulus

variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
  (μ : Measure (InfiniteAdelicGL F n))

variable (F n) in
/-- The modulus of continuity `ω(h) = ∫ |det z|^c ‖κ(z⁻¹ h) - κ(z⁻¹)‖ dμ(z)` of a kernel,
weighted by the determinant character. -/
def kernelModulus (κ : InfiniteAdelicGL F n → ℂ) (c : ℝ) (h : InfiniteAdelicGL F n) : ℝ :=
  ∫ z, absDet F n (AdelicGL.ofInfinite F n z) ^ c * ‖κ (z⁻¹ * h) - κ z⁻¹‖ ∂μ

theorem integrable_modulus_integrand [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (c : ℝ)
    (h : InfiniteAdelicGL F n) :
    Integrable (fun z => absDet F n (AdelicGL.ofInfinite F n z) ^ c *
      ‖κ (z⁻¹ * h) - κ z⁻¹‖) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_absDet_ofInfinite_rpow c).mul
      ((hκ.comp (continuous_inv.mul continuous_const)).sub (hκ.comp continuous_inv)).norm
  · have h1 := hasCompactSupport_kernel_translate hκc h
    have h2 := hasCompactSupport_kernel_translate hκc 1
    simp only [mul_one] at h2
    exact (h1.sub h2).norm.mul_left

/-- The modulus is small near the identity. -/
theorem exists_kernelModulus_le [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (InfiniteAdelicGL F n), IsOpen U ∧ (1 : InfiniteAdelicGL F n) ∈ U ∧
      ∀ h ∈ U, kernelModulus F n μ κ c h ≤ ε := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : InfiniteAdelicGL F n)
  set C : Set (InfiniteAdelicGL F n) := (tsupport κ * V⁻¹)⁻¹ with hCdef
  have hCc : IsCompact C := (hκc.mul hVc.inv).inv
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  set ρ : InfiniteAdelicGL F n → ℝ := fun z => absDet F n (AdelicGL.ofInfinite F n z) ^ c
    with hρdef
  have hρ : Continuous ρ := continuous_absDet_ofInfinite_rpow c
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => Real.rpow_nonneg (absDet_pos F n _).le c
  set M : ℝ := ∫ z in C, ρ z ∂μ with hMdef
  have hM0 : 0 ≤ M := setIntegral_nonneg hCm fun z _ => hρ0 z
  obtain ⟨U₀, hU₀, h1U₀, hU₀κ⟩ :=
    exists_nhds_one_norm_sub_lt hκ hκc (ε := ε / (M + 1)) (by positivity)
  refine ⟨U₀ ∩ interior V, hU₀.inter isOpen_interior,
    ⟨h1U₀, mem_interior_iff_mem_nhds.mpr hV1⟩, fun h hh => ?_⟩
  have hρint : IntegrableOn ρ C μ := hρ.continuousOn.integrableOn_compact hCc
  have hpt : ∀ z, ρ z * ‖κ (z⁻¹ * h) - κ z⁻¹‖ ≤ C.indicator (fun z => ε / (M + 1) * ρ z) z := by
    intro z
    by_cases hz : z ∈ C
    · rw [Set.indicator_of_mem hz, mul_comm (ε / (M + 1))]
      exact mul_le_mul_of_nonneg_left (hU₀κ h hh.1 z⁻¹).le (hρ0 z)
    · rw [Set.indicator_of_notMem hz]
      have hz' : z⁻¹ ∉ tsupport κ * V⁻¹ := fun hz' => hz (Set.mem_inv.mpr hz')
      have h0 : κ z⁻¹ = 0 := image_eq_zero_of_notMem_tsupport fun hz'' =>
        hz' ⟨z⁻¹, hz'', 1, by simpa using mem_of_mem_nhds hV1, mul_one _⟩
      have h1 : κ (z⁻¹ * h) = 0 := image_eq_zero_of_notMem_tsupport fun hz'' =>
        hz' ⟨z⁻¹ * h, hz'', h⁻¹, by simpa using interior_subset hh.2, by group⟩
      rw [h0, h1, sub_self, norm_zero, mul_zero]
  calc kernelModulus F n μ κ c h
      ≤ ∫ z, C.indicator (fun z => ε / (M + 1) * ρ z) z ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
          mul_nonneg (hρ0 z) (norm_nonneg _))
          (IntegrableOn.integrable_indicator (Integrable.const_mul hρint _) hCm)
          (Filter.Eventually.of_forall hpt)
    _ = ε / (M + 1) * M := by rw [integral_indicator hCm, integral_const_mul]
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- **The reproduction estimate.** If `f` is reproduced by right convolution with `κ`
and its weight is bounded by `Φ`, then right archimedean translation by `h` moves `f(g)` by at
most `Φ |det g|^c ω(h)`. -/
theorem norm_sub_le_kernelModulus [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (c : ℝ)
    (f : S.Space) (Φ : ℝ) (hΦ : ∀ g, S.weight c f g ≤ Φ)
    (hrep : ∀ (g : AdelicGL F n) (h : InfiniteAdelicGL F n),
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) =
        ∫ z, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h) ∂μ)
    (g : AdelicGL F n) (h : InfiniteAdelicGL F n) :
    ‖evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) -
        evaluate F n (S.toContinuous f) g‖ ≤
      Φ * absDet F n g ^ c * kernelModulus F n μ κ c h := by
  have hF : Continuous fun z : InfiniteAdelicGL F n =>
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) :=
    (continuous_evaluate F n _).comp (continuous_const.mul (map_continuous _))
  have hI : ∀ h' : InfiniteAdelicGL F n, Integrable (fun z =>
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h')) μ :=
    fun h' => Continuous.integrable_of_hasCompactSupport
      (hF.mul (hκ.comp (continuous_inv.mul continuous_const)))
      (hasCompactSupport_kernel_translate hκc h').mul_left
  have h1 := hrep g 1
  simp only [map_one, mul_one] at h1
  have hI1 := hI 1
  simp only [mul_one] at hI1
  have hΦ0 : 0 ≤ Φ := (S.weight_nonneg c f g).trans (hΦ g)
  have hg0 : 0 ≤ absDet F n g ^ c := Real.rpow_nonneg (absDet_pos F n g).le c
  rw [hrep g h, h1, ← integral_sub (hI h) hI1, kernelModulus, ← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((integrable_modulus_integrand μ hκ hκc c h).const_mul _)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [← mul_sub, norm_mul, S.norm_eq_weight_mul c, absDet_mul,
    Real.mul_rpow (absDet_pos F n g).le (absDet_pos F n _).le]
  have hz0 : 0 ≤ absDet F n (AdelicGL.ofInfinite F n z) ^ c :=
    Real.rpow_nonneg (absDet_pos F n _).le c
  calc S.weight c f (g * AdelicGL.ofInfinite F n z) *
        (absDet F n g ^ c * absDet F n (AdelicGL.ofInfinite F n z) ^ c) *
        ‖κ (z⁻¹ * h) - κ z⁻¹‖
      ≤ Φ * (absDet F n g ^ c * absDet F n (AdelicGL.ofInfinite F n z) ^ c) *
        ‖κ (z⁻¹ * h) - κ z⁻¹‖ := by
        gcongr
        exact hΦ _
    _ = _ := by ring

end Modulus

/-! ### Central invariance of the weight and the central normal form -/

/-- If `n [F : ℚ] c = Re λ`, the weight of a vector with central law `λ` is invariant under the
central archimedean torus. -/
theorem weight_mul_centralTorus (lam : ℂ) (c : ℝ)
    (hc : (n : ℝ) * Module.finrank ℚ F * c = lam.re) (f : S.Space)
    (hcent : ∀ (g : AdelicGL F n) (t : ℝ),
      evaluate F n (S.toContinuous f) (g * centralTorus F n t) =
        Complex.exp (lam * t) * evaluate F n (S.toContinuous f) g)
    (g : AdelicGL F n) (t : ℝ) :
    S.weight c f (g * centralTorus F n t) = S.weight c f g := by
  have key : Real.exp (lam * (t : ℂ)).re * (Real.exp (n * t) ^ Module.finrank ℚ F) ^ (-c) =
      1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_eq_one_iff]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [← hc]
    ring
  have hdet : absDet F n (g * centralTorus F n t) ^ (-c) =
      absDet F n g ^ (-c) * (Real.exp (n * t) ^ Module.finrank ℚ F) ^ (-c) := by
    rw [absDet_mul, absDet_centralTorus]
    exact Real.mul_rpow (absDet_pos F n g).le (by positivity)
  have hw : S.weight c f (g * centralTorus F n t) = Real.exp (lam * (t : ℂ)).re *
      ‖evaluate F n (S.toContinuous f) g‖ *
        (absDet F n g ^ (-c) * (Real.exp (n * t) ^ Module.finrank ℚ F) ^ (-c)) := by
    unfold weight
    rw [hcent g t, norm_mul, Complex.norm_exp]
    exact congrArg (HMul.hMul _) hdet
  rw [hw, weight]
  linear_combination (‖evaluate F n (S.toContinuous f) g‖ * absDet F n g ^ (-c)) * key

variable (F n) in
/-- **Central normal form.** Up to rational left translation, every adelic matrix is
`torInf x * q * e^s` with `q` in a fixed compact set, `x` in a chamber and `∑ x = 0`. -/
theorem exists_centralNormalForm (hn : 0 < n) :
    ∃ (Q₁ : Set (AdelicGL F n)) (K : ℝ), IsCompact Q₁ ∧ 0 ≤ K ∧
      ∀ g : AdelicGL F n, ∃ (γ : RationalGL F n) (x : Fin n → ℝ) (s : ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ Chamber K x ∧ ∑ i, x i = 0 ∧
        AdelicGL.rational F n γ * g =
          AdelicGL.ofInfinite F n (torInf F n x) * q * centralTorus F n s := by
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  refine ⟨Q₁, K, hQ₁, hK, fun g => ?_⟩
  obtain ⟨γ, y, q, hq, heq, hy⟩ := hdec g
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set s : ℝ := (∑ i, y i) / n with hs
  refine ⟨γ, y - fun _ => s, s, q, hq, fun i j hij => ?_, ?_, ?_⟩
  · have := hy i j hij
    simp only [Pi.sub_apply]
    linarith
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hs]
    field_simp
    ring
  · rw [heq, mul_assoc, ← centralTorus_commute F n s q, ← mul_assoc, centralTorus, ← map_mul,
      ← torInf_add, sub_add_cancel]

/-- A cuspidal vector with a central law has bounded weight. -/
theorem exists_weight_bound [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) (hn : 0 < n)
    (lam : ℂ) (c : ℝ) (hc : (n : ℝ) * Module.finrank ℚ F * c = lam.re) (f : S.Space)
    (hcent : ∀ (g : AdelicGL F n) (t : ℝ),
      evaluate F n (S.toContinuous f) (g * centralTorus F n t) =
        Complex.exp (lam * t) * evaluate F n (S.toContinuous f) g) :
    ∃ M : ℝ, ∀ g, S.weight c f g ≤ M := by
  obtain ⟨Q₁, K, hQ₁, hK, hnf⟩ := exists_centralNormalForm F n hn
  obtain ⟨C, hC⟩ := S.exists_chamber_decay hS f Q₁ hQ₁ (R := 0) (c := 0) hK le_rfl
  obtain ⟨B, hB⟩ := hQ₁.exists_bound_of_continuousOn (f := fun q => absDet F n q ^ (-c))
    (((continuous_absDet F n).rpow_const fun q => Or.inl (absDet_pos F n q).ne').continuousOn)
  refine ⟨C * B, fun g => ?_⟩
  obtain ⟨γ, x, s, q, hq, hx, hsum, heq⟩ := hnf g
  have e1 : S.weight c f g = S.weight c f (AdelicGL.ofInfinite F n (torInf F n x) * q) := by
    rw [← S.weight_rational c f γ g, heq, S.weight_mul_centralTorus lam c hc f hcent]
  have e2 : absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q) = absDet F n q := by
    rw [absDet_mul, absDet_ofInfinite_torInf, hsum, Real.exp_zero, one_pow, one_mul]
  rw [e1, weight, e2]
  have h1 := hC x hx (by rw [hsum, abs_zero]) q hq
  rw [zero_mul, neg_zero, Real.exp_zero, mul_one] at h1
  have h2 : absDet F n q ^ (-c) ≤ B := (Real.le_norm_self _).trans (hB q hq)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (absDet_pos F n q).le _) ((norm_nonneg _).trans h1)

/-! ### The finiteness theorem -/

variable (F n) in
theorem absDet_one : absDet F n 1 = 1 := by
  have h := absDet_mul F n 1 1
  rw [mul_one] at h
  exact (mul_eq_right₀ (absDet_pos F n 1).ne').mp h.symm

/-- Evaluation of realized vectors at the points of a finite set. -/
def evalOn (T : Finset (AdelicGL F n)) : S.Space →ₗ[ℂ] (T → ℂ) :=
  LinearMap.pi fun p : T => (LinearMap.proj (p : AdelicGL F n)).comp
    ((ContinuousMap.coeFnLinearMap ℂ).comp ((toContinuousMap F n).comp S.toContinuous))

theorem evalOn_apply (T : Finset (AdelicGL F n)) (f : S.Space) (p : T) :
    S.evalOn T f p = evaluate F n (S.toContinuous f) p := rfl

variable (F n) in
/-- **Finite nets.** A compact set of adelic matrices is covered by finitely many translates
`p (U × L)` on which `|det|^{-c}` stays below `2`. -/
theorem exists_finite_net {Ω : Set (AdelicGL F n)} (hΩ : IsCompact Ω)
    {U : Set (InfiniteAdelicGL F n)} (hUo : IsOpen U) (hU1 : (1 : InfiniteAdelicGL F n) ∈ U)
    (L : Subgroup (FiniteAdelicGL F n)) (hL : IsOpen (L : Set (FiniteAdelicGL F n))) (c : ℝ) :
    ∃ T : Finset (AdelicGL F n), ∀ g ∈ Ω, ∃ p ∈ T,
      AdelicGL.infinite F n (p⁻¹ * g) ∈ U ∧ AdelicGL.finite F n (p⁻¹ * g) ∈ L ∧
        absDet F n (p⁻¹ * g) ^ (-c) < 2 := by
  have hN : ∀ p ∈ Ω, {g | AdelicGL.infinite F n (p⁻¹ * g) ∈ U ∧
      AdelicGL.finite F n (p⁻¹ * g) ∈ L ∧ absDet F n (p⁻¹ * g) ^ (-c) < 2} ∈ 𝓝 p := by
    intro p _
    have hcont : Continuous fun g : AdelicGL F n => p⁻¹ * g :=
      continuous_const.mul continuous_id
    refine IsOpen.mem_nhds
      ((hUo.preimage ((map_continuous (AdelicGL.infinite F n)).comp hcont)).inter
        ((hL.preimage ((map_continuous (AdelicGL.finite F n)).comp hcont)).inter
          (isOpen_lt (((continuous_absDet F n).rpow_const fun q =>
            Or.inl (absDet_pos F n q).ne').comp hcont) continuous_const))) ?_
    show AdelicGL.infinite F n (p⁻¹ * p) ∈ U ∧ AdelicGL.finite F n (p⁻¹ * p) ∈ L ∧
      absDet F n (p⁻¹ * p) ^ (-c) < 2
    rw [inv_mul_cancel, map_one, map_one, absDet_one, Real.one_rpow]
    exact ⟨hU1, L.one_mem, by norm_num⟩
  obtain ⟨T, -, hT⟩ := hΩ.elim_nhds_subcover _ hN
  exact ⟨T, fun g hg => by simpa only [Set.mem_iUnion, exists_prop, Set.mem_ofPred_eq] using hT hg⟩

/-- `g` is *absorbed along a maximal block* for `U` and `L`: every left block-unipotent
translate of `g` along some maximal block is, up to rational left translation, a right
translate of `g` by an element of `U × L`. -/
def CuspAbsorbed (U : Set (InfiniteAdelicGL F n)) (L : Subgroup (FiniteAdelicGL F n))
    (g : AdelicGL F n) : Prop :=
  ∃ a : Fin n, 0 < a.val ∧ ∀ Y : Matrix (Fin a) (Fin (n - a)) (Adeles F),
    ∃ (γ : RationalGL F n) (u : InfiniteAdelicGL F n) (l : FiniteAdelicGL F n),
      u ∈ U ∧ l ∈ L ∧
      GeneralLinear.blockUnipotent (Nat.add_sub_cancel' a.isLt.le) Y * g =
        AdelicGL.rational F n γ * (g * AdelicGL.ofInfinite F n u) * AdelicGL.ofFinite F n l

variable (F n) in
/-- **The cusp cover.** Up to rational left translation and the central torus, every adelic
matrix either lies in a fixed compact set or is absorbed along a maximal block. -/
theorem exists_cusp_cover (hn : 0 < n) (L : Subgroup (FiniteAdelicGL F n))
    (hL : IsOpen (L : Set (FiniteAdelicGL F n))) {U : Set (InfiniteAdelicGL F n)}
    (hUo : IsOpen U) (hU1 : (1 : InfiniteAdelicGL F n) ∈ U) :
    ∃ Ω : Set (AdelicGL F n), IsCompact Ω ∧ ∀ g : AdelicGL F n,
      ∃ (γ : RationalGL F n) (s : ℝ) (g' : AdelicGL F n),
        AdelicGL.rational F n γ * g = g' * centralTorus F n s ∧
          (g' ∈ Ω ∨ CuspAbsorbed U L g') := by
  obtain ⟨Q₁, K, hQ₁, hK, hnf⟩ := exists_centralNormalForm F n hn
  choose ℓ₀ hℓ₀ using fun a : Fin n =>
    exists_deep_absorption F n (Nat.add_sub_cancel' a.isLt.le) L hL hQ₁ hUo hU1
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = n * (0 + n * (n * (K + 2 * n * K))) +
      (n : ℝ) ^ 3 * ∑ a, |ℓ₀ a| := ⟨_, rfl⟩
  have hXc : IsCompact {x : Fin n → ℝ | ∑ i, |x i| ≤ B} := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := -B) (b := B)).of_isClosed_subset
      (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).abs)
        continuous_const) fun x hx i _ => ?_
    have hi : |x i| ≤ ∑ j, |x j| :=
      Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    exact abs_le.mp (hi.trans hx)
  refine ⟨(fun p : (Fin n → ℝ) × AdelicGL F n =>
      AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) ''
        ({x : Fin n → ℝ | ∑ i, |x i| ≤ B} ×ˢ Q₁),
    (hXc.prod hQ₁).image (((map_continuous (AdelicGL.ofInfinite F n)).comp
      ((continuous_torInf F n).comp continuous_fst)).mul continuous_snd), fun g => ?_⟩
  obtain ⟨γ, x, s, q, hq, hx, hsum, heq⟩ := hnf g
  refine ⟨γ, s, AdelicGL.ofInfinite F n (torInf F n x) * q, heq, ?_⟩
  have hB0 : 0 ≤ (n : ℝ) ^ 3 * ∑ a, |ℓ₀ a| :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => abs_nonneg _)
  rcases chamber_alternative hK x hx (R := 0) (by rw [hsum, abs_zero]) with
    h1 | ⟨a, ha, ℓ, hℓ, hgap, h2⟩
  · refine Or.inl ⟨(x, q), ⟨?_, hq⟩, rfl⟩
    change ∑ i, |x i| ≤ B
    rw [hB]
    linarith
  · by_cases hℓa : ℓ₀ a ≤ ℓ
    · exact Or.inr ⟨a, ha, hℓ₀ a x ℓ hℓa (fun p r => hgap _ _ (by simp) (by simp)) q hq⟩
    · refine Or.inl ⟨(x, q), ⟨?_, hq⟩, rfl⟩
      have hla : ℓ ≤ ∑ a, |ℓ₀ a| :=
        (lt_of_not_ge hℓa).le.trans ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun a => |ℓ₀ a|) (fun a _ => abs_nonneg _)
            (Finset.mem_univ a)))
      have : (n : ℝ) ^ 3 * ℓ ≤ (n : ℝ) ^ 3 * ∑ a, |ℓ₀ a| :=
        mul_le_mul_of_nonneg_left hla (by positivity)
      change ∑ i, |x i| ≤ B
      rw [hB]
      linarith

/-- A vector whose bounded weight is at most half of each of its bounds vanishes. -/
theorem eq_zero_of_weight_le_half (c : ℝ) (f : S.Space) (M : ℝ) (hM : ∀ g, S.weight c f g ≤ M)
    (hhalf : ∀ Φ : ℝ, (∀ g, S.weight c f g ≤ Φ) → ∀ g, S.weight c f g ≤ Φ / 2) : f = 0 := by
  have hbdd : BddAbove (Set.range (S.weight c f)) := ⟨M, by rintro _ ⟨g, rfl⟩; exact hM g⟩
  have hΦ : ∀ g, S.weight c f g ≤ ⨆ g, S.weight c f g := fun g => le_ciSup hbdd g
  have hΦle : (⨆ g, S.weight c f g) ≤ 0 := by
    have := ciSup_le (hhalf _ hΦ)
    linarith
  apply S.toContinuous_injective
  rw [map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hw : S.weight c f x = 0 := le_antisymm ((hΦ x).trans hΦle) (S.weight_nonneg c f x)
  change evaluate F n (S.toContinuous f) x = 0
  rw [← norm_eq_zero, S.norm_eq_weight_mul c, hw, zero_mul]

section Finiteness

variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
  (μ : Measure (InfiniteAdelicGL F n)) [IsFiniteMeasureOnCompacts μ]

/-- **The deep estimate.** If every block-unipotent left translate of `g` is absorbed into a
right translate by `U` (up to rational and level translations), then the weight of a cuspidal
reproduced vector at `g` is at most `Φ ε`. -/
theorem weight_le_of_absorbed [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) {a b : ℕ}
    (h : a + b = n) (ha : 0 < a) (hb : 0 < b) {κ : InfiniteAdelicGL F n → ℂ}
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) (c : ℝ) (f : S.Space) (Φ : ℝ)
    (hΦ : ∀ g, S.weight c f g ≤ Φ)
    (hrep : ∀ (g : AdelicGL F n) (h : InfiniteAdelicGL F n),
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) =
        ∫ z, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h) ∂μ)
    (L : Subgroup (FiniteAdelicGL F n))
    (hlevel : ∀ (g : AdelicGL F n), ∀ l ∈ L,
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofFinite F n l) =
        evaluate F n (S.toContinuous f) g)
    (U : Set (InfiniteAdelicGL F n)) (ε : ℝ) (hU : ∀ u ∈ U, kernelModulus F n μ κ c u ≤ ε)
    (g : AdelicGL F n)
    (habs : ∀ Y : Matrix (Fin a) (Fin b) (Adeles F),
      ∃ (γ : RationalGL F n) (u : InfiniteAdelicGL F n) (l : FiniteAdelicGL F n),
        u ∈ U ∧ l ∈ L ∧ GeneralLinear.blockUnipotent h Y * g =
          AdelicGL.rational F n γ * (g * AdelicGL.ofInfinite F n u) * AdelicGL.ofFinite F n l) :
    S.weight c f g ≤ Φ * ε := by
  have hΦ0 : 0 ≤ Φ := (S.weight_nonneg c f g).trans (hΦ g)
  have hg0 : 0 < absDet F n g := absDet_pos F n g
  have hnorm : ‖evaluate F n (S.toContinuous f) g‖ ≤ Φ * absDet F n g ^ c * ε := by
    refine S.norm_le_of_cuspidal hS h ha hb f g _ fun Y => ?_
    obtain ⟨γ, u, l, hu, hl, heq⟩ := habs Y
    rw [heq, hlevel _ l hl, evaluate_rational]
    exact (S.norm_sub_le_kernelModulus μ hκ hκc c f Φ hΦ hrep g u).trans
      (mul_le_mul_of_nonneg_left (hU u hu) (mul_nonneg hΦ0 (Real.rpow_nonneg hg0.le c)))
  rw [weight]
  calc ‖evaluate F n (S.toContinuous f) g‖ * absDet F n g ^ (-c)
      ≤ Φ * absDet F n g ^ c * ε * absDet F n g ^ (-c) :=
        mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg hg0.le _)
    _ = Φ * ε * (absDet F n g ^ c * absDet F n g ^ (-c)) := by ring
    _ = Φ * ε := by rw [← Real.rpow_add hg0, add_neg_cancel, Real.rpow_zero, mul_one]

/-- **The near estimate.** If the reproduced vector vanishes at `p` and `p⁻¹ g` lies in
`U × L`, then its weight at `g` is at most `Φ ε |det (p⁻¹ g)|^{-c}`. -/
theorem weight_le_of_near {κ : InfiniteAdelicGL F n → ℂ}
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) (c : ℝ) (f : S.Space) (Φ : ℝ)
    (hΦ : ∀ g, S.weight c f g ≤ Φ)
    (hrep : ∀ (g : AdelicGL F n) (h : InfiniteAdelicGL F n),
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) =
        ∫ z, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h) ∂μ)
    (L : Subgroup (FiniteAdelicGL F n))
    (hlevel : ∀ (g : AdelicGL F n), ∀ l ∈ L,
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofFinite F n l) =
        evaluate F n (S.toContinuous f) g)
    (U : Set (InfiniteAdelicGL F n)) (ε : ℝ) (hU : ∀ u ∈ U, kernelModulus F n μ κ c u ≤ ε)
    (p g : AdelicGL F n) (hp : evaluate F n (S.toContinuous f) p = 0)
    (hu : AdelicGL.infinite F n (p⁻¹ * g) ∈ U) (hl : AdelicGL.finite F n (p⁻¹ * g) ∈ L) :
    S.weight c f g ≤ Φ * ε * absDet F n (p⁻¹ * g) ^ (-c) := by
  have hΦ0 : 0 ≤ Φ := (S.weight_nonneg c f g).trans (hΦ g)
  set k := p⁻¹ * g with hk
  have hgk : g = p * AdelicGL.ofInfinite F n (AdelicGL.infinite F n k) *
      AdelicGL.ofFinite F n (AdelicGL.finite F n k) := by
    rw [mul_assoc, ← AdelicGL.eq_ofInfinite_mul_ofFinite F n k, hk, mul_inv_cancel_left]
  have hp0 := absDet_pos F n p
  have hk0 := absDet_pos F n k
  have hnorm : ‖evaluate F n (S.toContinuous f) g‖ ≤ Φ * absDet F n p ^ c * ε := by
    have := S.norm_sub_le_kernelModulus μ hκ hκc c f Φ hΦ hrep p (AdelicGL.infinite F n k)
    rw [hp, sub_zero, ← hlevel _ _ hl, ← hgk] at this
    exact this.trans
      (mul_le_mul_of_nonneg_left (hU _ hu) (mul_nonneg hΦ0 (Real.rpow_nonneg hp0.le c)))
  have hdet : absDet F n g ^ (-c) = absDet F n p ^ (-c) * absDet F n k ^ (-c) := by
    rw [← Real.mul_rpow hp0.le hk0.le, ← absDet_mul, hk, mul_inv_cancel_left]
  rw [weight, hdet]
  calc ‖evaluate F n (S.toContinuous f) g‖ * (absDet F n p ^ (-c) * absDet F n k ^ (-c))
      ≤ Φ * absDet F n p ^ c * ε * (absDet F n p ^ (-c) * absDet F n k ^ (-c)) :=
        mul_le_mul_of_nonneg_right hnorm
          (mul_nonneg (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hk0.le _))
    _ = Φ * ε * absDet F n k ^ (-c) * (absDet F n p ^ c * absDet F n p ^ (-c)) := by ring
    _ = Φ * ε * absDet F n k ^ (-c) := by
        rw [← Real.rpow_add hp0, add_neg_cancel, Real.rpow_zero, mul_one]

/-- **Halving.** A reproduced cuspidal vector of level `L`, whose weight is invariant under
the central torus and which vanishes on a net of the compact part of a cusp cover, has weight at
most half of any bound `Φ` for its weight. -/
theorem weight_le_half [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (c : ℝ)
    (f : S.Space) (Φ : ℝ) (hΦ : ∀ g, S.weight c f g ≤ Φ)
    (hrep : ∀ (g : AdelicGL F n) (h : InfiniteAdelicGL F n),
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) =
        ∫ z, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h) ∂μ)
    (L : Subgroup (FiniteAdelicGL F n))
    (hlevel : ∀ (g : AdelicGL F n), ∀ l ∈ L,
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofFinite F n l) =
        evaluate F n (S.toContinuous f) g)
    (hcent : ∀ (g : AdelicGL F n) (s : ℝ), S.weight c f (g * centralTorus F n s) =
      S.weight c f g)
    (U : Set (InfiniteAdelicGL F n)) (hU : ∀ u ∈ U, kernelModulus F n μ κ c u ≤ 1 / 4)
    (Ω : Set (AdelicGL F n))
    (hcover : ∀ g : AdelicGL F n, ∃ (γ : RationalGL F n) (s : ℝ) (g' : AdelicGL F n),
      AdelicGL.rational F n γ * g = g' * centralTorus F n s ∧ (g' ∈ Ω ∨ CuspAbsorbed U L g'))
    (T : Finset (AdelicGL F n))
    (hT : ∀ g ∈ Ω, ∃ p ∈ T, AdelicGL.infinite F n (p⁻¹ * g) ∈ U ∧
      AdelicGL.finite F n (p⁻¹ * g) ∈ L ∧ absDet F n (p⁻¹ * g) ^ (-c) < 2)
    (hfT : ∀ p ∈ T, evaluate F n (S.toContinuous f) p = 0) (g : AdelicGL F n) :
    S.weight c f g ≤ Φ / 2 := by
  have hΦ0 : 0 ≤ Φ := (S.weight_nonneg c f g).trans (hΦ g)
  obtain ⟨γ, s, g', heq, hg'⟩ := hcover g
  have e1 : S.weight c f g = S.weight c f g' := by
    rw [← S.weight_rational c f γ g, heq, hcent]
  rw [e1]
  rcases hg' with hΩ | ⟨a, ha, habs⟩
  · obtain ⟨p, hpT, hu, hl, h2⟩ := hT g' hΩ
    calc S.weight c f g' ≤ Φ * (1 / 4) * absDet F n (p⁻¹ * g') ^ (-c) :=
          S.weight_le_of_near μ hκ hκc c f Φ hΦ hrep L hlevel U (1 / 4) hU p g' (hfT p hpT) hu hl
      _ ≤ Φ * (1 / 4) * 2 := mul_le_mul_of_nonneg_left h2.le (by linarith)
      _ = Φ / 2 := by ring
  · calc S.weight c f g' ≤ Φ * (1 / 4) :=
          S.weight_le_of_absorbed μ hS (Nat.add_sub_cancel' a.isLt.le) ha
            (Nat.sub_pos_of_lt a.isLt) hκ hκc c f Φ hΦ hrep L hlevel U (1 / 4) hU g' habs
      _ ≤ Φ / 2 := by linarith

set_option maxHeartbeats 800000 in
/-- **Finite dimension of reproduced cuspidal vectors.** A space `W` of cuspidal vectors with a
common open level `L`, reproduced by right convolution with one continuous compactly supported
archimedean kernel `κ`, and with a common central law `λ`, is finite-dimensional. -/
theorem finiteDimensional_of_reproduced [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    (hn : 0 < n) {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (L : Subgroup (FiniteAdelicGL F n)) (hL : IsOpen (L : Set (FiniteAdelicGL F n))) (lam : ℂ)
    (W : Submodule ℂ S.Space)
    (hlevel : ∀ f ∈ W, ∀ (g : AdelicGL F n), ∀ l ∈ L,
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofFinite F n l) =
        evaluate F n (S.toContinuous f) g)
    (hrep : ∀ f ∈ W, ∀ (g : AdelicGL F n) (h : InfiniteAdelicGL F n),
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) =
        ∫ z, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h) ∂μ)
    (hcent : ∀ f ∈ W, ∀ (g : AdelicGL F n) (t : ℝ),
      evaluate F n (S.toContinuous f) (g * centralTorus F n t) =
        Complex.exp (lam * t) * evaluate F n (S.toContinuous f) g) :
    FiniteDimensional ℂ W := by
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (n : ℝ) * Module.finrank ℚ F * c = lam.re :=
    ⟨lam.re / (n * Module.finrank ℚ F), by field_simp⟩
  obtain ⟨U, hUo, hU1, hU⟩ := exists_kernelModulus_le μ hκ hκc c (ε := 1 / 4) (by norm_num)
  obtain ⟨Ω, hΩc, hcover⟩ := exists_cusp_cover F n hn L hL hUo hU1
  obtain ⟨T, hT⟩ := exists_finite_net F n hΩc hUo hU1 L hL c
  refine FiniteDimensional.of_injective ((S.evalOn T).comp W.subtype)
    ((injective_iff_map_eq_zero _).mpr fun f hf => Subtype.ext ?_)
  have hfT : ∀ p ∈ T, evaluate F n (S.toContinuous f) p = 0 := fun p hp => by
    rw [← S.evalOn_apply T f ⟨p, hp⟩]
    exact congrFun hf ⟨p, hp⟩
  obtain ⟨M, hM⟩ := S.exists_weight_bound hS hn lam c hc f (hcent f f.2)
  exact S.eq_zero_of_weight_le_half c f M hM fun Φ hΦ => S.weight_le_half μ hS hκ hκc c f Φ hΦ
    (hrep f f.2) L (hlevel f f.2) (S.weight_mul_centralTorus lam c hc f (hcent f f.2)) U hU Ω
    hcover T hT hfT

end Finiteness

end Langlands.Automorphic.OperatorRealization
