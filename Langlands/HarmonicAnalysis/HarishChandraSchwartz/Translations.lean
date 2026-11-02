import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Mathlib.Topology.Algebra.Module.UniformConvergence
import Mathlib.Topology.LocallyConstant.Basic

/-! # Translations on the Harish-Chandra Schwartz space

Waldspurger 2003, III.6: for `f ∈ C(G)` and `g₁, g₂ ∈ G` the function `ρ(g₁) λ(g₂) f`
lies in `C(G)`, and the map `G × G × C(G) → C(G)` is continuous. The weights `Ξ` and `σ`
are arbitrary; the translation bound of Lemma II.1.2 and the corresponding bound for `σ`
are explicit hypotheses.
-/

noncomputable section

open scoped ENNReal NNReal Topology UniformConvergence
open Filter TopologicalSpace

namespace Langlands.HarishChandraSchwartz

universe u

section Equicontinuity

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [LocallyConvexSpace ℝ V]

namespace Space

/-- Equicontinuity criterion for the inductive limit `C(G)`: a family of linear maps from
`C(G)` to a locally convex space is equicontinuous at `0` as soon as its restrictions to
every level `C_H` are. -/
theorem nhds_zero_of_forall_level {ι : Type*} (T : ι → Space Ξ σ →ₗ[ℂ] V)
    (hT : ∀ K : CompactOpenSubgroup G, ∀ W ∈ 𝓝 (0 : V),
      {f : Level Ξ σ K | ∀ i, T i (ofLevel K f) ∈ W} ∈ 𝓝 0)
    {W : Set V} (hW : W ∈ 𝓝 (0 : V)) : {f : Space Ξ σ | ∀ i, T i f ∈ W} ∈ 𝓝 0 := by
  let : UniformSpace V := IsTopologicalAddGroup.rightUniformSpace V
  have : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
  let φ : Space Ξ σ →ₗ[ℂ] (ι → V) := LinearMap.pi T
  let ofFun' : (ι → V) →+ (ι →ᵤ V) := AddMonoidHom.id _
  let F : Space Ξ σ →+ (ι →ᵤ V) := ofFun'.comp φ.toAddMonoidHom
  -- the topology of uniform convergence of the family `T`
  let t : TopologicalSpace (Space Ξ σ) := induced F inferInstance
  have hadd : @IsTopologicalAddGroup _ t _ := isTopologicalAddGroup_induced F
  have hbasis : (@nhds _ t 0).HasBasis (fun S : Set V => S ∈ 𝓝 (0 : V) ∧ Convex ℝ S)
      fun S => {f : Space Ξ σ | ∀ i, T i f ∈ S} := by
    rw [nhds_induced, map_zero]
    exact (UniformFun.hasBasis_nhds_zero_of_basis
      (LocallyConvexSpace.convex_basis_zero ℝ V)).comap F
  have hbdd : ∀ u : Space Ξ σ, Bornology.IsVonNBounded ℂ (Set.range (φ u)) := by
    intro u W hW
    obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem u)
    let f : Level Ξ σ K := (⟨(u : G → ℂ), hK⟩ : levelSubmodule Ξ σ K.toSubgroup)
    have hu : ofLevel K f = u := ext fun _ => rfl
    filter_upwards [absorbent_nhds_zero (hT K W hW) f] with a ha
    rintro _ ⟨i, rfl⟩
    obtain ⟨f', hf', hff'⟩ := Set.mem_smul_set.mp (ha (Set.mem_singleton f))
    refine Set.mem_smul_set.mpr ⟨T i (ofLevel K f'), hf' i, ?_⟩
    rw [← map_smul, ← map_smul, hff', hu]
    rfl
  have hsmul : @ContinuousSMul ℂ (Space Ξ σ) _ _ t := by
    let _ : TopologicalSpace (Space Ξ σ) := t
    exact UniformFun.continuousSMul_induced_of_range_bounded ℂ ι V (Space Ξ σ) φ ⟨rfl⟩ hbdd
  have hlc : @LocallyConvexSpace ℝ (Space Ξ σ) _ _ _ _ t := by
    let _ : TopologicalSpace (Space Ξ σ) := t
    refine LocallyConvexSpace.ofBasisZero ℝ (Space Ξ σ) _ _ hbasis fun S hS => ?_
    rw [Set.ofPred_forall]
    exact convex_iInter fun i => hS.2.linear_preimage ((T i).restrictScalars ℝ)
  have hle : originalTop Ξ σ ≤ t := by
    refine iSup_le fun K => ?_
    rw [← continuous_iff_coinduced_le]
    refine continuous_induced_rng.mpr ?_
    let FK : Level Ξ σ K →+ (ι →ᵤ V) := F.comp (ofLevel K).toAddMonoidHom
    refine continuous_of_continuousAt_zero FK ?_
    rw [ContinuousAt, map_zero]
    exact (UniformFun.hasBasis_nhds_zero).tendsto_right_iff.mpr fun W hW => hT K W hW
  have hle' : topologicalSpace Ξ σ ≤ t := by
    have := hadd
    have := hsmul
    have := hlc
    exact (topologicalSpace_le_iff (t := t)).mpr hle
  obtain ⟨S, hS, hSW⟩ := (LocallyConvexSpace.convex_basis_zero ℝ V).mem_iff.mp hW
  have hmem := (le_iff_nhds _ _).mp hle' 0 (hbasis.mem_of_mem hS)
  exact Filter.mem_of_superset hmem fun f hf i => hSW (hf i)

end Space

end Equicontinuity

section Translate

variable {G : Type u} [Group G]

/-- The two-sided translate `ρ(g₁) λ(g₂) f : x ↦ f(g₂⁻¹ x g₁)`, where `ρ` is the right and
`λ` the left regular action (Waldspurger I.6 and III.6). -/
def translate (g₁ g₂ : G) (f : G → ℂ) : G → ℂ :=
  fun x => f (g₂⁻¹ * x * g₁)

@[simp] theorem translate_apply (g₁ g₂ : G) (f : G → ℂ) (x : G) :
    translate g₁ g₂ f x = f (g₂⁻¹ * x * g₁) :=
  rfl

@[simp] theorem translate_one_one (f : G → ℂ) : translate 1 1 f = f := by
  funext x
  simp

theorem translate_translate (g₁ g₂ h₁ h₂ : G) (f : G → ℂ) :
    translate g₁ g₂ (translate h₁ h₂ f) = translate (g₁ * h₁) (g₂ * h₂) f := by
  funext x
  simp only [translate_apply, mul_inv_rev, mul_assoc]

/-- A function bi-invariant under `H` is fixed by translations by elements of `H`. -/
theorem IsBiInvariant.translate_eq {H : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f)
    {h₁ h₂ : G} (h₁m : h₁ ∈ H) (h₂m : h₂ ∈ H) : translate h₁ h₂ f = f := by
  funext x
  exact hf _ (H.inv_mem h₂m) _ h₁m x

/-- The conjugate `g H g⁻¹ = {x | g⁻¹ x g ∈ H}` of a subgroup. -/
def conjSubgroup (g : G) (H : Subgroup G) : Subgroup G :=
  H.comap (MulAut.conj g).symm.toMonoidHom

theorem mem_conjSubgroup {g : G} {H : Subgroup G} {x : G} :
    x ∈ conjSubgroup g H ↔ g⁻¹ * x * g ∈ H := by
  simp [conjSubgroup, MulAut.conj_symm_apply]

/-- If `f` is bi-invariant under `H`, then `ρ(g₁) λ(g₂) f` is bi-invariant under
`g₁ H g₁⁻¹ ∩ g₂ H g₂⁻¹`. -/
theorem IsBiInvariant.translate {H : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f)
    (g₁ g₂ : G) :
    IsBiInvariant (conjSubgroup g₁ H ⊓ conjSubgroup g₂ H) (translate g₁ g₂ f) := by
  intro h₁ h₁m h₂ h₂m x
  have e₁ : g₂⁻¹ * h₁ * g₂ ∈ H := mem_conjSubgroup.mp (Subgroup.mem_inf.mp h₁m).2
  have e₂ : g₁⁻¹ * h₂ * g₁ ∈ H := mem_conjSubgroup.mp (Subgroup.mem_inf.mp h₂m).1
  have h : g₂⁻¹ * (h₁ * x * h₂) * g₁ =
      (g₂⁻¹ * h₁ * g₂) * (g₂⁻¹ * x * g₁) * (g₁⁻¹ * h₂ * g₁) := by group
  simp only [translate_apply]
  rw [h, hf _ e₁ _ e₂]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The conjugate `g K g⁻¹` of a compact open subgroup. -/
def CompactOpenSubgroup.conj (g : G) (K : CompactOpenSubgroup G) : CompactOpenSubgroup G :=
  ⟨K.1.comap (MulAut.conj g).symm.toMonoidHom
      (by
        have : ⇑(MulAut.conj g).symm.toMonoidHom = fun x => g⁻¹ * x * g :=
          funext fun x => MulAut.conj_symm_apply g x
        rw [this]
        fun_prop),
    by
      have h := ((Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)).isCompact_preimage.mpr
        K.2
      convert h using 1
      ext x
      simp [MulAut.conj_symm_apply]⟩

theorem CompactOpenSubgroup.conj_toSubgroup (g : G) (K : CompactOpenSubgroup G) :
    (K.conj g).toSubgroup = conjSubgroup g K.toSubgroup :=
  rfl

/-- The compact open subgroup `g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹`, under which `ρ(g₁) λ(g₂)` maps
`K`-bi-invariant functions to bi-invariant functions. -/
def CompactOpenSubgroup.translate (g₁ g₂ : G) (K : CompactOpenSubgroup G) :
    CompactOpenSubgroup G :=
  (K.conj g₁).inf (K.conj g₂)

theorem CompactOpenSubgroup.translate_toSubgroup (g₁ g₂ : G) (K : CompactOpenSubgroup G) :
    (K.translate g₁ g₂).toSubgroup = conjSubgroup g₁ K.toSubgroup ⊓ conjSubgroup g₂ K.toSubgroup :=
  rfl

end Translate

section Bounds

variable {G : Type u} [Group G]

/-- Lemma II.1.2 of Waldspurger as a property of arbitrary weights: there is `d ∈ ℕ` such
that for all `g₁, g₂ ∈ G` there is `C` with `Ξ(g₁ g g₂) ≤ C Ξ(g) (1 + σ(g))^d` for all
`g ∈ G`. -/
def TranslationBound (Ξ σ : G → ℝ) : Prop :=
  ∃ d : ℕ, ∀ g₁ g₂ : G, ∃ C : ℝ, ∀ g : G, Ξ (g₁ * g * g₂) ≤ C * Ξ g * (1 + σ g) ^ d

/-- Two-sided translations change `1 + σ` by at most a bounded factor: for all `g₁, g₂`
there is `C` with `1 + σ(g₁ g g₂) ≤ C (1 + σ(g))` for all `g`. -/
def HeightTranslationBound (σ : G → ℝ) : Prop :=
  ∀ g₁ g₂ : G, ∃ C : ℝ, ∀ g : G, 1 + σ (g₁ * g * g₂) ≤ C * (1 + σ g)

/-- The hypotheses on the weights used for translations: `Ξ > 0`, `σ ≥ 0`, Lemma II.1.2
for `Ξ`, and the translation bound for `σ`. -/
structure TranslationWeights (Ξ σ : G → ℝ) : Prop where
  pos : ∀ g, 0 < Ξ g
  nonneg : ∀ g, 0 ≤ σ g
  bound : TranslationBound Ξ σ
  heightBound : HeightTranslationBound σ

variable {Ξ σ : G → ℝ}

/-- A nonnegative subadditive `σ` (as the height `σ = log ‖·‖` of Waldspurger I.1)
satisfies the translation bound, with `C = (1 + σ(g₁)) (1 + σ(g₂))`. -/
theorem heightTranslationBound_of_le_add (hσ : ∀ g, 0 ≤ σ g)
    (hadd : ∀ g h, σ (g * h) ≤ σ g + σ h) : HeightTranslationBound σ := by
  intro g₁ g₂
  refine ⟨(1 + σ g₁) * (1 + σ g₂), fun g => ?_⟩
  have h1 := hadd (g₁ * g) g₂
  have h2 := hadd g₁ g
  have a := hσ g₁
  have b := hσ g
  have c := hσ g₂
  nlinarith [mul_nonneg a b, mul_nonneg b c, mul_nonneg a c, mul_nonneg (mul_nonneg a b) c]

/-- Comparison of `(1 + σ)^s` at `g₁ y g₂` and at `y`, for every real exponent `s`. -/
theorem HeightTranslationBound.exists_rpow_le (hσ : ∀ g, 0 ≤ σ g)
    (hS : HeightTranslationBound σ) (g₁ g₂ : G) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (s : ℝ) (y : G), (1 + σ (g₁ * y * g₂)) ^ s ≤ M ^ |s| * (1 + σ y) ^ s := by
  obtain ⟨C₁, hC₁⟩ := hS g₁ g₂
  obtain ⟨C₂, hC₂⟩ := hS g₁⁻¹ g₂⁻¹
  refine ⟨max 1 (max C₁ C₂), le_max_left _ _, fun s y => ?_⟩
  set M := max 1 (max C₁ C₂)
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hy : 0 < 1 + σ y := by linarith [hσ y]
  have hx : 0 < 1 + σ (g₁ * y * g₂) := by linarith [hσ (g₁ * y * g₂)]
  have hup : 1 + σ (g₁ * y * g₂) ≤ M * (1 + σ y) :=
    (hC₁ y).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hy.le)
  have hdown : 1 + σ y ≤ M * (1 + σ (g₁ * y * g₂)) := by
    have h := hC₂ (g₁ * y * g₂)
    have e : g₁⁻¹ * (g₁ * y * g₂) * g₂⁻¹ = y := by group
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hx.le)
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs, ← Real.mul_rpow hM0.le hy.le]
    exact Real.rpow_le_rpow hx.le hup hs
  · rw [abs_of_neg hs]
    have hle : (1 + σ y) / M ≤ 1 + σ (g₁ * y * g₂) := by
      rw [div_le_iff₀ hM0]
      linarith
    calc (1 + σ (g₁ * y * g₂)) ^ s ≤ ((1 + σ y) / M) ^ s :=
          Real.rpow_le_rpow_of_nonpos (div_pos hy hM0) hle hs.le
      _ = M ^ (-s) * (1 + σ y) ^ s := by
          rw [Real.div_rpow hy.le hM0.le, Real.rpow_neg hM0.le, div_eq_mul_inv, mul_comm]

/-- The seminorm estimate for translations: `ν_r(ρ(g₁) λ(g₂) f) ≤ c ν_{r+d}(f)`, with `d`
from Lemma II.1.2 and `c` depending on `g₁`, `g₂` and `r`. -/
theorem TranslationWeights.nu_translate_le (hw : TranslationWeights Ξ σ) (g₁ g₂ : G) :
    ∃ d : ℕ, ∀ r : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∀ f : G → ℂ,
      nu Ξ σ r (translate g₁ g₂ f) ≤ ENNReal.ofReal c * nu Ξ σ (r + d) f := by
  obtain ⟨d, hd⟩ := hw.bound
  obtain ⟨C, hC⟩ := hd g₂⁻¹ g₁
  obtain ⟨M, hM1, hM⟩ := hw.heightBound.exists_rpow_le hw.nonneg g₂ g₁⁻¹
  have hC0 : 0 < C := by
    have h := lt_of_lt_of_le (hw.pos _) (hC 1)
    have hb : 0 < Ξ 1 * (1 + σ 1) ^ d :=
      mul_pos (hw.pos 1) (pow_pos (by linarith [hw.nonneg 1]) d)
    rw [mul_assoc] at h
    exact pos_of_mul_pos_left h hb.le
  refine ⟨d, fun r => ⟨C * M ^ |r + d|, ?_, fun f => ?_⟩⟩
  · exact mul_nonneg hC0.le (Real.rpow_nonneg (by linarith) _)
  refine iSup_le fun x => ?_
  set y := g₂⁻¹ * x * g₁ with hy_def
  have hxy : x = g₂ * y * g₁⁻¹ := by rw [hy_def]; group
  have hΞx := hw.pos x
  have hΞy := hw.pos y
  have hσx : 0 < 1 + σ x := by linarith [hw.nonneg x]
  have hσy : 0 < 1 + σ y := by linarith [hw.nonneg y]
  -- the real inequality between the weights at `x` and at `y`
  have hreal : (Ξ x)⁻¹ * (1 + σ x) ^ r ≤
      (C * M ^ |r + d|) * ((Ξ y)⁻¹ * (1 + σ y) ^ (r + d)) := by
    have h1 : (Ξ x)⁻¹ ≤ C * (1 + σ x) ^ (d : ℝ) * (Ξ y)⁻¹ := by
      have h := hC x
      rw [Real.rpow_natCast]
      rw [inv_le_iff_one_le_mul₀ hΞx]
      have : 1 ≤ C * (1 + σ x) ^ d * Ξ x * (Ξ y)⁻¹ := by
        rw [le_mul_inv_iff₀ hΞy, one_mul]
        linarith
      linarith
    have h2 : (1 + σ x) ^ (r + d) ≤ M ^ |r + d| * (1 + σ y) ^ (r + d) := by
      have h := hM (r + d) y
      rwa [← hxy] at h
    calc (Ξ x)⁻¹ * (1 + σ x) ^ r
        ≤ C * (1 + σ x) ^ (d : ℝ) * (Ξ y)⁻¹ * (1 + σ x) ^ r :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hσx.le _)
      _ = C * (Ξ y)⁻¹ * (1 + σ x) ^ (r + d) := by
          rw [Real.rpow_add hσx]
          ring
      _ ≤ C * (Ξ y)⁻¹ * (M ^ |r + d| * (1 + σ y) ^ (r + d)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0.le (inv_nonneg.mpr hΞy.le))
      _ = (C * M ^ |r + d|) * ((Ξ y)⁻¹ * (1 + σ y) ^ (r + d)) := by ring
  have hc0 : 0 ≤ C * M ^ |r + d| := mul_nonneg hC0.le (Real.rpow_nonneg (by linarith) _)
  have hweight : weight Ξ σ r x ≤
      ENNReal.ofReal (C * M ^ |r + d|) * weight Ξ σ (r + d) y := by
    unfold weight
    rw [← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ‖translate g₁ g₂ f x‖ₑ * weight Ξ σ r x
      = ‖f y‖ₑ * weight Ξ σ r x := rfl
    _ ≤ ‖f y‖ₑ * (ENNReal.ofReal (C * M ^ |r + d|) * weight Ξ σ (r + d) y) := by gcongr
    _ = ENNReal.ofReal (C * M ^ |r + d|) * (‖f y‖ₑ * weight Ξ σ (r + d) y) := by ring
    _ ≤ ENNReal.ofReal (C * M ^ |r + d|) * nu Ξ σ (r + d) f := by
        gcongr
        exact enorm_mul_weight_le_nu f y

end Bounds

section Operators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}

/-- `ρ(g₁) λ(g₂)` maps the level `C_K` into the level of `g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹`
(Waldspurger III.6, using Lemma II.1.2). -/
theorem TranslationWeights.translate_mem_levelSubmodule (hw : TranslationWeights Ξ σ)
    (g₁ g₂ : G) {K : CompactOpenSubgroup G} {f : G → ℂ}
    (hf : f ∈ levelSubmodule Ξ σ K.toSubgroup) :
    translate g₁ g₂ f ∈ levelSubmodule Ξ σ (K.translate g₁ g₂).toSubgroup := by
  refine ⟨hf.1.translate g₁ g₂, fun r => ?_⟩
  obtain ⟨d, hd⟩ := hw.nu_translate_le g₁ g₂
  obtain ⟨c, -, hc⟩ := hd r
  exact lt_of_le_of_lt (hc f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf.2 _))

/-- `ρ(g₁) λ(g₂)` maps `C(G)` into itself (Waldspurger III.6). -/
theorem TranslationWeights.translate_mem_schwartzSubmodule (hw : TranslationWeights Ξ σ)
    (g₁ g₂ : G) {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) :
    translate g₁ g₂ f ∈ schwartzSubmodule Ξ σ := by
  let L : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := translate g₁ g₂
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : schwartzSubmodule Ξ σ ≤ (schwartzSubmodule Ξ σ).comap L :=
    iSup_le fun K _ hf' => levelSubmodule_le_schwartzSubmodule Ξ σ (K.translate g₁ g₂)
      (hw.translate_mem_levelSubmodule g₁ g₂ hf')
  exact hle hf

namespace Level

/-- `ρ(g₁) λ(g₂) : C_K → C_{g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹}` as a linear map. -/
def translate (hw : TranslationWeights Ξ σ) (g₁ g₂ : G) (K : CompactOpenSubgroup G) :
    Level Ξ σ K →ₗ[ℂ] Level Ξ σ (K.translate g₁ g₂) where
  toFun f := (⟨HarishChandraSchwartz.translate g₁ g₂ f,
    hw.translate_mem_levelSubmodule g₁ g₂ (f : levelSubmodule Ξ σ K.toSubgroup).2⟩ :
      levelSubmodule Ξ σ (K.translate g₁ g₂).toSubgroup)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_translate (hw : TranslationWeights Ξ σ) (g₁ g₂ : G)
    (K : CompactOpenSubgroup G) (f : Level Ξ σ K) :
    ((translate hw g₁ g₂ K f : Level Ξ σ (K.translate g₁ g₂)) : G → ℂ) =
      HarishChandraSchwartz.translate g₁ g₂ f :=
  rfl

theorem continuous_translate (hw : TranslationWeights Ξ σ) (g₁ g₂ : G)
    (K : CompactOpenSubgroup G) : Continuous (translate hw g₁ g₂ K) := by
  refine (withSeminorms K).continuous_of_isBounded (withSeminorms (K.translate g₁ g₂)) _ ?_
  refine Seminorm.IsBounded.of_real fun r => ?_
  obtain ⟨d, hd⟩ := hw.nu_translate_le g₁ g₂
  obtain ⟨c, hc0, hc⟩ := hd r
  refine ⟨{r + d}, c, fun f => ?_⟩
  rw [Finset.sup_singleton]
  change (nu Ξ σ r (HarishChandraSchwartz.translate g₁ g₂ f)).toReal ≤
    c * (nu Ξ σ (r + d) f).toReal
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nu_ne_top f _)) (hc f)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at h

end Level

namespace Space

omit [IsTopologicalGroup G] in
@[simp] theorem coe_sub (f₁ f₂ : Space Ξ σ) : ((f₁ - f₂ : Space Ξ σ) : G → ℂ) = f₁ - f₂ :=
  rfl

/-- `ρ(g₁) λ(g₂) : C(G) → C(G)` as a linear map. -/
def translateLinear (hw : TranslationWeights Ξ σ) (g₁ g₂ : G) :
    Space Ξ σ →ₗ[ℂ] Space Ξ σ where
  toFun f := (⟨HarishChandraSchwartz.translate g₁ g₂ f,
    hw.translate_mem_schwartzSubmodule g₁ g₂ (coe_mem f)⟩ : schwartzSubmodule Ξ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ρ(g₁) λ(g₂) : C(G) → C(G)` is continuous; it is built from III.6(1). -/
def translate (hw : TranslationWeights Ξ σ) (g₁ g₂ : G) : Space Ξ σ →L[ℂ] Space Ξ σ :=
  mkCLM (translateLinear hw g₁ g₂) fun K => by
    have h : (translateLinear hw g₁ g₂ ∘ ofLevel K : Level Ξ σ K → Space Ξ σ) =
        ofLevel (K.translate g₁ g₂) ∘ Level.translate hw g₁ g₂ K :=
      funext fun _ => ext fun _ => rfl
    rw [h]
    exact (continuous_ofLevel _).comp (Level.continuous_translate hw g₁ g₂ K)

@[simp] theorem coe_translate (hw : TranslationWeights Ξ σ) (g₁ g₂ : G) (f : Space Ξ σ) :
    ((translate hw g₁ g₂ f : Space Ξ σ) : G → ℂ) = HarishChandraSchwartz.translate g₁ g₂ f :=
  rfl

theorem translate_apply (hw : TranslationWeights Ξ σ) (g₁ g₂ : G) (f : Space Ξ σ) (x : G) :
    translate hw g₁ g₂ f x = f (g₂⁻¹ * x * g₁) :=
  rfl

@[simp] theorem translate_one_one (hw : TranslationWeights Ξ σ) (f : Space Ξ σ) :
    translate hw 1 1 f = f :=
  ext fun x => by simp [translate_apply]

theorem translate_translate (hw : TranslationWeights Ξ σ) (g₁ g₂ h₁ h₂ : G) (f : Space Ξ σ) :
    translate hw g₁ g₂ (translate hw h₁ h₂ f) = translate hw (g₁ * h₁) (g₂ * h₂) f :=
  ext fun x => congrFun (HarishChandraSchwartz.translate_translate g₁ g₂ h₁ h₂ f) x

variable [Nonempty (CompactOpenSubgroup G)]

/-- Translations by a compact open subgroup `H` form an equicontinuous family at `0`. On a
level `C_K` only finitely many of them are distinct, because `ρ(k₁) λ(k₂)` depends only on
the cosets `k₁ (K ∩ H)` and `k₂ (K ∩ H)`. -/
theorem translate_nhds_zero (hw : TranslationWeights Ξ σ) (H : CompactOpenSubgroup G)
    {W : Set (Space Ξ σ)} (hW : W ∈ 𝓝 (0 : Space Ξ σ)) :
    {f : Space Ξ σ | ∀ k : (H.1 : Set G) × (H.1 : Set G), translate hw k.1 k.2 f ∈ W} ∈ 𝓝 0 := by
  let ι := (H.1 : Set G) × (H.1 : Set G)
  have : CompactSpace (H.1 : Set G) := isCompact_iff_compactSpace.mp H.2
  refine nhds_zero_of_forall_level (fun k : ι => (translate hw k.1 k.2).toLinearMap)
    (fun K W hW => ?_) hW
  let Φ : ι → Level Ξ σ K → Space Ξ σ := fun k f => translate hw k.1 k.2 (ofLevel K f)
  have hloc : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro k
    have hopen : IsOpen {k' : ι | (k.1 : G)⁻¹ * k'.1 ∈ (K.1 : Set G) ∧
        (k.2 : G)⁻¹ * k'.2 ∈ (K.1 : Set G)} :=
      (K.1.isOpen.preimage (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).inter
        (K.1.isOpen.preimage (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
    have hk : k ∈ {k' : ι | (k.1 : G)⁻¹ * k'.1 ∈ (K.1 : Set G) ∧
        (k.2 : G)⁻¹ * k'.2 ∈ (K.1 : Set G)} := by
      simp only [Set.mem_ofPred_eq, inv_mul_cancel]
      exact ⟨K.1.one_mem, K.1.one_mem⟩
    filter_upwards [hopen.mem_nhds hk] with k' hk'
    funext f
    refine ext fun x => ?_
    have h := congrFun ((Level.isBiInvariant f).translate_eq hk'.1 hk'.2)
      ((k.2 : G)⁻¹ * x * k.1)
    simp only [HarishChandraSchwartz.translate_apply] at h
    change f ((k'.2 : G)⁻¹ * x * k'.1) = f ((k.2 : G)⁻¹ * x * k.1)
    rw [← h]
    congr 1
    group
  have hfin := hloc.range_finite
  have hset : {f : Level Ξ σ K | ∀ k : ι, (translate hw k.1 k.2).toLinearMap (ofLevel K f) ∈ W} =
      ⋂ φ ∈ Set.range Φ, φ ⁻¹' W := by
    ext f
    simp [Φ]
  rw [hset]
  refine (Filter.biInter_mem hfin).mpr ?_
  rintro _ ⟨k, rfl⟩
  have hc : Continuous (Φ k) := (translate hw k.1 k.2).continuous.comp (continuous_ofLevel K)
  refine hc.continuousAt.preimage_mem_nhds ?_
  simpa [Φ] using hW

/-- Waldspurger III.6: the map `G × G × C(G) → C(G)`, `(g₁, g₂, f) ↦ ρ(g₁) λ(g₂) f`, is
continuous. -/
theorem continuous_translate (hw : TranslationWeights Ξ σ) :
    Continuous fun p : (G × G) × Space Ξ σ => translate hw p.1.1 p.1.2 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨g₁, g₂⟩, f₀⟩
  rw [ContinuousAt, Filter.tendsto_def]
  intro W hW
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f₀)
  set A := translate hw g₁ g₂
  have hW' : (fun u => A u + A f₀) ⁻¹' W ∈ 𝓝 (0 : Space Ξ σ) := by
    refine (A.continuous.add continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa using hW
  have hU := translate_nhds_zero hw H hW'
  have h₁ : {x : G | g₁⁻¹ * x ∈ (H.1 : Set G)} ∈ 𝓝 g₁ :=
    (H.1.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp)
  have h₂ : {x : G | g₂⁻¹ * x ∈ (H.1 : Set G)} ∈ 𝓝 g₂ :=
    (H.1.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp)
  have h₃ : (fun f => f - f₀) ⁻¹' {f : Space Ξ σ | ∀ k : (H.1 : Set G) × (H.1 : Set G),
      translate hw k.1 k.2 f ∈ (fun u => A u + A f₀) ⁻¹' W} ∈ 𝓝 f₀ := by
    refine (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa using hU
  filter_upwards [prod_mem_nhds (prod_mem_nhds h₁ h₂) h₃]
  rintro ⟨⟨x₁, x₂⟩, f⟩ ⟨⟨hx₁, hx₂⟩, hf⟩
  have hk := hf (⟨g₁⁻¹ * x₁, hx₁⟩, ⟨g₂⁻¹ * x₂, hx₂⟩)
  simp only [Set.mem_preimage] at hk ⊢
  convert hk using 1
  refine ext fun x => ?_
  have hinv := (Level.isBiInvariant (K := H)
    ((⟨(f₀ : G → ℂ), hH⟩ : levelSubmodule Ξ σ H.toSubgroup) : Level Ξ σ H))
    _ (H.toSubgroup.inv_mem (show g₂⁻¹ * x₂ ∈ H.toSubgroup from hx₂))
    _ (show g₁⁻¹ * x₁ ∈ H.toSubgroup from hx₁) (g₂⁻¹ * x * g₁)
  change f₀ ((g₂⁻¹ * x₂)⁻¹ * (g₂⁻¹ * x * g₁) * (g₁⁻¹ * x₁)) = f₀ (g₂⁻¹ * x * g₁) at hinv
  change f (x₂⁻¹ * x * x₁) =
    (f ((g₂⁻¹ * x₂)⁻¹ * (g₂⁻¹ * x * g₁) * (g₁⁻¹ * x₁)) -
      f₀ ((g₂⁻¹ * x₂)⁻¹ * (g₂⁻¹ * x * g₁) * (g₁⁻¹ * x₁))) + f₀ (g₂⁻¹ * x * g₁)
  rw [hinv]
  have e : (g₂⁻¹ * x₂)⁻¹ * (g₂⁻¹ * x * g₁) * (g₁⁻¹ * x₁) = x₂⁻¹ * x * x₁ := by group
  rw [e]
  ring

end Space

end Operators

end Langlands.HarishChandraSchwartz
