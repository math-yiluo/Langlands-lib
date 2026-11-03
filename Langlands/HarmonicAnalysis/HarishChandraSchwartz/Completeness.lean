import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull

/-! # Completeness of the Harish-Chandra Schwartz space

Waldspurger 2003, III.6: `C(G)` with the inductive-limit topology of the levels `C_H` is a
complete locally convex space [Bourbaki, EVT II §4.6, Proposition 9]. This module proves:

- every level `C_H` is complete;
- the inductive limit is strict: `C(G)` induces on each `C_H` its own topology;
- a balanced convex set whose trace on every `C_H` is a neighborhood of `0` is a
  neighborhood of `0` in `C(G)`;
- `C(G)` is complete when some sequence of compact open subgroups is cofinal among all
  compact open subgroups, for example when `G` is nonarchimedean, locally compact and
  first countable.

The uniform structures are those of the topological additive groups `C_H` and `C(G)`.
-/

noncomputable section

open scoped ENNReal NNReal Topology Uniformity Pointwise
open Filter Set Topology

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] {Ξ σ : G → ℝ}

section Uniform

/-- The uniform structure of the topological additive group `C_H`. -/
instance Level.uniformSpace (K : CompactOpenSubgroup G) : UniformSpace (Level Ξ σ K) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance Level.isUniformAddGroup (K : CompactOpenSubgroup G) :
    IsUniformAddGroup (Level Ξ σ K) :=
  isUniformAddGroup_of_addCommGroup

/-- The uniform structure of the topological additive group `C(G)`. -/
instance Space.uniformSpace : UniformSpace (Space Ξ σ) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance Space.isUniformAddGroup : IsUniformAddGroup (Space Ξ σ) :=
  isUniformAddGroup_of_addCommGroup

end Uniform

namespace Level

variable (K : CompactOpenSubgroup G)

/-- Evaluation `f ↦ f(g)` on `C_H`, as a linear map. -/
def evalLinear (g : G) : Level Ξ σ K →ₗ[ℂ] ℂ where
  toFun f := f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every level `C_H` is complete, for positive `Ξ` and nonnegative `σ`. -/
theorem completeSpace (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) :
    CompleteSpace (Level Ξ σ K) := by
  refine ⟨fun {F} hF => ?_⟩
  have hFne : F.NeBot := hF.1
  have hlim : ∀ g, ∃ z : ℂ, Tendsto (fun f : Level Ξ σ K => f g) F (𝓝 z) := fun g =>
    CompleteSpace.complete (hF.map (uniformContinuous_addMonoidHom_of_continuous
      (f := evalLinear K g) (Space.continuous_eval_level hΞ hσ K g)))
  choose φ hφ using hlim
  have key : ∀ r : ℝ, ∀ ε > 0, ∃ A ∈ F, ∀ f ∈ A, nu Ξ σ r (⇑f - φ) ≤ ENNReal.ofReal ε := by
    intro r ε hε
    have hS : {p : Level Ξ σ K × Level Ξ σ K | seminorm K r (p.2 - p.1) < ε} ∈
        𝓤 (Level Ξ σ K) := by
      rw [uniformity_eq_comap_nhds_zero]
      refine ⟨(seminorm K r).ball 0 ε, (Seminorm.continuous_iff hε).mp
        (continuous_seminorm K r), fun p hp => ?_⟩
      exact (Seminorm.mem_ball_zero _).mp hp
    obtain ⟨A, hA, hAA⟩ := (cauchy_iff.mp hF).2 _ hS
    refine ⟨A, hA, fun f hf => ?_⟩
    unfold nu
    refine iSup_le fun g => ?_
    have ht : Tendsto (fun f' : Level Ξ σ K => ‖f g - f' g‖ₑ * weight Ξ σ r g) F
        (𝓝 (‖f g - φ g‖ₑ * weight Ξ σ r g)) :=
      ENNReal.Tendsto.mul_const
        (((continuous_const.sub continuous_id).enorm.tendsto (φ g)).comp (hφ g))
        (Or.inr ENNReal.ofReal_ne_top)
    refine le_of_tendsto ht ?_
    filter_upwards [hA] with f' hf'
    have h1 : seminorm K r (f' - f) < ε := by
      have h := hAA (mk_mem_prod hf hf')
      rw [mem_ofPred_eq] at h
      exact h
    calc ‖f g - f' g‖ₑ * weight Ξ σ r g = ‖(⇑(f' - f)) g‖ₑ * weight Ξ σ r g := by
          rw [enorm_sub_rev]; rfl
      _ ≤ nu Ξ σ r ⇑(f' - f) := enorm_mul_weight_le_nu _ g
      _ ≤ ENNReal.ofReal ε :=
          (ENNReal.le_ofReal_iff_toReal_le (nu_ne_top _ r) hε.le).mpr h1.le
  have hbi : IsBiInvariant K.toSubgroup φ := by
    intro h₁ h₁m h₂ h₂m g
    have he : (fun f : Level Ξ σ K => f (h₁ * g * h₂)) = fun f => f g :=
      funext fun f => isBiInvariant f h₁ h₁m h₂ h₂m g
    refine tendsto_nhds_unique (hφ (h₁ * g * h₂)) ?_
    rw [he]
    exact hφ g
  have hfin : ∀ r, nu Ξ σ r φ < ⊤ := by
    intro r
    obtain ⟨A, hA, hAφ⟩ := key r 1 one_pos
    obtain ⟨f, hf⟩ := hFne.nonempty_of_mem hA
    have e : φ = ⇑f + -(⇑f - φ) := by abel
    rw [e]
    refine (nu_add_le _ _).trans_lt ?_
    rw [nu_neg]
    exact ENNReal.add_lt_top.mpr ⟨nu_lt_top f r, (hAφ f hf).trans_lt ENNReal.ofReal_lt_top⟩
  let x : Level Ξ σ K := (⟨φ, hbi, hfin⟩ : levelSubmodule Ξ σ K.toSubgroup)
  refine ⟨x, tendsto_id'.mp (((withSeminorms K).tendsto_nhds id x).mpr fun r ε hε => ?_)⟩
  obtain ⟨A, hA, hAφ⟩ := key r (ε / 2) (half_pos hε)
  filter_upwards [hA] with f hf
  change (nu Ξ σ r (⇑f - φ)).toReal < ε
  exact (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le (hAφ f hf)).trans_lt (half_lt_self hε)

end Level

namespace Space

/-- `C(G)` carrying the topology of the single seminorm `q`. This auxiliary type is the
target in `continuous_seminorm_of_forall`. -/
def SeminormTop (_q : Seminorm ℂ (Space Ξ σ)) : Type u :=
  Space Ξ σ

namespace SeminormTop

variable (q : Seminorm ℂ (Space Ξ σ))

instance : AddCommGroup (SeminormTop q) :=
  inferInstanceAs (AddCommGroup (Space Ξ σ))

instance : Module ℂ (SeminormTop q) :=
  inferInstanceAs (Module ℂ (Space Ξ σ))

instance : Module ℝ (SeminormTop q) :=
  inferInstanceAs (Module ℝ (Space Ξ σ))

instance : IsScalarTower ℝ ℂ (SeminormTop q) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (Space Ξ σ))

/-- The identity map `C(G) → SeminormTop q`. -/
def ofSpace : Space Ξ σ →ₗ[ℂ] SeminormTop q :=
  LinearMap.id

/-- The seminorm `q` on `SeminormTop q`. -/
def seminorm : Seminorm ℂ (SeminormTop q) :=
  q

/-- The one-member family `{q}`. -/
def seminormFamily : SeminormFamily ℂ (SeminormTop q) Unit :=
  fun _ => seminorm q

/-- The topology of the seminorm `q`. -/
instance topologicalSpace : TopologicalSpace (SeminormTop q) :=
  (seminormFamily q).moduleFilterBasis.topology

theorem withSeminorms : WithSeminorms (seminormFamily q) :=
  ⟨rfl⟩

instance : IsTopologicalAddGroup (SeminormTop q) :=
  (withSeminorms q).isTopologicalAddGroup

instance : ContinuousSMul ℂ (SeminormTop q) :=
  (withSeminorms q).continuousSMul

instance : LocallyConvexSpace ℝ (SeminormTop q) :=
  (withSeminorms q).toLocallyConvexSpace

end SeminormTop

/-- A seminorm on `C(G)` is continuous if its restriction to every level `C_H` is
continuous. -/
theorem continuous_seminorm_of_forall (q : Seminorm ℂ (Space Ξ σ))
    (hq : ∀ K : CompactOpenSubgroup G, Continuous (q.comp (ofLevel K))) : Continuous q := by
  have hT : Continuous (SeminormTop.ofSpace q) := by
    refine (continuous_iff_continuous_comp _).mpr fun K => ?_
    exact (SeminormTop.withSeminorms q).continuous_of_continuous_comp
      ((SeminormTop.ofSpace q) ∘ₗ ofLevel K) fun _ => hq K
  exact ((SeminormTop.withSeminorms q).continuous_seminorm ()).comp hT

/-- A balanced convex subset of `C(G)` whose trace on every level `C_H` is a neighborhood of
`0` in `C_H` is a neighborhood of `0` in `C(G)`. -/
theorem mem_nhds_zero_of_forall [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]
    {U : Set (Space Ξ σ)} (hb : Balanced ℂ U) (hc : Convex ℝ U)
    (hU : ∀ K : CompactOpenSubgroup G, ofLevel K ⁻¹' U ∈ 𝓝 0) : U ∈ 𝓝 (0 : Space Ξ σ) := by
  have h0 : (0 : Space Ξ σ) ∈ U := by
    obtain ⟨K⟩ := ‹Nonempty (CompactOpenSubgroup G)›
    simpa using mem_of_mem_nhds (hU K)
  have ha : Absorbent ℝ U := by
    intro x
    obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem x)
    let f : Level Ξ σ K := (⟨x, hK⟩ : levelSubmodule Ξ σ K.toSubgroup)
    have : ContinuousSMul ℝ (Level Ξ σ K) := IsScalarTower.continuousSMul ℂ
    have hf := absorbent_nhds_zero (𝕜 := ℝ) (hU K) f
    unfold Absorbs at hf ⊢
    refine hf.mono fun a ha => ?_
    rintro _ rfl
    obtain ⟨w, hw, hwf⟩ := ha rfl
    refine ⟨ofLevel K w, hw, ?_⟩
    dsimp only at hwf ⊢
    rw [← LinearMap.map_smul_of_tower, hwf]
    exact Space.ext fun _ => rfl
  let p : Seminorm ℂ (Space Ξ σ) := gaugeSeminorm hb hc ha
  have hp : Continuous p := continuous_seminorm_of_forall p fun K => by
    refine Seminorm.continuous' (r := 1) ?_
    refine mem_of_superset (hU K) fun f hf => ?_
    rw [Seminorm.mem_closedBall_zero]
    exact gauge_le_one_of_mem hf
  have hball : {x | p x < 1} ∈ 𝓝 (0 : Space Ξ σ) :=
    (isOpen_lt hp continuous_const).mem_nhds (by simp)
  exact mem_of_superset hball (setOfPred_gauge_lt_one_subset_self hc h0 ha)

/-- Every `f ∈ C(G)` has all seminorms `ν_r(f)` finite. -/
theorem nu_lt_top (f : Space Ξ σ) (r : ℝ) : nu Ξ σ r f < ⊤ := by
  have h : ∀ r, nu Ξ σ r f < ⊤ :=
    Submodule.iSup_induction (fun K : CompactOpenSubgroup G => levelSubmodule Ξ σ K.toSubgroup)
      (motive := fun φ => ∀ r, nu Ξ σ r φ < ⊤) (coe_mem f) (fun _ _ hφ => hφ.2)
      (fun _ => by simp) fun φ ψ hφ hψ r =>
        (nu_add_le φ ψ).trans_lt (ENNReal.add_lt_top.mpr ⟨hφ r, hψ r⟩)
  exact h r

theorem nu_ne_top (f : Space Ξ σ) (r : ℝ) : nu Ξ σ r f ≠ ⊤ :=
  (nu_lt_top f r).ne

variable (Ξ σ) in
/-- The seminorm `ν_r` on `C(G)`. -/
def seminorm (r : ℝ) : Seminorm ℂ (Space Ξ σ) :=
  Seminorm.of (fun f => (nu Ξ σ r f).toReal)
    (fun f₁ f₂ => by
      change (nu Ξ σ r (⇑f₁ + ⇑f₂)).toReal ≤ (nu Ξ σ r f₁).toReal + (nu Ξ σ r f₂).toReal
      rw [← ENNReal.toReal_add (nu_ne_top f₁ r) (nu_ne_top f₂ r)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨nu_ne_top f₁ r, nu_ne_top f₂ r⟩)
        (nu_add_le _ _))
    (fun c f => by
      change (nu Ξ σ r (c • ⇑f)).toReal = ‖c‖ * (nu Ξ σ r f).toReal
      rw [nu_smul, ENNReal.toReal_mul, toReal_enorm])

@[simp] theorem seminorm_apply (r : ℝ) (f : Space Ξ σ) :
    seminorm Ξ σ r f = (nu Ξ σ r f).toReal :=
  rfl

/-- The seminorms `ν_r` are continuous on `C(G)`. -/
theorem continuous_seminorm (r : ℝ) : Continuous (seminorm Ξ σ r) :=
  continuous_seminorm_of_forall _ fun K => Level.continuous_seminorm K r

/-- Strictness of the inductive limit at `0`: every neighborhood of `0` in `C_H` is the
trace of a neighborhood of `0` in `C(G)`. -/
theorem comap_nhds_zero_le (K : CompactOpenSubgroup G) :
    (𝓝 (0 : Space Ξ σ)).comap (ofLevel K) ≤ 𝓝 0 := by
  intro W hW
  obtain ⟨s, ε, hε, hsub⟩ := ((Level.withSeminorms K).mem_nhds_iff 0 W).mp hW
  refine ⟨⋂ r ∈ s, (seminorm Ξ σ r).ball 0 ε, (biInter_finset_mem s).mpr fun r _ =>
    (Seminorm.continuous_iff hε).mp (continuous_seminorm r), fun f hf => hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine Seminorm.finset_sup_apply_lt hε fun r hr => ?_
  have h := mem_iInter₂.mp hf r hr
  rw [Seminorm.mem_ball_zero] at h
  exact h

/-- The inductive limit is strict: `C(G)` induces on each level `C_H` its own topology. -/
theorem isInducing_ofLevel (K : CompactOpenSubgroup G) :
    IsInducing (ofLevel (Ξ := Ξ) (σ := σ) K) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm ?_ (comap_nhds_zero_le K)
  have h := (continuous_ofLevel (Ξ := Ξ) (σ := σ) K).tendsto 0
  rw [map_zero] at h
  exact tendsto_iff_comap.mp h

end Space

/-- The balanced core of a convex set containing `0` in a complex vector space is convex. -/
theorem convex_balancedCore {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] {s : Set E} (hs : Convex ℝ s) (h0 : (0 : E) ∈ s) :
    Convex ℝ (balancedCore ℂ s) := by
  rw [balancedCore_eq_iInter h0]
  refine convex_iInter fun r => convex_iInter fun _ => ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hs hx hy ha hb hab, ?_⟩
  simp only [smul_add, smul_comm r a, smul_comm r b]

section Sequence

variable [IsTopologicalGroup G]

/-- The running intersections `H 0 ∩ ⋯ ∩ H n` of a sequence of compact open subgroups. -/
def CompactOpenSubgroup.accumulate (H : ℕ → CompactOpenSubgroup G) : ℕ → CompactOpenSubgroup G
  | 0 => H 0
  | n + 1 => (CompactOpenSubgroup.accumulate H n).inf (H (n + 1))

theorem CompactOpenSubgroup.accumulate_le (H : ℕ → CompactOpenSubgroup G) (n : ℕ) :
    (CompactOpenSubgroup.accumulate H n).toSubgroup ≤ (H n).toSubgroup := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact CompactOpenSubgroup.inf_le_right _ _

theorem CompactOpenSubgroup.accumulate_antitone (H : ℕ → CompactOpenSubgroup G) {m n : ℕ}
    (h : m ≤ n) :
    (CompactOpenSubgroup.accumulate H n).toSubgroup ≤
      (CompactOpenSubgroup.accumulate H m).toSubgroup := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (CompactOpenSubgroup.inf_le_left _ _).trans ih

/-- In a nonarchimedean, weakly locally compact, first countable group some sequence of
compact open subgroups is cofinal: every compact open subgroup contains one of them. -/
theorem exists_seq_compactOpenSubgroup_le {G : Type u} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] [FirstCountableTopology G] :
    ∃ H : ℕ → CompactOpenSubgroup G,
      ∀ K : CompactOpenSubgroup G, ∃ n, (H n).toSubgroup ≤ K.toSubgroup := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  have hK : ∀ n, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U n :=
    fun n => compactOpenSubgroupBasis G (U n) (hU.mem n)
  choose K hKc hKU using hK
  refine ⟨fun n => ⟨K n, hKc n⟩, fun L => ?_⟩
  obtain ⟨n, -, hn⟩ := hU.toHasBasis.mem_iff.mp L.1.mem_nhds_one
  exact ⟨n, fun x hx => hn (hKU n hx)⟩

end Sequence

namespace Space

/-- Waldspurger III.6: `C(G)` is complete, for positive `Ξ` and nonnegative `σ`, when some
sequence of compact open subgroups is cofinal among all compact open subgroups. The proof is
the classical argument for strict inductive limits of sequences of complete spaces
(Waldspurger cites [Bourbaki, EVT II §4.6, Proposition 9]). -/
theorem completeSpace [IsTopologicalGroup G] (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hH : ∃ H : ℕ → CompactOpenSubgroup G,
      ∀ K : CompactOpenSubgroup G, ∃ n, (H n).toSubgroup ≤ K.toSubgroup) :
    CompleteSpace (Space Ξ σ) := by
  obtain ⟨H₀, hH₀⟩ := hH
  set H := CompactOpenSubgroup.accumulate H₀
  have hHle : ∀ K : CompactOpenSubgroup G, ∃ n, (H n).toSubgroup ≤ K.toSubgroup := fun K =>
    let ⟨n, hn⟩ := hH₀ K
    ⟨n, (CompactOpenSubgroup.accumulate_le H₀ n).trans hn⟩
  have hanti : ∀ {m n : ℕ}, m ≤ n → (H n).toSubgroup ≤ (H m).toSubgroup := fun h =>
    CompactOpenSubgroup.accumulate_antitone H₀ h
  have : Nonempty (CompactOpenSubgroup G) := ⟨H₀ 0⟩
  -- the levels `C_{H n}` as subspaces of `C(G)`
  let E : ℕ → Submodule ℂ (Space Ξ σ) := fun n =>
    (levelSubmodule Ξ σ (H n).toSubgroup).comap toFunLinear
  have hEmono : ∀ {m n : ℕ}, m ≤ n → E m ≤ E n := fun h _ hx =>
    levelSubmodule_antitone Ξ σ (hanti h) hx
  have hEall : ∀ x : Space Ξ σ, ∃ n, x ∈ E n := fun x => by
    obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem x)
    obtain ⟨n, hn⟩ := hHle K
    exact ⟨n, levelSubmodule_antitone Ξ σ hn hK⟩
  have hErange : ∀ (K : CompactOpenSubgroup G) (n : ℕ), (H n).toSubgroup ≤ K.toSubgroup →
      ∀ f : Level Ξ σ K, ofLevel K f ∈ E n := fun K n hn f =>
    levelSubmodule_antitone Ξ σ hn (f : levelSubmodule Ξ σ K.toSubgroup).2
  have hEiff : ∀ (n : ℕ) (x : Space Ξ σ), x ∈ E n →
      x ∈ range (ofLevel (Ξ := Ξ) (σ := σ) (H n)) := fun n x hx =>
    ⟨(⟨x, hx⟩ : levelSubmodule Ξ σ (H n).toSubgroup), Space.ext fun _ => rfl⟩
  refine ⟨fun {F} hF => ?_⟩
  have hFne : F.NeBot := hF.1
  -- the filter `F + 𝓝 0`
  let Gf : Filter (Space Ξ σ) := map (fun p : Space Ξ σ × Space Ξ σ => p.1 + p.2) (F ×ˢ 𝓝 0)
  have hG : Cauchy Gf := (hF.prod cauchy_nhds).map uniformContinuous_add
  have hFG : F ≤ Gf := by
    intro S hS
    obtain ⟨A, hA, V, hV, hAV⟩ := mem_prod_iff.mp (mem_map.mp hS)
    refine mem_of_superset hA fun a ha => ?_
    have h := hAV (mk_mem_prod ha (mem_of_mem_nhds hV))
    simpa using h
  -- the sets of `F + 𝓝 0` all meet one level
  obtain ⟨n, hn⟩ : ∃ n, (comap (ofLevel (Ξ := Ξ) (σ := σ) (H n)) Gf).NeBot := by
    by_contra hcon
    push Not at hcon
    have hbad : ∀ n, ∃ A ∈ F, ∃ V ∈ 𝓝 (0 : Space Ξ σ), ∀ a ∈ A, ∀ v ∈ V, a + v ∉ E n := by
      intro n
      have h := comap_eq_bot_iff_compl_range.mp (hcon n)
      obtain ⟨A, hA, V, hV, hAV⟩ := mem_prod_iff.mp (mem_map.mp h)
      exact ⟨A, hA, V, hV, fun a ha v hv hE => hAV (mk_mem_prod ha hv) (hEiff n _ hE)⟩
    choose A hA V hV hAV using hbad
    have hB : ∀ n, ∃ B ⊆ V n, B ∈ 𝓝 (0 : Space Ξ σ) ∧ Balanced ℂ B ∧ Convex ℝ B := by
      intro n
      obtain ⟨C, ⟨hC0, hCc⟩, hCV⟩ :=
        (LocallyConvexSpace.convex_basis_zero ℝ (Space Ξ σ)).mem_iff.mp (hV n)
      exact ⟨balancedCore ℂ C, (balancedCore_subset C).trans hCV,
        balancedCore_mem_nhds_zero hC0, balancedCore_balanced C,
        convex_balancedCore hCc (mem_of_mem_nhds hC0)⟩
    choose B hBV hB0 hBb hBc using hB
    let W : ℕ → Set (Space Ξ σ) := fun n => ⋂ k ∈ Iic n, B k
    have hW0 : ∀ n, W n ∈ 𝓝 (0 : Space Ξ σ) := fun n =>
      (biInter_mem (finite_Iic n)).mpr fun k _ => hB0 k
    have hWb : ∀ n, Balanced ℂ (W n) := fun n => balanced_iInter₂ fun k _ => hBb k
    have hWc : ∀ n, Convex ℝ (W n) := fun n => convex_iInter₂ fun k _ => hBc k
    have hWV : ∀ n, W n ⊆ V n := fun n =>
      (biInter_subset_of_mem (mem_Iic.mpr le_rfl)).trans (hBV n)
    have hWanti : ∀ {m n : ℕ}, m ≤ n → W n ⊆ W m := fun h =>
      biInter_subset_biInter_left (Iic_subset_Iic.mpr h)
    -- `U = ⋂_N (C_{H N} + W N)`
    let U : Set (Space Ξ σ) := ⋂ N, {x | ∃ e ∈ E N, x - e ∈ W N}
    have hUb : Balanced ℂ U := balanced_iInter fun N a ha => by
      rintro _ ⟨x, ⟨e, he, hxe⟩, rfl⟩
      exact ⟨a • e, (E N).smul_mem a he, by rw [← smul_sub]; exact (hWb N).smul_mem ha hxe⟩
    have hUc : Convex ℝ U := convex_iInter fun N => by
      rintro x ⟨e, he, hxe⟩ y ⟨e', he', hye'⟩ a b ha hb hab
      refine ⟨a • e + b • e',
        (E N).add_mem ((E N).smul_of_tower_mem a he) ((E N).smul_of_tower_mem b he'), ?_⟩
      have e1 : a • x + b • y - (a • e + b • e') = a • (x - e) + b • (y - e') := by
        simp only [smul_sub]; abel
      rw [e1]
      exact hWc N hxe hye' ha hb hab
    have hU : U ∈ 𝓝 (0 : Space Ξ σ) := by
      refine mem_nhds_zero_of_forall hUb hUc fun K => ?_
      obtain ⟨m, hm⟩ := hHle K
      have h1 : ofLevel K ⁻¹' W m ∈ 𝓝 (0 : Level Ξ σ K) := by
        have h := (continuous_ofLevel (Ξ := Ξ) (σ := σ) K).tendsto 0
        rw [map_zero] at h
        exact h (hW0 m)
      refine mem_of_superset h1 fun f hf => mem_iInter.mpr fun N => ?_
      rcases le_or_gt m N with hmN | hNm
      · exact ⟨ofLevel K f, hEmono hmN (hErange K m hm f), by
          rw [sub_self]; exact mem_of_mem_nhds (hW0 N)⟩
      · exact ⟨0, (E N).zero_mem, by rw [sub_zero]; exact hWanti hNm.le hf⟩
    have hUunif : {p : Space Ξ σ × Space Ξ σ | p.2 - p.1 ∈ U} ∈ 𝓤 (Space Ξ σ) := by
      rw [uniformity_eq_comap_nhds_zero]
      exact preimage_mem_comap hU
    obtain ⟨C, hC, hCC⟩ := (cauchy_iff.mp hF).2 _ hUunif
    obtain ⟨a, ha⟩ := hFne.nonempty_of_mem hC
    obtain ⟨k, hk⟩ := hEall a
    obtain ⟨y, hyC, hyA⟩ := hFne.nonempty_of_mem (inter_mem hC (hA k))
    have hay : a - y ∈ U := hCC (mk_mem_prod hyC ha)
    obtain ⟨e, he, hv⟩ := mem_iInter.mp hay k
    refine hAV k y hyA _ (hWV k hv) ?_
    have e2 : y + (a - y - e) = a - e := by abel
    rw [e2]
    exact (E k).sub_mem hk he
  -- the trace of `F + 𝓝 0` on `C_{H n}` converges
  have := hn
  have hUI : IsUniformInducing (ofLevel (Ξ := Ξ) (σ := σ) (H n)) :=
    AddMonoidHom.isUniformInducing_of_isInducing (isInducing_ofLevel (H n))
  have hGc : Cauchy (comap (ofLevel (Ξ := Ξ) (σ := σ) (H n)) Gf) :=
    hG.comap hUI.comap_uniformity.le
  have := Level.completeSpace (H n) hΞ hσ
  obtain ⟨φ, hφ⟩ := CompleteSpace.complete hGc
  have hcl : ClusterPt (ofLevel (H n) φ) Gf := by
    have h1 : map (ofLevel (H n)) (comap (ofLevel (Ξ := Ξ) (σ := σ) (H n)) Gf) ≤
        𝓝 (ofLevel (H n) φ) ⊓ Gf :=
      le_inf ((map_mono hφ).trans ((continuous_ofLevel (H n)).tendsto φ)) map_comap_le
    exact (hn.map _).mono h1
  exact ⟨_, hFG.trans (le_nhds_of_cauchy_adhp hG hcl)⟩

/-- `C(G)` is complete when `G` is nonarchimedean, weakly locally compact and first countable
(for example `G(F)` for a reductive group over a nonarchimedean local field `F`). -/
theorem completeSpace_of_firstCountable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    [FirstCountableTopology G] (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) :
    CompleteSpace (Space Ξ σ) :=
  completeSpace hΞ hσ exists_seq_compactOpenSubgroup_le

end Space

end Langlands.HarishChandraSchwartz
