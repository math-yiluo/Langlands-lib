import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Harish-Chandra Schwartz spaces for arbitrary weights

This module carries out the construction of Waldspurger 2003, III.6, for an
arbitrary topological group `G` and arbitrary real-valued weights `Ξ` and `σ`.
The source weights (the spherical function `Ξ` of II.1 and the height
`σ = log ‖·‖` of I.1) are realized elsewhere; nothing here assumes their
properties.
-/

noncomputable section

open scoped ENNReal NNReal Topology
open TopologicalSpace

namespace Langlands.HarishChandraSchwartz

universe u

section BiInvariant

variable {G : Type u} [Group G]

/-- A function on `G` is bi-invariant under `H` if `f (h₁ * g * h₂) = f g` for all
`h₁ h₂ ∈ H`; this is membership in Waldspurger's `C(H \ G / H)`. -/
def IsBiInvariant (H : Subgroup G) (f : G → ℂ) : Prop :=
  ∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ g, f (h₁ * g * h₂) = f g

theorem IsBiInvariant.mono {H H' : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f)
    (hH : H' ≤ H) : IsBiInvariant H' f :=
  fun h₁ h₁m h₂ h₂m g => hf h₁ (hH h₁m) h₂ (hH h₂m) g

theorem isBiInvariant_zero (H : Subgroup G) : IsBiInvariant H (0 : G → ℂ) :=
  fun _ _ _ _ _ => rfl

theorem IsBiInvariant.add {H : Subgroup G} {f₁ f₂ : G → ℂ} (h₁ : IsBiInvariant H f₁)
    (h₂ : IsBiInvariant H f₂) : IsBiInvariant H (f₁ + f₂) :=
  fun a ha b hb g => by simp only [Pi.add_apply, h₁ a ha b hb g, h₂ a ha b hb g]

theorem IsBiInvariant.smul {H : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f) (c : ℂ) :
    IsBiInvariant H (c • f) :=
  fun a ha b hb g => by simp only [Pi.smul_apply, hf a ha b hb g]

end BiInvariant

section Weights

variable {G : Type u}

/-- The weight `Ξ(g)⁻¹ (1 + σ(g))^r` of Waldspurger's seminorm `ν_r`, as an extended
nonnegative real. For positive `Ξ` and nonnegative `σ` it is the real weight itself. -/
def weight (Ξ σ : G → ℝ) (r : ℝ) (g : G) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ξ g)⁻¹ * (1 + σ g) ^ r)

/-- Waldspurger's seminorm `ν_r(f) = sup_g |f(g)| Ξ(g)⁻¹ (1 + σ(g))^r` (III.6),
with value `∞` when the supremum is infinite. -/
def nu (Ξ σ : G → ℝ) (r : ℝ) (f : G → ℂ) : ℝ≥0∞ :=
  ⨆ g, ‖f g‖ₑ * weight Ξ σ r g

variable {Ξ σ : G → ℝ} {r : ℝ}

theorem enorm_mul_weight_le_nu (f : G → ℂ) (g : G) :
    ‖f g‖ₑ * weight Ξ σ r g ≤ nu Ξ σ r f :=
  le_iSup (fun g => ‖f g‖ₑ * weight Ξ σ r g) g

@[simp] theorem nu_zero : nu Ξ σ r (0 : G → ℂ) = 0 := by
  simp [nu]

theorem nu_add_le (f₁ f₂ : G → ℂ) : nu Ξ σ r (f₁ + f₂) ≤ nu Ξ σ r f₁ + nu Ξ σ r f₂ := by
  refine iSup_le fun g => ?_
  calc ‖(f₁ + f₂) g‖ₑ * weight Ξ σ r g
      ≤ (‖f₁ g‖ₑ + ‖f₂ g‖ₑ) * weight Ξ σ r g := by
        gcongr
        exact enorm_add_le _ _
    _ = ‖f₁ g‖ₑ * weight Ξ σ r g + ‖f₂ g‖ₑ * weight Ξ σ r g := add_mul _ _ _
    _ ≤ nu Ξ σ r f₁ + nu Ξ σ r f₂ :=
        add_le_add (enorm_mul_weight_le_nu f₁ g) (enorm_mul_weight_le_nu f₂ g)

theorem nu_smul (c : ℂ) (f : G → ℂ) : nu Ξ σ r (c • f) = ‖c‖ₑ * nu Ξ σ r f := by
  simp only [nu, Pi.smul_apply, smul_eq_mul, enorm_mul, ENNReal.mul_iSup, mul_assoc]

theorem nu_neg (f : G → ℂ) : nu Ξ σ r (-f) = nu Ξ σ r f := by
  simp [nu]

/-- For nonnegative `σ`, the weights increase with `r`. -/
theorem weight_mono (hσ : ∀ g, 0 ≤ σ g) {r s : ℝ} (hrs : r ≤ s) (g : G) :
    weight Ξ σ r g ≤ weight Ξ σ s g := by
  unfold weight
  have hb : 1 ≤ 1 + σ g := le_add_of_nonneg_right (hσ g)
  have hrs' : (1 + σ g) ^ r ≤ (1 + σ g) ^ s := Real.rpow_le_rpow_of_exponent_le hb hrs
  rcases le_or_gt 0 (Ξ g)⁻¹ with h | h
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hrs' h)
  · have : (Ξ g)⁻¹ * (1 + σ g) ^ r ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h.le (Real.rpow_nonneg (by linarith) r)
    rw [ENNReal.ofReal_of_nonpos this]
    exact bot_le

/-- For nonnegative `σ`, the seminorms `ν_r` increase with `r`. -/
theorem nu_mono (hσ : ∀ g, 0 ≤ σ g) {r s : ℝ} (hrs : r ≤ s) (f : G → ℂ) :
    nu Ξ σ r f ≤ nu Ξ σ s f :=
  iSup_mono fun g => by
    gcongr
    exact weight_mono hσ hrs g

/-- For positive `Ξ` and nonnegative `σ`, a finite `ν_r(f)` bounds the values of `f`:
`|f(g)| ≤ ν_r(f) Ξ(g) (1 + σ(g))^(-r)`. -/
theorem norm_le_of_nu (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) {f : G → ℂ}
    (hf : nu Ξ σ r f ≠ ⊤) (g : G) :
    ‖f g‖ ≤ (nu Ξ σ r f).toReal * (Ξ g * (1 + σ g) ^ (-r)) := by
  have hb : 0 < 1 + σ g := by linarith [hσ g]
  have hw : 0 < (Ξ g)⁻¹ * (1 + σ g) ^ r := mul_pos (inv_pos.mpr (hΞ g)) (Real.rpow_pos_of_pos hb r)
  have hle := enorm_mul_weight_le_nu (Ξ := Ξ) (σ := σ) (r := r) f g
  rw [weight, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at hle
  have hle' := (ENNReal.ofReal_le_iff_le_toReal hf).mp hle
  have hinv : (Ξ g * (1 + σ g) ^ (-r)) * ((Ξ g)⁻¹ * (1 + σ g) ^ r) = 1 := by
    rw [Real.rpow_neg hb.le]
    field_simp [(hΞ g).ne', (Real.rpow_pos_of_pos hb r).ne']
  calc ‖f g‖ = ‖f g‖ * ((Ξ g)⁻¹ * (1 + σ g) ^ r) * (Ξ g * (1 + σ g) ^ (-r)) := by
        rw [mul_assoc, mul_comm ((Ξ g)⁻¹ * _), hinv, mul_one]
    _ ≤ (nu Ξ σ r f).toReal * (Ξ g * (1 + σ g) ^ (-r)) := by
        gcongr
        exact mul_nonneg (hΞ g).le (Real.rpow_nonneg hb.le _)

end Weights

section Levels

variable {G : Type u} [Group G] (Ξ σ : G → ℝ)

/-- Waldspurger's level space `C_H`: functions bi-invariant under `H` all of whose
seminorms `ν_r`, `r ∈ ℝ`, are finite. -/
def levelSubmodule (H : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {f | IsBiInvariant H f ∧ ∀ r : ℝ, nu Ξ σ r f < ⊤}
  zero_mem' := ⟨isBiInvariant_zero H, fun r => by simp⟩
  add_mem' {f₁ f₂} h₁ h₂ := ⟨h₁.1.add h₂.1, fun r =>
    lt_of_le_of_lt (nu_add_le f₁ f₂) (ENNReal.add_lt_top.mpr ⟨h₁.2 r, h₂.2 r⟩)⟩
  smul_mem' c f hf := ⟨hf.1.smul c, fun r => by
    rw [nu_smul]
    exact ENNReal.mul_lt_top enorm_lt_top (hf.2 r)⟩

theorem mem_levelSubmodule_iff {H : Subgroup G} {f : G → ℂ} :
    f ∈ levelSubmodule Ξ σ H ↔ IsBiInvariant H f ∧ ∀ r : ℝ, nu Ξ σ r f < ⊤ :=
  Iff.rfl

theorem levelSubmodule_antitone {H H' : Subgroup G} (hH : H' ≤ H) :
    levelSubmodule Ξ σ H ≤ levelSubmodule Ξ σ H' :=
  fun _ hf => ⟨hf.1.mono hH, hf.2⟩

end Levels

section Spaces

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The compact open subgroups of `G`, as open subgroups whose underlying set is compact. -/
abbrev CompactOpenSubgroup : Type u :=
  {K : OpenSubgroup G // IsCompact (K : Set G)}

variable {G}

/-- The underlying subgroup of a compact open subgroup. -/
abbrev CompactOpenSubgroup.toSubgroup (K : CompactOpenSubgroup G) : Subgroup G :=
  K.1.toSubgroup

/-- The intersection of two compact open subgroups. -/
def CompactOpenSubgroup.inf [IsTopologicalGroup G] (K L : CompactOpenSubgroup G) :
    CompactOpenSubgroup G :=
  ⟨K.1 ⊓ L.1, by
    rw [OpenSubgroup.coe_inf]
    exact K.2.inter_right L.1.isClosed⟩

theorem CompactOpenSubgroup.inf_le_left [IsTopologicalGroup G] (K L : CompactOpenSubgroup G) :
    (K.inf L).toSubgroup ≤ K.toSubgroup :=
  OpenSubgroup.toSubgroup_le.mpr _root_.inf_le_left

theorem CompactOpenSubgroup.inf_le_right [IsTopologicalGroup G] (K L : CompactOpenSubgroup G) :
    (K.inf L).toSubgroup ≤ L.toSubgroup :=
  OpenSubgroup.toSubgroup_le.mpr _root_.inf_le_right

variable (Ξ σ : G → ℝ)

/-- Waldspurger's Harish-Chandra Schwartz space `C(G) = ⋃_H C_H`, with `H` running over
the compact open subgroups of `G`, as the supremum of the level submodules. -/
def schwartzSubmodule : Submodule ℂ (G → ℂ) :=
  ⨆ K : CompactOpenSubgroup G, levelSubmodule Ξ σ K.toSubgroup

theorem levelSubmodule_le_schwartzSubmodule (K : CompactOpenSubgroup G) :
    levelSubmodule Ξ σ K.toSubgroup ≤ schwartzSubmodule Ξ σ :=
  le_iSup (fun K : CompactOpenSubgroup G => levelSubmodule Ξ σ K.toSubgroup) K

/-- When `G` has a compact open subgroup, `C(G)` is the union of the levels `C_H`. -/
theorem mem_schwartzSubmodule_iff [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]
    {f : G → ℂ} :
    f ∈ schwartzSubmodule Ξ σ ↔ ∃ K : CompactOpenSubgroup G, f ∈ levelSubmodule Ξ σ K.toSubgroup := by
  refine Submodule.mem_iSup_of_directed _ ?_
  intro K L
  exact ⟨K.inf L, levelSubmodule_antitone Ξ σ (K.inf_le_left L),
    levelSubmodule_antitone Ξ σ (K.inf_le_right L)⟩

/-- The level space `C_H` as a type, for a compact open subgroup `H`. -/
def Level (K : CompactOpenSubgroup G) : Type u :=
  levelSubmodule Ξ σ K.toSubgroup

/-- The Harish-Chandra Schwartz space `C(G)` as a type. -/
def Space : Type u :=
  schwartzSubmodule Ξ σ

namespace Level

variable {Ξ σ} (K : CompactOpenSubgroup G)

instance : AddCommGroup (Level Ξ σ K) :=
  inferInstanceAs (AddCommGroup (levelSubmodule Ξ σ K.toSubgroup))

instance : Module ℂ (Level Ξ σ K) :=
  inferInstanceAs (Module ℂ (levelSubmodule Ξ σ K.toSubgroup))

instance : Module ℝ (Level Ξ σ K) :=
  inferInstanceAs (Module ℝ (levelSubmodule Ξ σ K.toSubgroup))

instance : IsScalarTower ℝ ℂ (Level Ξ σ K) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (levelSubmodule Ξ σ K.toSubgroup))

instance : FunLike (Level Ξ σ K) G ℂ where
  coe f := (f : levelSubmodule Ξ σ K.toSubgroup).1
  coe_injective _ _ h := Subtype.ext h

variable {K}

@[ext] theorem ext {f₁ f₂ : Level Ξ σ K} (h : ∀ g, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext _ _ h

@[simp] theorem coe_zero : ((0 : Level Ξ σ K) : G → ℂ) = 0 := rfl

@[simp] theorem coe_add (f₁ f₂ : Level Ξ σ K) : ((f₁ + f₂ : Level Ξ σ K) : G → ℂ) = f₁ + f₂ :=
  rfl

@[simp] theorem coe_smul (c : ℂ) (f : Level Ξ σ K) : ((c • f : Level Ξ σ K) : G → ℂ) = c • f :=
  rfl

theorem isBiInvariant (f : Level Ξ σ K) : IsBiInvariant K.toSubgroup f :=
  (f : levelSubmodule Ξ σ K.toSubgroup).2.1

theorem nu_lt_top (f : Level Ξ σ K) (r : ℝ) : nu Ξ σ r f < ⊤ :=
  (f : levelSubmodule Ξ σ K.toSubgroup).2.2 r

theorem nu_ne_top (f : Level Ξ σ K) (r : ℝ) : nu Ξ σ r f ≠ ⊤ :=
  (nu_lt_top f r).ne

variable (K)

/-- The norm `ν_r` on the level `C_H`. -/
def seminorm (r : ℝ) : Seminorm ℂ (Level Ξ σ K) :=
  Seminorm.of (fun f => (nu Ξ σ r f).toReal)
    (fun f₁ f₂ => by
      change (nu Ξ σ r (⇑f₁ + ⇑f₂)).toReal ≤ (nu Ξ σ r f₁).toReal + (nu Ξ σ r f₂).toReal
      rw [← ENNReal.toReal_add (nu_ne_top f₁ r) (nu_ne_top f₂ r)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨nu_ne_top f₁ r, nu_ne_top f₂ r⟩)
        (nu_add_le _ _))
    (fun c f => by
      change (nu Ξ σ r (c • ⇑f)).toReal = ‖c‖ * (nu Ξ σ r f).toReal
      rw [nu_smul, ENNReal.toReal_mul, toReal_enorm])

@[simp] theorem seminorm_apply (r : ℝ) (f : Level Ξ σ K) :
    seminorm K r f = (nu Ξ σ r f).toReal :=
  rfl

/-- The family `(ν_r)_{r ∈ ℝ}` defining the topology of `C_H`. -/
def seminormFamily : SeminormFamily ℂ (Level Ξ σ K) ℝ :=
  fun r => seminorm K r

/-- The topology of `C_H` defined by the norms `ν_r`, `r ∈ ℝ` (Waldspurger III.6). -/
instance topologicalSpace : TopologicalSpace (Level Ξ σ K) :=
  (seminormFamily K).moduleFilterBasis.topology

theorem withSeminorms : WithSeminorms (seminormFamily (Ξ := Ξ) (σ := σ) K) :=
  ⟨rfl⟩

instance : IsTopologicalAddGroup (Level Ξ σ K) :=
  (withSeminorms K).isTopologicalAddGroup

instance : ContinuousSMul ℂ (Level Ξ σ K) :=
  (withSeminorms K).continuousSMul

instance : LocallyConvexSpace ℝ (Level Ξ σ K) :=
  (withSeminorms K).toLocallyConvexSpace

theorem continuous_seminorm (r : ℝ) : Continuous (seminorm (Ξ := Ξ) (σ := σ) K r) :=
  (withSeminorms K).continuous_seminorm r

end Level

namespace Space

variable {Ξ σ}

instance : AddCommGroup (Space Ξ σ) :=
  inferInstanceAs (AddCommGroup (schwartzSubmodule Ξ σ))

instance : Module ℂ (Space Ξ σ) :=
  inferInstanceAs (Module ℂ (schwartzSubmodule Ξ σ))

instance : Module ℝ (Space Ξ σ) :=
  inferInstanceAs (Module ℝ (schwartzSubmodule Ξ σ))

instance : IsScalarTower ℝ ℂ (Space Ξ σ) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (schwartzSubmodule Ξ σ))

instance : FunLike (Space Ξ σ) G ℂ where
  coe f := (f : schwartzSubmodule Ξ σ).1
  coe_injective _ _ h := Subtype.ext h

@[ext] theorem ext {f₁ f₂ : Space Ξ σ} (h : ∀ g, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext _ _ h

@[simp] theorem coe_zero : ((0 : Space Ξ σ) : G → ℂ) = 0 := rfl

@[simp] theorem coe_add (f₁ f₂ : Space Ξ σ) : ((f₁ + f₂ : Space Ξ σ) : G → ℂ) = f₁ + f₂ :=
  rfl

@[simp] theorem coe_smul (c : ℂ) (f : Space Ξ σ) : ((c • f : Space Ξ σ) : G → ℂ) = c • f :=
  rfl

theorem coe_mem (f : Space Ξ σ) : (f : G → ℂ) ∈ schwartzSubmodule Ξ σ :=
  (f : schwartzSubmodule Ξ σ).2

/-- The inclusion `C_H → C(G)` of a level into the Harish-Chandra Schwartz space. -/
def ofLevel (K : CompactOpenSubgroup G) : Level Ξ σ K →ₗ[ℂ] Space Ξ σ :=
  Submodule.inclusion (levelSubmodule_le_schwartzSubmodule Ξ σ K)

@[simp] theorem coe_ofLevel (K : CompactOpenSubgroup G) (f : Level Ξ σ K) :
    ((ofLevel K f : Space Ξ σ) : G → ℂ) = f :=
  rfl

variable (Ξ σ) in
/-- The inductive-limit topology in the category of topological spaces: the finest topology
making every inclusion `C_H → C(G)` continuous. It need not be a vector-space topology. -/
@[instance_reducible]
def originalTop : TopologicalSpace (Space Ξ σ) :=
  ⨆ K : CompactOpenSubgroup G, coinduced (ofLevel (Ξ := Ξ) (σ := σ) K) inferInstance

variable (Ξ σ) in
/-- The topology of `C(G)`: the locally convex inductive limit of the topologies of the
levels `C_H` (Waldspurger III.6, citing Bourbaki EVT II §4.6). It is the infimum of all
locally convex vector-space topologies coarser than `originalTop`. -/
instance topologicalSpace : TopologicalSpace (Space Ξ σ) :=
  sInf {t : TopologicalSpace (Space Ξ σ) | originalTop Ξ σ ≤ t ∧
    @IsTopologicalAddGroup (Space Ξ σ) t _ ∧
    @ContinuousSMul ℂ (Space Ξ σ) _ _ t ∧
    @LocallyConvexSpace ℝ (Space Ξ σ) _ _ _ _ t}

instance : IsTopologicalAddGroup (Space Ξ σ) :=
  isTopologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ ↦ ht

instance : ContinuousSMul ℂ (Space Ξ σ) :=
  continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ ↦ ht

instance : LocallyConvexSpace ℝ (Space Ξ σ) :=
  .sInf fun _ ⟨_, _, _, ht⟩ ↦ ht

theorem originalTop_le : originalTop Ξ σ ≤ topologicalSpace Ξ σ :=
  le_sInf fun _t ⟨ht, _⟩ ↦ ht

/-- A locally convex vector-space topology on `C(G)` is coarser than the inductive-limit
topology if and only if it is coarser than `originalTop`. -/
theorem topologicalSpace_le_iff {t : TopologicalSpace (Space Ξ σ)}
    [@IsTopologicalAddGroup _ t _] [@ContinuousSMul ℂ _ _ _ t]
    [@LocallyConvexSpace ℝ _ _ _ _ _ t] :
    topologicalSpace Ξ σ ≤ t ↔ originalTop Ξ σ ≤ t :=
  ⟨le_trans originalTop_le, fun H ↦ sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

/-- Every inclusion `C_H → C(G)` is continuous. -/
theorem continuous_ofLevel (K : CompactOpenSubgroup G) :
    Continuous (ofLevel (Ξ := Ξ) (σ := σ) K) := by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup_of_le K le_rfl) originalTop_le

/-- The inclusion `C_H → C(G)` as a continuous linear map. -/
def ofLevelCLM (K : CompactOpenSubgroup G) : Level Ξ σ K →L[ℂ] Space Ξ σ where
  toLinearMap := ofLevel K
  cont := continuous_ofLevel K

@[simp] theorem coe_ofLevelCLM (K : CompactOpenSubgroup G) :
    (ofLevelCLM K : Level Ξ σ K → Space Ξ σ) = ofLevel K :=
  rfl

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [t : TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
  [LocallyConvexSpace ℝ V]

/-- The universal property III.6(1): a linear map from `C(G)` to a locally convex complex
topological vector space is continuous if and only if its restriction to every level `C_H`
is continuous. -/
theorem continuous_iff_continuous_comp (T : Space Ξ σ →ₗ[ℂ] V) :
    Continuous T ↔ ∀ K : CompactOpenSubgroup G, Continuous (T ∘ ofLevel K) := by
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced T t) _ := isTopologicalAddGroup_induced T
  have : @ContinuousSMul ℂ _ _ _ (induced T t) := continuousSMul_induced T
  have : @LocallyConvexSpace ℝ _ _ _ _ _ (induced T t) :=
    LocallyConvexSpace.induced (T.restrictScalars ℝ)
  rw [topologicalSpace_le_iff, originalTop, iSup_le_iff]
  simp_rw [← continuous_iff_le_induced, continuous_coinduced_dom]

/-- Construct a continuous linear map on `C(G)` from continuity on every level. -/
def mkCLM (T : Space Ξ σ →ₗ[ℂ] V)
    (hT : ∀ K : CompactOpenSubgroup G, Continuous (T ∘ ofLevel K)) :
    Space Ξ σ →L[ℂ] V where
  toLinearMap := T
  cont := (continuous_iff_continuous_comp T).mpr hT

@[simp] theorem coe_mkCLM (T : Space Ξ σ →ₗ[ℂ] V)
    (hT : ∀ K : CompactOpenSubgroup G, Continuous (T ∘ ofLevel K)) :
    (mkCLM T hT : Space Ξ σ → V) = T :=
  rfl

/-- The underlying-function map `C(G) → (G → ℂ)`, as a linear map. -/
def toFunLinear : Space Ξ σ →ₗ[ℂ] (G → ℂ) :=
  (schwartzSubmodule Ξ σ).subtype

@[simp] theorem toFunLinear_apply (f : Space Ξ σ) : toFunLinear f = f :=
  rfl

theorem toFunLinear_injective : Function.Injective (toFunLinear (Ξ := Ξ) (σ := σ)) :=
  DFunLike.coe_injective

/-- For positive `Ξ`, evaluation at each point is continuous on every level `C_H`. -/
theorem continuous_eval_level (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (K : CompactOpenSubgroup G) (g : G) :
    Continuous fun f : Level Ξ σ K => f g := by
  let ev : Level Ξ σ K →ₗ[ℂ] ℂ :=
    { toFun := fun f => f g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change Continuous ev
  refine WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ ℂ) ev fun _ => ?_
  refine Seminorm.continuous_of_le (q := (Ξ g).toNNReal • Level.seminorm K 0)
    (by
      rw [FunLike.coe_smul]
      exact (Level.continuous_seminorm (Ξ := Ξ) (σ := σ) K 0).const_smul _) ?_
  intro f
  have h := norm_le_of_nu (r := 0) hΞ hσ (Level.nu_ne_top f 0) g
  simp only [neg_zero, Real.rpow_zero, mul_one] at h
  change ‖f g‖ ≤ ((Ξ g).toNNReal • Level.seminorm K 0) f
  rw [smul_apply, Level.seminorm_apply, NNReal.smul_def, Real.coe_toNNReal _ (hΞ g).le,
    smul_eq_mul, mul_comm]
  exact h

/-- For positive `Ξ`, the underlying-function map `C(G) → (G → ℂ)` is continuous for the
product topology. -/
theorem continuous_toFunLinear (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) :
    Continuous (toFunLinear (Ξ := Ξ) (σ := σ)) := by
  refine (continuous_iff_continuous_comp _).mpr fun K => continuous_pi fun g => ?_
  exact continuous_eval_level hΞ hσ K g

/-- For positive `Ξ` and nonnegative `σ`, the topology of `C(G)` is Hausdorff. -/
theorem t2Space (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) : T2Space (Space Ξ σ) :=
  .of_injective_continuous toFunLinear_injective (continuous_toFunLinear hΞ hσ)

end Space

end Spaces

end Langlands.HarishChandraSchwartz
