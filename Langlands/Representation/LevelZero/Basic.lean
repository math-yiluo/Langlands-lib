import Langlands.Group.GL.IntegralReduction
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.LevelZero.CentralPowerProduct
import Langlands.Representation.LevelZero.Indicator

/-!
# The inducing datum of a level-zero representation of `GL_{m+1}(F)`

Let `F` be a nonarchimedean local field with valuation ring `𝒪`, residue field `k` and
uniformizer `ϖ`, and let `K = GL_{m+1}(𝒪)`. A representation `σ` of `GL_{m+1}(k)`, inflated to
`K` through reduction modulo the maximal ideal and extended by letting the central element
`ϖ · 1` act trivially, is a representation `Λ` of the open subgroup `J = ϖ^ℤ K`. Reduction is
trivial on an open subgroup of `K`, so `Λ` is trivial on an open subgroup of `J`.
-/

noncomputable section

open Filter Topology

namespace Langlands.LevelZero

open GeneralLinear ValuativeRel

universe u uW

section Integers

variable (F : Type u) [Field F] [ValuativeRel F]

/-- The valuation ring of `F`. -/
abbrev integers : Subring F := (valuation F).integer

/-- An integer lies in the maximal ideal exactly when its valuation is less than one. -/
theorem mem_maximalIdeal_iff (x : integers F) :
    x ∈ IsLocalRing.maximalIdeal (integers F) ↔ valuation F (x : F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, ne_of_lt⟩

/-- Two integers have the same residue exactly when their difference has valuation less
than one. -/
theorem residue_eq_residue_iff (x y : integers F) :
    IsLocalRing.residue (integers F) x = IsLocalRing.residue (integers F) y ↔
      valuation F ((x : F) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  rfl

end Integers

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (m : ℕ)

/-- The maximal compact subgroup `GL_{m+1}(𝒪)`. -/
abbrev maximalCompact : Subgroup (GeneralLinear (m + 1) F) :=
  Conductor.integralSubgroup (integers F) m

/-- Reduction of `GL_{m+1}(𝒪)` modulo the maximal ideal. -/
abbrev residueReduction :
    maximalCompact (F := F) m →* GeneralLinear (m + 1) (IsLocalRing.ResidueField (integers F)) :=
  IntegralReduction.reduction (integers F) m

/-- The scalar matrix of a unit. -/
def uniformizerScalar (ϖ : Fˣ) : GeneralLinear (m + 1) F := GeneralLinear.scalar ϖ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem uniformizerScalar_mem_center (ϖ : Fˣ) :
    uniformizerScalar m ϖ ∈ Subgroup.center (GeneralLinear (m + 1) F) :=
  Subgroup.mem_center_iff.mpr fun g =>
    (Matrix.GeneralLinearGroup.scalar_commute ϖ g).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem uniformizerScalar_zpow (ϖ : Fˣ) (a : ℤ) :
    uniformizerScalar m ϖ ^ a = GeneralLinear.scalar (ϖ ^ a) := by
  rw [uniformizerScalar, map_zpow]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem scalar_apply_self (c : Fˣ) (i : Fin (m + 1)) :
    (GeneralLinear.scalar c : GeneralLinear (m + 1) F) i i = c := by
  change (Matrix.scalar (Fin (m + 1)) (c : F)) i i = c
  simp

variable {m}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- No nontrivial power of the uniformizer scalar is integral. -/
theorem zpow_mem_maximalCompact {ϖ : Fˣ}
    (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ) (a : ℤ)
    (ha : uniformizerScalar m ϖ ^ a ∈ maximalCompact (F := F) m) : a = 0 := by
  rw [Conductor.mem_integralSubgroup] at ha
  obtain ⟨h1, h2⟩ := ha
  have e1 := h1 0 0
  have e2 := h2 0 0
  rw [uniformizerScalar_zpow, scalar_apply_self] at e1
  rw [uniformizerScalar_zpow, ← map_inv, scalar_apply_self] at e2
  rw [Valuation.mem_integer_iff, Units.val_zpow_eq_zpow_val, map_zpow₀] at e1
  rw [Valuation.mem_integer_iff, ← zpow_neg, Units.val_zpow_eq_zpow_val, map_zpow₀] at e2
  have hpos : 0 < valuation F (ϖ : F) := Iwasawa.valuation_pos _ ϖ
  have hanti := zpow_right_strictAnti₀ hpos hϖ.1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hanti hlt
    simp only [zpow_zero] at h
    exact absurd e1 (not_le.mpr h)
  · have h := hanti (neg_lt_zero.mpr hgt)
    simp only [zpow_zero] at h
    exact absurd e2 (not_le.mpr h)

variable (m)

/-- The inducing subgroup `J = ϖ^ℤ GL_{m+1}(𝒪)`. -/
def inducingSubgroup (ϖ : Fˣ) : Subgroup (GeneralLinear (m + 1) F) :=
  powerProduct (uniformizerScalar m ϖ) (uniformizerScalar_mem_center m ϖ) (maximalCompact m)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem maximalCompact_le_inducingSubgroup (ϖ : Fˣ) :
    maximalCompact (F := F) m ≤ inducingSubgroup m ϖ :=
  le_powerProduct _ _ _

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The representation of `J` inflated from `σ`, with `ϖ · 1` acting trivially. -/
def inducingRep {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
    (σ : Representation ℂ (GeneralLinear (m + 1) (IsLocalRing.ResidueField (integers F))) W) :
    Representation ℂ (inducingSubgroup m ϖ) W :=
  extendRepresentation (uniformizerScalar_mem_center m ϖ) (zpow_mem_maximalCompact hϖ)
    (σ.comp (residueReduction m))

variable {m}

theorem inducingRep_of_mem {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
    (σ : Representation ℂ (GeneralLinear (m + 1) (IsLocalRing.ResidueField (integers F))) W)
    {k : GeneralLinear (m + 1) F} (hk : k ∈ maximalCompact (F := F) m) :
    inducingRep m hϖ σ ⟨k, maximalCompact_le_inducingSubgroup m ϖ hk⟩ =
      σ (residueReduction m ⟨k, hk⟩) :=
  extendRepresentation_of_mem _ _ _ ⟨k, hk⟩

theorem inducingRep_zpow_mul {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
    (σ : Representation ℂ (GeneralLinear (m + 1) (IsLocalRing.ResidueField (integers F))) W)
    (a : ℤ) {k : GeneralLinear (m + 1) F} (hk : k ∈ maximalCompact (F := F) m) :
    inducingRep m hϖ σ ⟨uniformizerScalar m ϖ ^ a * k,
        zpow_mul_mem_powerProduct _ _ _ a hk⟩ =
      σ (residueReduction m ⟨k, hk⟩) :=
  extendRepresentation_zpow_mul _ _ _ a ⟨k, hk⟩

/-! ### An open subgroup on which reduction is trivial -/

variable (m)

/-- Matrices whose entries, and those of their inverse, are congruent to the identity. -/
def nearIdentity : Set (GeneralLinear (m + 1) F) :=
  {g | ∀ i j, valuation F ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) < 1 ∧
    valuation F ((g⁻¹ : GeneralLinear (m + 1) F) i j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) < 1}

theorem nearIdentity_mem_nhds : nearIdentity (F := F) m ∈ 𝓝 (1 : GeneralLinear (m + 1) F) := by
  have hB : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun x hx => by simpa using hx⟩
  have hentry : ∀ i j, Continuous fun g : GeneralLinear (m + 1) F =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j -
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j :=
    fun i j => (GeneralLinear.entry i j).continuous.sub continuous_const
  have hentry' : ∀ i j, Continuous fun g : GeneralLinear (m + 1) F =>
      (g⁻¹ : GeneralLinear (m + 1) F) i j -
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j :=
    fun i j => ((GeneralLinear.entry i j).continuous.comp continuous_inv).sub continuous_const
  have h0 : ∀ i j, (((1 : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) = 0 := fun i j => by simp
  have h0' : ∀ i j, (((1 : GeneralLinear (m + 1) F)⁻¹ : GeneralLinear (m + 1) F) i j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) = 0 := fun i j => by simp
  have hset : nearIdentity (F := F) m =
      ⋂ i, ⋂ j, ((fun g : GeneralLinear (m + 1) F =>
          (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j -
            (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) ⁻¹' {x | valuation F x < 1} ∩
        (fun g : GeneralLinear (m + 1) F => (g⁻¹ : GeneralLinear (m + 1) F) i j -
            (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) ⁻¹' {x | valuation F x < 1}) := by
    ext g
    simp [nearIdentity]
  rw [hset]
  refine iInter_mem.mpr fun i => iInter_mem.mpr fun j => inter_mem ?_ ?_
  · apply (hentry i j).continuousAt.preimage_mem_nhds
    rw [h0]
    exact hB
  · apply (hentry' i j).continuousAt.preimage_mem_nhds
    rw [h0']
    exact hB

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem valuation_le_one_of_near (x d : F) (hd : valuation F d ≤ 1)
    (h : valuation F (x - d) < 1) : valuation F x ≤ 1 := by
  have : x = (x - d) + d := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le h.le hd)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem valuation_one_apply_le (i j : Fin (m + 1)) :
    valuation F ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem nearIdentity_subset_maximalCompact :
    nearIdentity (F := F) m ⊆ (maximalCompact (F := F) m : Set (GeneralLinear (m + 1) F)) := by
  intro g hg
  rw [SetLike.mem_coe, Conductor.mem_integralSubgroup]
  exact ⟨fun i j => (Valuation.mem_integer_iff _ _).mpr
      (valuation_le_one_of_near _ _ (valuation_one_apply_le m i j) (hg i j).1),
    fun i j => (Valuation.mem_integer_iff _ _).mpr
      (valuation_le_one_of_near _ _ (valuation_one_apply_le m i j) (hg i j).2)⟩

theorem residueReduction_eq_one_of_near {g : GeneralLinear (m + 1) F}
    (hg : g ∈ nearIdentity (F := F) m) :
    residueReduction m ⟨g, nearIdentity_subset_maximalCompact m hg⟩ = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [IntegralReduction.reduction_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
  have hδ : (if i = j then (1 : IsLocalRing.ResidueField (integers F)) else 0) =
      IsLocalRing.residue (integers F) (if i = j then 1 else 0) := by
    split_ifs <;> simp
  rw [hδ, residue_eq_residue_iff, IntegralReduction.integralEquiv_symm_apply_val]
  have h := (hg i j).1
  rw [Matrix.one_apply] at h
  split_ifs at h ⊢ <;> simpa using h

/-- An open (compact) subgroup of `GL_{m+1}(𝒪)` on which reduction is trivial. -/
theorem exists_openSubgroup_reduction_trivial :
    ∃ L : OpenSubgroup (GeneralLinear (m + 1) F),
      ∃ hLK : (L : Subgroup (GeneralLinear (m + 1) F)) ≤ maximalCompact (F := F) m,
        ∀ (g : GeneralLinear (m + 1) F) (hg : g ∈ L), residueReduction m ⟨g, hLK hg⟩ = 1 := by
  obtain ⟨L, -, hLU⟩ := LocalFieldTopology.generalLinear_compactOpen F (m + 1) _
    (nearIdentity_mem_nhds (F := F) m)
  exact ⟨L, fun g hg => nearIdentity_subset_maximalCompact m (hLU hg),
    fun g hg => residueReduction_eq_one_of_near m (hLU hg)⟩

end Langlands.LevelZero
