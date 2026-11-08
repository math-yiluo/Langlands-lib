import Langlands.LocalFactor.DeligneHenniartDimensionOne

/-! # Deligne--Henniart Lemma 4.7 over an intermediate field -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local LocalClassField
open VirtualRepresentation.LocalWeil.Ramification Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-! ## The carried upper groups -/

theorem intermediateUpperGroup_antitone (E : Extension F) :
    Antitone (intermediateUpperGroup F E) := fun _ _ hst =>
  Subgroup.map_mono (upperGroup_antitone (E.asPadicField (p := p)) hst)

theorem intermediateUpperGroup_normal (E : Extension F) (s : ℝ) :
    (intermediateUpperGroup F E s).Normal :=
  (upperGroup_normal (E.asPadicField (p := p)) s).map _
    (intermediateWeilEquiv F E).surjective

/-- With the inertia comparison for `E`, the carried upper group of index `s ≥ 0`
lies in the inertia subgroup of `W_E`. -/
theorem intermediateUpperGroup_le_inertia (E : Extension F)
    (hinert : AbsoluteUpperInertia (E.asPadicField (p := p))
      (E.asPadicField (p := p)).canonicalTopologicalData)
    {s : ℝ} (hs : 0 ≤ s) :
    intermediateUpperGroup F E s ≤ CommonClosureWeilDeligne.inertia F E := by
  rintro _ ⟨w, hw, rfl⟩
  have h0 : w ∈ upperGroup (E.asPadicField (p := p)) 0 :=
    upperGroup_antitone (E.asPadicField (p := p)) hs hw
  have hI : w ∈ localInertia (E.asPadicField (p := p)) := by
    rw [localInertia_eq_comap]
    change localProjection (E.asPadicField (p := p)) w ∈
      (E.asPadicField (p := p)).absoluteInertia
        (E.asPadicField (p := p)).canonicalTopologicalData
    rw [← hinert]
    exact h0
  have hF := (intermediateWeilMap_mem_localInertia F E w).mpr hI
  exact hF

/-! ## Conductors on the larger field -/

/-- The relative form of `restrictCharacter_trivial_iff`: tests over `E` relative to
its own carried upper groups. -/
theorem restrictCharacter_trivial_iff_rel {e : ReciprocityFamily F}
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E) {b : ℕ}
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (intermediateUpperGroup F E s).map (reciprocityUnits F e E).toMonoidHom =
        (fieldData F E).principalUnits ⌈s⌉₊)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (ψH : ℝ → ℝ)
    (hmem : ∀ v : ℝ, 0 ≤ v → ∀ g : weilSubgroup F L,
      weilInclusion F E L h g ∈ intermediateUpperGroup F E v ↔
        g ∈ intermediateUpperGroup F L (ψH v))
    (hNL : ∀ g ∈ intermediateUpperGroup F E ((b : ℝ) / 2),
      (g : localWeilGroup F) ∈ weilSubgroup F L)
    {v : ℝ} (hv : (b : ℝ) / 2 ≤ v) (hψv : 0 ≤ ψH v) :
    (∀ u ∈ (fieldData F L).principalUnits ⌈ψH v⌉₊,
        restrictCharacter F e E L h χ u = 1) ↔ (b : ℝ) < v := by
  have hv0 : 0 ≤ v := le_trans (by positivity) hv
  rw [trivial_iff_of_map_reciprocityUnits F L _ _ _ (hWL _ hψv),
    weilCharacter_restrictCharacter]
  have hstep : (∀ g ∈ intermediateUpperGroup F L (ψH v),
        ((weilCharacter F e E χ).comp (weilInclusion F E L h)) g = 1) ↔
      ∀ x ∈ intermediateUpperGroup F E v, weilCharacter F e E χ x = 1 := by
    constructor
    · intro H x hx
      have hxL : (x : localWeilGroup F) ∈ weilSubgroup F L :=
        hNL _ (intermediateUpperGroup_antitone F E hv hx)
      have hg : weilInclusion F E L h ⟨x, hxL⟩ = x := rfl
      have := H ⟨x, hxL⟩ ((hmem v hv0 _).mp (by rw [hg]; exact hx))
      exact this
    · intro H g hg
      exact H _ ((hmem v hv0 g).mpr hg)
  rw [hstep, ← trivial_iff_of_map_reciprocityUnits F E χ _ _ (hWE v hv0)]
  change (fieldData F E).MultiplicativeTrivialAt χ ⌈v⌉₊ ↔ _
  rw [PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le, hcond,
    Nat.add_one_le_iff, Nat.lt_ceil]

/-- The relative form of `conductor_restrictCharacter`. -/
theorem conductor_restrictCharacter_rel {e : ReciprocityFamily F}
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E) {b : ℕ}
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (intermediateUpperGroup F E s).map (reciprocityUnits F e E).toMonoidHom =
        (fieldData F E).principalUnits ⌈s⌉₊)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (ψH : ℝ → ℝ) (hcont : Continuous ψH) (hmono : StrictMono ψH) (hzero : ψH 0 = 0)
    (hmem : ∀ v : ℝ, 0 ≤ v → ∀ g : weilSubgroup F L,
      weilInclusion F E L h g ∈ intermediateUpperGroup F E v ↔
        g ∈ intermediateUpperGroup F L (ψH v))
    (hNL : ∀ g ∈ intermediateUpperGroup F E ((b : ℝ) / 2),
      (g : localWeilGroup F) ∈ weilSubgroup F L) :
    ∃ B : ℕ, ψH b = B ∧
      (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) = B + 1 := by
  set T := fieldData F L
  set χL := restrictCharacter F e E L h χ
  have hb2 : (b : ℝ) / 2 ≤ b := by
    have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  have hψnn : ∀ v : ℝ, 0 ≤ v → 0 ≤ ψH v := fun v hv => hzero ▸ hmono.monotone hv
  have hψb := hψnn b (Nat.cast_nonneg b)
  have key := fun (v : ℝ) (hv : (b : ℝ) / 2 ≤ v) =>
    restrictCharacter_trivial_iff_rel F E L h χ hcond hWE hWL ψH hmem hNL hv
      (hψnn v (le_trans (by positivity) hv))
  have hnot : ¬ T.MultiplicativeTrivialAt χL ⌈ψH b⌉₊ := by
    intro htr
    exact lt_irrefl _ ((key b hb2).mp htr)
  have hlow : ⌈ψH b⌉₊ < T.multiplicativeConductor χL := by
    by_contra hle
    push Not at hle
    exact hnot ((T.multiplicativeTrivialAt_iff_conductor_le χL _).mpr hle)
  set B := ⌊ψH b⌋₊ with hB
  have hlt : ψH b < (B : ℝ) + 1 := Nat.lt_floor_add_one _
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont b ((B : ℝ) + 1 - ψH b)
    (by linarith)
  have hvb : (b : ℝ) < b + δ / 2 := by linarith
  have hdist : dist ((b : ℝ) + δ / 2) b < δ := by
    rw [Real.dist_eq, show (b : ℝ) + δ / 2 - b = δ / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have hψv : ψH (b + δ / 2) < B + 1 := by
    have := hball _ hdist
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith
  have htriv := (key (b + δ / 2) (by linarith)).mpr hvb
  have hup : T.multiplicativeConductor χL ≤ ⌈ψH (b + δ / 2)⌉₊ :=
    (T.multiplicativeTrivialAt_iff_conductor_le χL _).mp htriv
  have hceil : ⌈ψH (b + δ / 2)⌉₊ ≤ B + 1 := by
    apply Nat.ceil_le.mpr
    push_cast
    exact hψv.le
  have hfc : ⌈ψH b⌉₊ ≤ B := by omega
  have hint : ψH b = B := by
    have h1 : ψH b ≤ ⌈ψH b⌉₊ := Nat.le_ceil _
    have h2 : (B : ℝ) ≤ ψH b := Nat.floor_le hψb
    have h3 : ((⌈ψH b⌉₊ : ℕ) : ℝ) ≤ B := by exact_mod_cast hfc
    linarith
  refine ⟨B, hint, ?_⟩
  have h4 : ⌈ψH b⌉₊ = B := by
    rw [hint, Nat.ceil_natCast]
  change T.multiplicativeConductor χL = B + 1
  omega

/-! ## The exact witness over an intermediate field -/

/-- The Herbrand input for `E ≤ L` at the break `b`, relative to the carried upper
groups of `E` and `L`: a continuous strictly increasing `ψ` with `ψ 0 = 0`, Herbrand's
subgroup formula, the slope relation between `b/2` and `b`, and the slope bound. -/
def HerbrandInputRel (E L : Extension F) (h : E.field ≤ L.field) (b : ℕ) : Prop :=
  ∃ ψH : ℝ → ℝ, Continuous ψH ∧ StrictMono ψH ∧ ψH 0 = 0 ∧
    (∀ v : ℝ, 0 ≤ v → ∀ g : weilSubgroup F L,
      weilInclusion F E L h g ∈ intermediateUpperGroup F E v ↔
        g ∈ intermediateUpperGroup F L (ψH v)) ∧
    ((fieldData F E).ramificationIndex : ℝ) * (ψH b - ψH ((b : ℝ) / 2)) =
      (fieldData F L).ramificationIndex * ((b : ℝ) / 2) ∧
    ((fieldData F E).ramificationIndex : ℝ) * ψH b ≤
      (fieldData F L).ramificationIndex * (b : ℝ)

/-- DH81 Lemma 4.7 over an intermediate field `E`: if `c` linearizes the character `χ`
of `E` of break `b ≥ 1`, then `c⁻¹` is an exact witness for `[χ]` relative to the
carried upper group of `E` of index `b/2`. The unit-level theorems at `E` and at every
larger field `L` whose Weil subgroup contains that group, the inertia comparison for
`E`, and the relative Herbrand input for each such `L` are hypotheses. -/
theorem exactWitnessOn_characterClass_of_linearization_rel {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε) (E : Extension F)
    (hinert : AbsoluteUpperInertia (E.asPadicField (p := p))
      (E.asPadicField (p := p)).canonicalTopologicalData)
    (χ : FieldCharacter F E) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (ψ : AdditiveCharacter F E) (c : E.fieldˣ)
    (hlin : letI := (fieldData F E).topology;
      ∀ z ∈ (fieldData F E).principalUnits (b + 1 - (b + 1) / 2),
        (χ z : ℂ) = ψ.complex ((c : E.field) * ((z : E.field) - 1)))
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (intermediateUpperGroup F E s).map (reciprocityUnits F e E).toMonoidHom =
        (fieldData F E).principalUnits ⌈s⌉₊)
    (hL : ∀ (L : Extension F) (h : E.field ≤ L.field),
      (∀ g ∈ intermediateUpperGroup F E ((b : ℝ) / 2),
        (g : localWeilGroup F) ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧ HerbrandInputRel F E L h b) :
    ExactWitnessOn F e ε E (intermediateUpperGroup F E ((b : ℝ) / 2)) ψ
      (characterClass F e E χ) c⁻¹ := by
  have hb2 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  apply exactWitnessOn_characterClass F hsys E _ (intermediateUpperGroup_normal F E _)
    (intermediateUpperGroup_le_inertia F E hinert hb2) ψ χ c⁻¹
  intro L h η hNL hη μL
  obtain ⟨hWL, ψH, hcont, hmono, hzero, hmem, hslope, hle⟩ := hL L h hNL
  obtain ⟨B, hBψ, haL⟩ := conductor_restrictCharacter_rel F E L h χ hcond hWE hWL ψH hcont
    hmono hzero hmem hNL
  set η' := CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η with hη'
  have hψh0 : 0 ≤ ψH ((b : ℝ) / 2) := hzero ▸ hmono.monotone hb2
  have hψhpos : 0 < ψH ((b : ℝ) / 2) := by
    rw [← hzero]
    apply hmono
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hηtriv : (fieldData F L).MultiplicativeTrivialAt η' ⌈ψH ((b : ℝ) / 2)⌉₊ := by
    change ∀ u ∈ (fieldData F L).principalUnits ⌈ψH ((b : ℝ) / 2)⌉₊, η' u = 1
    rw [trivial_iff_of_map_reciprocityUnits F L η' _ _ (hWL _ hψh0), hη',
      CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
    intro g hg
    have hgE := (hmem _ hb2 g).mpr hg
    have := hη ⟨weilInclusion F E L h g, hgE⟩
    exact this
  have haη := ((fieldData F L).multiplicativeTrivialAt_iff_conductor_le η' _).mp hηtriv
  have heE : 0 < (fieldData F E).ramificationIndex := (fieldData F E).ramificationIndex_pos
  rw [hBψ] at hslope hle
  have hleN : (fieldData F E).ramificationIndex * B ≤
      (fieldData F L).ramificationIndex * b := by exact_mod_cast hle
  have haηR : ((fieldData F L).multiplicativeConductor η' : ℝ) ≤ ⌈ψH ((b : ℝ) / 2)⌉ := by
    have h1 : ((fieldData F L).multiplicativeConductor η' : ℝ) ≤
        (⌈ψH ((b : ℝ) / 2)⌉₊ : ℝ) := by
      exact_mod_cast haη
    have h2 : ((⌈ψH ((b : ℝ) / 2)⌉₊ : ℕ) : ℤ) = ⌈ψH ((b : ℝ) / 2)⌉ :=
      Int.natCast_ceil_eq_ceil hψh0
    calc ((fieldData F L).multiplicativeConductor η' : ℝ) ≤ (⌈ψH ((b : ℝ) / 2)⌉₊ : ℝ) := h1
      _ = ((⌈ψH ((b : ℝ) / 2)⌉₊ : ℤ) : ℝ) := by norm_cast
      _ = (⌈ψH ((b : ℝ) / 2)⌉ : ℝ) := by rw [h2]
  obtain ⟨hR, hT, h2L, htm, htA, hηt, hη2⟩ := depth_conditions heE hslope hleN hψhpos haηR
  rw [← haL] at h2L htm htA hηt hη2
  have hm : 0 < b + 1 - (b + 1) / 2 := by omega
  have hχA : ∀ z ∈ (fieldData F E).principalUnits (b + 1), χ z = 1 := by
    rw [← hcond]
    exact (fieldData F E).multiplicativeConductor_spec χ
  exact abelianEpsilonExpression_restrictCharacter_mul F hsys.1 E L h χ ψ c
    hm (by omega) hlin hχA η' μL hR hT h2L htm htA hηt hη2

/-- The packaged form: a character `χ` of `E` of break `b ≥ 1` (conductor `b + 1`) has an
exact witness relative to the carried upper group of `E` of index `b/2`, of order
`(b + 1) + n(ψ)` (DH81 4.7 and 4.2.2 in dimension one, over `E`). -/
theorem exists_exactWitnessOn_rel {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε) (E : Extension F)
    (hinert : AbsoluteUpperInertia (E.asPadicField (p := p))
      (E.asPadicField (p := p)).canonicalTopologicalData)
    (χ : FieldCharacter F E) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (ψ : AdditiveCharacter F E)
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (intermediateUpperGroup F E s).map (reciprocityUnits F e E).toMonoidHom =
        (fieldData F E).principalUnits ⌈s⌉₊)
    (hL : ∀ (L : Extension F) (h : E.field ≤ L.field),
      (∀ g ∈ intermediateUpperGroup F E ((b : ℝ) / 2),
        (g : localWeilGroup F) ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧ HerbrandInputRel F E L h b) :
    ∃ γ : E.fieldˣ,
      (fieldData F E).ord (γ : E.field) = ((b : ℤ) + 1) + (fieldData F E).additiveConductor ψ ∧
      ExactWitnessOn F e ε E (intermediateUpperGroup F E ((b : ℝ) / 2)) ψ
        (characterClass F e E χ) γ := by
  let T := fieldData F E
  have h2 : 2 ≤ T.multiplicativeConductor χ := by
    change 2 ≤ (fieldData F E).multiplicativeConductor _
    omega
  obtain ⟨c, hc, hlin⟩ := exists_linearization T χ ψ h2
  have hab : T.multiplicativeConductor χ = b + 1 := hcond
  refine ⟨c⁻¹, ?_, ?_⟩
  · rw [hab] at hc
    change T.ord ((c⁻¹ : E.fieldˣ) : E.field) = _
    rw [Units.val_inv_eq_inv_val, T.ord_inv, hc]
    push_cast
    ring
  · rw [hab] at hlin
    exact exactWitnessOn_characterClass_of_linearization_rel F hsys E hinert χ hb hcond ψ c
      hlin hWE hL

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
