import Langlands.LocalFactor.DeligneHenniartApproximateRankOne
import Langlands.LocalFactor.DeligneHenniartDimensionOneRelative

/-! # The approximate witness for one wild character (DH81 4.3 and 4.4) -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local LocalClassField
open VirtualRepresentation.LocalWeil.Ramification Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The first-order norm–trace congruence for `E ≤ L` (DH81 3.12(i)) at the level `b` of
`E` and the layer `B` of `L`: every nonzero `y ∈ L` of order at least `B` has trace of
order at least `b`, and `N(1 + y)` agrees with `1 + Tr y` up to `U_E^{b+1}`. -/
def TopLayerInput (E L : Extension F) (h : E.field ≤ L.field) (b : ℕ) (B : ℝ) : Prop :=
  ∀ y : L.field, y ≠ 0 → B ≤ ((fieldData F L).ord y : ℝ) →
    @Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra y ∈
        (fieldData F E).additiveLattice (-(b : ℤ)) ∧
      ∀ (z : L.fieldˣ) (t : E.fieldˣ), (z : L.field) = 1 + y →
        (t : E.field) =
            1 + @Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra y →
          E.unitsNorm L h z * t⁻¹ ∈ (fieldData F E).principalUnits (b + 1)

/-- The input for one larger field `L` in the approximate case, relative to a family `U`
of subgroups of `W_E`: a continuous strictly increasing `ψ` with `ψ 0 = 0` satisfying
Herbrand's subgroup formula between `U` and the upper groups of `L`, and the norm–trace
congruence at the layer `ψ(b)`. -/
def ApproximateHerbrandInput (E L : Extension F) (h : E.field ≤ L.field)
    (U : ℝ → Subgroup (weilSubgroup F E)) (b : ℕ) : Prop :=
  ∃ ψH : ℝ → ℝ, Continuous ψH ∧ StrictMono ψH ∧ ψH 0 = 0 ∧
    (∀ v : ℝ, 0 ≤ v → ∀ g : weilSubgroup F L,
      weilInclusion F E L h g ∈ U v ↔ g ∈ intermediateUpperGroup F L (ψH v)) ∧
    TopLayerInput F E L h b (ψH b)

/-! ## Conductors on the larger field, for a family of subgroups -/

/-- `restrictCharacter_trivial_iff` for a family `U` of subgroups of `W_E` and any threshold
`s₀`: if `U s₀` lies in `W_L`, then for `v ≥ s₀` the norm pullback of `χ` is trivial at
level `⌈ψ v⌉` exactly when `b < v`. -/
theorem restrictCharacter_trivial_iff_family {e : ReciprocityFamily F}
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E) {b : ℕ}
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (U : ℝ → Subgroup (weilSubgroup F E)) (hU : Antitone U)
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (U s).map (reciprocityUnits F e E).toMonoidHom = (fieldData F E).principalUnits ⌈s⌉₊)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (ψH : ℝ → ℝ)
    (hmem : ∀ v : ℝ, 0 ≤ v → ∀ g : weilSubgroup F L,
      weilInclusion F E L h g ∈ U v ↔ g ∈ intermediateUpperGroup F L (ψH v))
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hNL : ∀ g ∈ U s₀, (g : localWeilGroup F) ∈ weilSubgroup F L)
    {v : ℝ} (hv : s₀ ≤ v) (hψv : 0 ≤ ψH v) :
    (∀ u ∈ (fieldData F L).principalUnits ⌈ψH v⌉₊,
        restrictCharacter F e E L h χ u = 1) ↔ (b : ℝ) < v := by
  have hv0 : 0 ≤ v := hs₀.trans hv
  rw [trivial_iff_of_map_reciprocityUnits F L _ _ _ (hWL _ hψv),
    weilCharacter_restrictCharacter]
  have hstep : (∀ g ∈ intermediateUpperGroup F L (ψH v),
        ((weilCharacter F e E χ).comp (weilInclusion F E L h)) g = 1) ↔
      ∀ x ∈ U v, weilCharacter F e E χ x = 1 := by
    constructor
    · intro H x hx
      have hxL : (x : localWeilGroup F) ∈ weilSubgroup F L := hNL _ (hU hv hx)
      have hg : weilInclusion F E L h ⟨x, hxL⟩ = x := rfl
      exact H ⟨x, hxL⟩ ((hmem v hv0 _).mp (by rw [hg]; exact hx))
    · intro H g hg
      exact H _ ((hmem v hv0 g).mpr hg)
  rw [hstep, ← trivial_iff_of_map_reciprocityUnits F E χ _ _ (hWE v hv0)]
  change (fieldData F E).MultiplicativeTrivialAt χ ⌈v⌉₊ ↔ _
  rw [PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le, hcond,
    Nat.add_one_le_iff, Nat.lt_ceil]

/-- `conductor_restrictCharacter` for a family `U` and a threshold `s₀ ≤ b`. -/
theorem conductor_restrictCharacter_family {e : ReciprocityFamily F}
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E) {b : ℕ}
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (U : ℝ → Subgroup (weilSubgroup F E)) (hU : Antitone U)
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (U s).map (reciprocityUnits F e E).toMonoidHom = (fieldData F E).principalUnits ⌈s⌉₊)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (ψH : ℝ → ℝ) (hcont : Continuous ψH) (hmono : StrictMono ψH) (hzero : ψH 0 = 0)
    (hmem : ∀ v : ℝ, 0 ≤ v → ∀ g : weilSubgroup F L,
      weilInclusion F E L h g ∈ U v ↔ g ∈ intermediateUpperGroup F L (ψH v))
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hs₀b : s₀ ≤ b)
    (hNL : ∀ g ∈ U s₀, (g : localWeilGroup F) ∈ weilSubgroup F L) :
    ∃ B : ℕ, ψH b = B ∧
      (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) = B + 1 := by
  set T := fieldData F L
  set χL := restrictCharacter F e E L h χ
  have hψnn : ∀ v : ℝ, 0 ≤ v → 0 ≤ ψH v := fun v hv => hzero ▸ hmono.monotone hv
  have hψb := hψnn b (Nat.cast_nonneg b)
  have key := fun (v : ℝ) (hv : s₀ ≤ v) =>
    restrictCharacter_trivial_iff_family F E L h χ hcond U hU hWE hWL ψH hmem hs₀ hNL hv
      (hψnn v (hs₀.trans hv))
  have hnot : ¬ T.MultiplicativeTrivialAt χL ⌈ψH b⌉₊ := by
    intro htr
    exact lt_irrefl _ ((key b hs₀b).mp htr)
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

/-! ## The comparison of linearizers on the top layer (DH81 4.4) -/

/-- DH81 4.4: given the norm–trace congruence at the top layer `B` of the norm pullback
(whose conductor is `B + 1`), the linearizer `c` of `χ` on `E` and a linearizer `d` of the
pullback on `L` agree modulo `U_L^1`. -/
theorem mul_inv_mem_principalUnits_one_of_topLayer {e : ReciprocityFamily F}
    (he : NormalizedReciprocity F e) (E L : Extension F) (h : E.field ≤ L.field)
    (χ : FieldCharacter F E) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (ψ : AdditiveCharacter F E) (c : E.fieldˣ)
    (hlin : letI := (fieldData F E).topology;
      ∀ z ∈ (fieldData F E).principalUnits (b + 1 - (b + 1) / 2),
        (χ z : ℂ) = ψ.complex ((c : E.field) * ((z : E.field) - 1)))
    {B : ℕ} (hB : 1 ≤ B)
    (haL : (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) = B + 1)
    (htop : TopLayerInput F E L h b B)
    (d : L.fieldˣ)
    (hd : (fieldData F L).ord (d : L.field) =
      -((fieldData F L).additiveConductor (traceCharacter F E L h ψ) +
        (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ)))
    (hmL : 0 < (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) -
      (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) / 2)
    (hlinL : letI := (fieldData F L).topology;
      ∀ x : (fieldData F L).additiveLattice
          (-(((fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) -
            (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) / 2 : ℕ) :
              ℤ)),
        (restrictCharacter F e E L h χ (RankOneStability.oneAddUnit (fieldData F L) hmL x) :
            ℂ) =
          (traceCharacter F E L h ψ).complex ((d : L.field) * x.val)) :
    E.unitsInclusion L h c * d⁻¹ ∈ (fieldData F L).principalUnits 1 := by
  let TL := fieldData F L
  let := TL.topology
  let := (fieldData F E).topology
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  set aL := (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) with haL'
  have hBA : B < aL := by omega
  have key := mul_inv_mem_principalUnits_of_eq_on_lattice TL (traceCharacter F E L h ψ)
    (c := E.unitsInclusion L h c) (c' := d) hBA hd ?_
  · have h1 : aL - B = 1 := by omega
    rwa [h1] at key
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0, mul_zero, mul_zero]
  have hord : (B : ℤ) ≤ TL.ord x := by
    have h1 : TL.discreteValuation x ≤ WithZero.exp (-(B : ℤ)) := hx
    rw [discreteValuation_eq_exp_neg_ord TL hx0, WithZero.exp_le_exp] at h1
    omega
  have hu0 : (1 + x) ≠ 0 := by
    intro h0
    have hv := RankOneStability.valuation_one_add TL (m := B) (by omega) hx
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  let u : L.fieldˣ := Units.mk0 (1 + x) hu0
  have hxm : x ∈ TL.additiveLattice (-((aL - aL / 2 : ℕ) : ℤ)) :=
    TL.additiveLattice_mono (by omega) hx
  have h2 := hlinL ⟨x, hxm⟩
  have hu : RankOneStability.oneAddUnit TL hmL ⟨x, hxm⟩ = u := Units.ext rfl
  rw [hu] at h2
  obtain ⟨htr, hnorm⟩ := htop x hx0 (by exact_mod_cast hord)
  set τ := @Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra x
    with hτ
  have ht0 : (1 + τ) ≠ 0 := by
    intro h0
    have hv := RankOneStability.valuation_one_add (fieldData F E) (m := b) (by omega) htr
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  let t : E.fieldˣ := Units.mk0 (1 + τ) ht0
  have hnt := hnorm u t rfl rfl
  have hχnt : χ (E.unitsNorm L h u * t⁻¹) = 1 := by
    have hspec := (fieldData F E).multiplicativeConductor_spec χ
    rw [hcond] at hspec
    exact hspec _ hnt
  have htm : t ∈ (fieldData F E).principalUnits (b + 1 - (b + 1) / 2) := by
    have htb : t ∈ (fieldData F E).principalUnits b := by
      refine ⟨RankOneStability.valuation_one_add (fieldData F E) (m := b) (by omega) htr, ?_⟩
      change (fieldData F E).discreteValuation ((1 + τ) - 1) ≤ _
      rw [add_sub_cancel_left]
      exact htr
    exact (fieldData F E).principalUnits_antitone (by omega) htb
  have hχt := hlin t htm
  have h1 : (restrictCharacter F e E L h χ u : ℂ) = ψ.complex ((c : E.field) * τ) := by
    rw [restrictCharacter_apply F he, ← inv_mul_cancel_right (E.unitsNorm L h u) t, map_mul,
      hχnt, one_mul, hχt]
    congr 2
    change (1 + τ) - 1 = τ
    ring
  rw [← h2, h1, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, traceCharacter_apply]
  congr 2
  change Algebra.trace E.field L.field (algebraMap E.field L.field (c : E.field) * x) = _
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/-! ## The approximate witness for one character -/

/-- DH81 4.3 for a character `χ` of `E` of break `b ≥ 1`, relative to a family `U` of
subgroups of `W_E`: if `c` linearizes `χ`, then `c⁻¹` is an approximate witness for `[χ]`
relative to `U b`. Hypotheses: the unit-level theorem for `U`, and for every larger field
`L` with `U b` inside `W_L`, the unit-level theorem at `L` and the approximate Herbrand
input. -/
theorem approximateWitnessOn_characterClass_of_linearization_family {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε) (E : Extension F)
    (U : ℝ → Subgroup (weilSubgroup F E)) (hU : Antitone U) (hUn : ∀ s, (U s).Normal)
    (hUI : ∀ s : ℝ, 0 ≤ s → U s ≤ CommonClosureWeilDeligne.inertia F E)
    (χ : FieldCharacter F E) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F E).multiplicativeConductor χ = b + 1)
    (ψ : AdditiveCharacter F E) (c : E.fieldˣ)
    (hlin : letI := (fieldData F E).topology;
      ∀ z ∈ (fieldData F E).principalUnits (b + 1 - (b + 1) / 2),
        (χ z : ℂ) = ψ.complex ((c : E.field) * ((z : E.field) - 1)))
    (hWE : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F E).topology;
      (U s).map (reciprocityUnits F e E).toMonoidHom = (fieldData F E).principalUnits ⌈s⌉₊)
    (hL : ∀ (L : Extension F) (h : E.field ≤ L.field),
      (∀ g ∈ U b, (g : localWeilGroup F) ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧ ApproximateHerbrandInput F E L h U b) :
    ApproximateWitnessOn F e ε E (U b) ψ (characterClass F e E χ) c⁻¹ := by
  apply approximateWitnessOn_characterClass F hsys E (U b) (hUn b) (hUI b (Nat.cast_nonneg b))
    ψ χ c⁻¹
  intro L h η hNL hη μL
  obtain ⟨hWL, ψH, hcont, hmono, hzero, hmem, htop⟩ := hL L h hNL
  obtain ⟨B, hBψ, haL⟩ := conductor_restrictCharacter_family F E L h χ hcond U hU hWE hWL ψH
    hcont hmono hzero hmem (Nat.cast_nonneg b) le_rfl hNL
  set η' := CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η with hη'
  have hψb0 : 0 ≤ ψH b := hzero ▸ hmono.monotone (Nat.cast_nonneg b)
  have hBpos : 1 ≤ B := by
    have h0 : 0 < ψH b := by
      rw [← hzero]
      apply hmono
      exact_mod_cast hb
    rw [hBψ] at h0
    exact_mod_cast h0
  have hηtriv : (fieldData F L).MultiplicativeTrivialAt η' ⌈ψH b⌉₊ := by
    change ∀ u ∈ (fieldData F L).principalUnits ⌈ψH b⌉₊, η' u = 1
    rw [trivial_iff_of_map_reciprocityUnits F L η' _ _ (hWL _ hψb0), hη',
      CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
    intro g hg
    have hgE := (hmem _ (Nat.cast_nonneg b) g).mpr hg
    exact hη ⟨weilInclusion F E L h g, hgE⟩
  have haη := ((fieldData F L).multiplicativeTrivialAt_iff_conductor_le η' _).mp hηtriv
  rw [hBψ, Nat.ceil_natCast] at haη
  rw [hBψ] at htop
  set χL := restrictCharacter F e E L h χ with hχL
  set ψL := traceCharacter F E L h ψ with hψL
  have hmL : 0 < (fieldData F L).multiplicativeConductor χL -
      (fieldData F L).multiplicativeConductor χL / 2 := by omega
  obtain ⟨d0, hd0, hdord, hlinL⟩ := RankOneStability.exists_deep_linearization (fieldData F L)
    χL ψL hmL (by omega) (by omega)
  let d : L.fieldˣ := Units.mk0 d0 hd0
  have hd : (fieldData F L).ord (d : L.field) =
      -((fieldData F L).additiveConductor ψL + (fieldData F L).multiplicativeConductor χL) := by
    change (fieldData F L).ord d0 = _
    rw [hdord]
    ring
  have hcd := mul_inv_mem_principalUnits_one_of_topLayer F hsys.1 E L h χ hb hcond ψ c hlin
    hBpos haL htop d hd hmL hlinL
  obtain ⟨N, hN⟩ := approximateTwistWitness_of_comparison (fieldData F L) χL ψL (by omega) d hd
    hmL hlinL (E.unitsInclusion L h c) hcd η' (by omega) μL
  refine ⟨N, ?_⟩
  rw [map_inv (E.unitsInclusion L h) c]
  exact hN

/-- The family `baseUpperGroup F` is antitone. -/
theorem baseUpperGroup_antitone : Antitone (baseUpperGroup F) := fun _ _ hst _ hg =>
  upperGroup_antitone F hst hg

/-- DH81 4.3 at the bottom field, relative to the upper groups of `F`. -/
theorem approximateWitnessOn_characterClass_of_linearization {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε)
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (χ : FieldCharacter F (baseExtension F)) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor χ = b + 1)
    (ψ : AdditiveCharacter F (baseExtension F)) (c : (baseExtension F).fieldˣ)
    (hlin : letI := (fieldData F (baseExtension F)).topology;
      ∀ z ∈ (fieldData F (baseExtension F)).principalUnits (b + 1 - (b + 1) / 2),
        (χ z : ℂ) = ψ.complex ((c : (baseExtension F).field) *
          ((z : (baseExtension F).field) - 1)))
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (hL : ∀ (L : Extension F) (h : (baseExtension F).field ≤ L.field),
      (∀ g ∈ baseUpperGroup F b, (g : localWeilGroup F) ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧
        ApproximateHerbrandInput F (baseExtension F) L h (baseUpperGroup F) b) :
    ApproximateWitnessOn F e ε (baseExtension F) (baseUpperGroup F b) ψ
      (characterClass F e (baseExtension F) χ) c⁻¹ :=
  approximateWitnessOn_characterClass_of_linearization_family F hsys (baseExtension F)
    (baseUpperGroup F) (baseUpperGroup_antitone F) (baseUpperGroup_normal F)
    (fun _ hs => baseUpperGroup_le_inertia F hinert hs) χ hb hcond ψ c hlin hWK hL

/-- DH81 4.3 over an intermediate field `E`, relative to its own upper groups. -/
theorem approximateWitnessOn_characterClass_of_linearization_rel {e : ReciprocityFamily F}
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
      (∀ g ∈ intermediateUpperGroup F E b, (g : localWeilGroup F) ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧
        ApproximateHerbrandInput F E L h (intermediateUpperGroup F E) b) :
    ApproximateWitnessOn F e ε E (intermediateUpperGroup F E b) ψ
      (characterClass F e E χ) c⁻¹ :=
  approximateWitnessOn_characterClass_of_linearization_family F hsys E
    (intermediateUpperGroup F E) (intermediateUpperGroup_antitone F E)
    (intermediateUpperGroup_normal F E)
    (fun _ hs => intermediateUpperGroup_le_inertia F E hinert hs) χ hb hcond ψ c hlin hWE hL

/-! ## All clauses of the target for the line of one wild character -/

/-- The conclusion of `VirtualStabilityStatement` for the line `v` of a character `χ` of the
local Weil group whose bottom-field character has conductor `b + 1 ≥ 2` (DH81 4.6 with
4.2(i) in dimension one): the valuation, the exact witness and its coset, and an
approximate witness congruent to it modulo `U^1` with its coset. The exact and the
approximate witness are both the inverse of a linearizer of `χ`. -/
theorem virtualStability_lineBasis
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (hgeo : CommonClosureGeometricStatement.{uF, uF})
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε)
    (χ : localWeilGroup F →ₜ* ℂˣ) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor
      (baseFieldCharacter F e χ) = b + 1)
    (ψ : AdditiveCharacter F (baseExtension F))
    (hLexact : ∀ L : Extension F, (∀ w ∈ upperGroup F ((b : ℝ) / 2), w ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧ HerbrandInput F L b)
    (hLapprox : ∀ (L : Extension F) (h : (baseExtension F).field ≤ L.field),
      (∀ g ∈ baseUpperGroup F b, (g : localWeilGroup F) ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧
        ApproximateHerbrandInput F (baseExtension F) L h (baseUpperGroup F) b)
    (hv : (breakSupport F (generator (lineBasis.{uF, max uF uV} χ))).Nonempty)
    (hpos : PositiveBreakSupport F (generator (lineBasis.{uF, max uF uV} χ))) :
    ∃ γ : (baseExtension F).fieldˣ,
      ((fieldData F (baseExtension F)).ord (γ : (baseExtension F).field) : ℝ) =
          wildArtinSum.{uF, uV} F (generator (lineBasis.{uF, max uF uV} χ)) +
            (LocalWeil.degree F (generator (lineBasis.{uF, max uF uV} χ)) : ℝ) *
              (fieldData F (baseExtension F)).additiveConductor ψ ∧
      ExactWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
        (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ γ ∧
      (∀ γ' : (baseExtension F).fieldˣ,
        ExactWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
            (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ γ' ↔
          γ' * γ⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits
            ⌈minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv / 2⌉₊) ∧
      ∃ γ₀ : (baseExtension F).fieldˣ,
        ApproximateWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
            (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ γ₀ ∧
          γ * γ₀⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits 1 ∧
          ∀ γ₀' : (baseExtension F).fieldˣ,
            ApproximateWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
                (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ γ₀' ↔
              γ₀' * γ₀⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits 1 := by
  let T := fieldData F (baseExtension F)
  have hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊ := fun s hs =>
    baseUpperGroup_map_reciprocityUnits F hreal hinert hcmp e
      (geometric_baseReciprocityCandidate F hgeo e hsys.1) hs
  have h2 : 2 ≤ T.multiplicativeConductor (baseFieldCharacter F e χ) := by
    change 2 ≤ (fieldData F (baseExtension F)).multiplicativeConductor _
    omega
  obtain ⟨c, hc, hlin⟩ := exists_linearization T (baseFieldCharacter F e χ) ψ h2
  have hlab := breakLabel_lineBasis.{uF, max uF uV} F χ hcond hWK
  have hab : T.multiplicativeConductor (baseFieldCharacter F e χ) = b + 1 := hcond
  rw [hab] at hc hlin
  have hmin : minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv = b := by
    rw [minimumBreak_generator, hlab]
  have hex : ExactWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
      (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ c⁻¹ := by
    rw [hmin]
    apply exactWitness_of_exactWitnessOn F hthr
    rw [realizeAtBase_generator_lineBasis F e χ]
    exact exactWitnessOn_characterClass_of_linearization F hsys hinert
      (baseFieldCharacter F e χ) hb hcond ψ c hlin hWK hLexact
  have hap : ApproximateWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
      (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ c⁻¹ := by
    rw [hmin]
    apply approximateWitness_of_approximateWitnessOn F hthr
    rw [realizeAtBase_generator_lineBasis F e χ]
    exact approximateWitnessOn_characterClass_of_linearization F hsys hinert
      (baseFieldCharacter F e χ) hb hcond ψ c hlin hWK hLapprox
  refine ⟨c⁻¹, ?_, hex,
    exactWitness_iff_mem_coset_of_isSystem F hthr hreal hinert hcmp hgeo hsys hv hpos hex,
    c⁻¹, hap, by rw [mul_inv_cancel]; exact one_mem _,
    approximateWitness_iff_mem_coset_of_isSystem F hthr hreal hinert hcmp hgeo hsys hv hpos hap⟩
  rw [Units.val_inv_eq_inv_val, T.ord_inv, hc, wildArtinSum_generator_lineBasis, hlab,
    degree_generator_lineBasis]
  push_cast
  ring

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
