import Langlands.LocalFactor.DeligneHenniartInductionStep
import Langlands.LocalFactor.DeligneHenniartRelativeWitness
import Langlands.LocalFactor.DeligneHenniartNormTrace
import Langlands.LocalFactor.DeligneHenniartIntermediateUnits
import Langlands.LocalFactor.DeligneHenniartExactCoset

/-! # The rank-one twist relation on a larger field (DH81 4.7) -/

noncomputable section

universe uF uV uG uH uW

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The restricted character is the norm pullback (DH81 writes `χ ∘ N_{L/K}`). -/
theorem restrictCharacter_apply {e : ReciprocityFamily F} (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E) (z : L.fieldˣ) :
    restrictCharacter F e E L h χ z = χ (E.unitsNorm L h z) := by
  obtain ⟨v, rfl⟩ := reciprocityUnits_surjective F e L z
  rw [← weilCharacter_apply, weilCharacter_restrictCharacter]
  change weilCharacter F e E χ (weilInclusion F E L h v) = _
  rw [weilCharacter_apply, reciprocityUnits_weilInclusion F he]

/-- On deep elements, the norm pullback of a linearized character is linearized through
the trace character by the same element (DH81 3.3 and 3.6, with `1 + y`). -/
theorem restrictCharacter_one_add {e : ReciprocityFamily F} (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E)
    (ψ : AdditiveCharacter F E) (c : E.fieldˣ) {m A : ℕ} (hm : 0 < m) (hA : 0 < A)
    (hlin : letI := (fieldData F E).topology; ∀ z ∈ (fieldData F E).principalUnits m,
      (χ z : ℂ) = ψ.complex ((c : E.field) * ((z : E.field) - 1)))
    (hχ : ∀ z ∈ (fieldData F E).principalUnits A, χ z = 1)
    (y : L.field) (hy : y ≠ 0) (hy1 : 0 < (fieldData F L).ord y)
    (hR : ((A : ℤ) - 1) * (fieldData F L).ramificationIndex <
      2 * (fieldData F E).ramificationIndex * (fieldData F L).ord y)
    (hT : ((m : ℤ) - 1) * (fieldData F L).ramificationIndex <
      (fieldData F E).ramificationIndex * (fieldData F L).ord y)
    (u : L.fieldˣ) (hu : (u : L.field) = 1 + y) :
    let := (fieldData F L).topology
    (restrictCharacter F e E L h χ u : ℂ) =
      (traceCharacter F E L h ψ).complex ((E.unitsInclusion L h c : L.field) * y) := by
  let := (fieldData F E).topology
  let := (fieldData F L).topology
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower (Padic p) E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field L.field := FiniteDimensional.right F.Carrier E.field L.field
  have key := character_norm_one_add (E.asPadicField (p := p)) (L.asPadicField (p := p))
    (fieldData F E) (fieldData F L) χ.toMonoidHom ψ.complex (c : E.field) hm hA hlin hχ
    y hy hy1 hR hT u hu
  rw [restrictCharacter_apply F he]
  refine key.trans ?_
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, traceCharacter_apply]
  congr 2
  change _ = Algebra.trace E.field L.field (algebraMap E.field L.field (c : E.field) * y)
  rw [← smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/-- DH81 4.7 on one larger field `L`: if the element `c` of `E` linearizes `χ`, then
`c⁻¹` satisfies the rank-one twist relation for the norm pullback of `χ` and every
character `η'` of `L` of small conductor. The depth `t` must satisfy the
norm–trace conditions on `E` and lie between the linearization depth and the
conductor of the pullback on `L`. -/
theorem abelianEpsilonExpression_restrictCharacter_mul {e : ReciprocityFamily F}
    (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field) (χ : FieldCharacter F E)
    (ψ : AdditiveCharacter F E) (c : E.fieldˣ) {m A : ℕ} (hm : 0 < m) (hA : 0 < A)
    (hlin : letI := (fieldData F E).topology; ∀ z ∈ (fieldData F E).principalUnits m,
      (χ z : ℂ) = ψ.complex ((c : E.field) * ((z : E.field) - 1)))
    (hχ : ∀ z ∈ (fieldData F E).principalUnits A, χ z = 1)
    (η : FieldCharacter F L) (μL : HaarMeasure F L) {t : ℕ}
    (hR : ((A : ℤ) - 1) * (fieldData F L).ramificationIndex <
      2 * (fieldData F E).ramificationIndex * t)
    (hT : ((m : ℤ) - 1) * (fieldData F L).ramificationIndex <
      (fieldData F E).ramificationIndex * t)
    (haL : 2 ≤ (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ))
    (htm : (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) -
      (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) / 2 ≤ t)
    (htA : t < (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ))
    (hη : (fieldData F L).multiplicativeConductor η ≤
      (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ) - t)
    (hη2 : 2 * (fieldData F L).multiplicativeConductor η ≤
      (fieldData F L).multiplicativeConductor (restrictCharacter F e E L h χ)) :
    (fieldData F L).abelianEpsilonExpression (restrictCharacter F e E L h χ * η)
        (traceCharacter F E L h ψ) μL =
      (η (E.unitsInclusion L h c⁻¹) : ℂ) *
        (fieldData F L).abelianEpsilonExpression (restrictCharacter F e E L h χ)
          (traceCharacter F E L h ψ) μL := by
  let TL := fieldData F L
  let := TL.topology
  set χL := restrictCharacter F e E L h χ with hχL
  set ψL := traceCharacter F E L h ψ with hψL
  set aL := TL.multiplicativeConductor χL with haLdef
  have hmL : 0 < aL - aL / 2 := by omega
  obtain ⟨c', hc'0, hc'ord, hlin'⟩ := RankOneStability.exists_deep_linearization TL χL ψL
    hmL (by omega) (by omega)
  let d : L.fieldˣ := Units.mk0 c' hc'0
  have hd : TL.ord (d : L.field) = -(TL.additiveConductor ψL + aL) := by
    change TL.ord c' = _
    rw [hc'ord]
    ring
  have heE : (0 : ℤ) < (fieldData F E).ramificationIndex := by
    exact_mod_cast (fieldData F E).ramificationIndex_pos
  set cL := E.unitsInclusion L h c with hcL
  have h_eq : ∀ x ∈ TL.additiveLattice (-(t : ℤ)),
      ψL.complex ((cL : L.field) * x) = ψL.complex ((d : L.field) * x) := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, mul_zero, mul_zero]
    have hord : (t : ℤ) ≤ TL.ord x := by
      have h1 : TL.discreteValuation x ≤ WithZero.exp (-(t : ℤ)) := hx
      rw [discreteValuation_eq_exp_neg_ord TL hx0, WithZero.exp_le_exp] at h1
      omega
    have hu0 : (1 + x) ≠ 0 := by
      intro h0
      have hv := RankOneStability.valuation_one_add TL (m := t) (by omega) hx
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    let u : L.fieldˣ := Units.mk0 (1 + x) hu0
    have hord' : (t : ℤ) ≤ (fieldData F L).ord x := hord
    have ht1 : 1 ≤ t := by omega
    have h1 := restrictCharacter_one_add F he E L h χ ψ c hm hA hlin hχ x hx0 (by omega)
      (by nlinarith) (by nlinarith) u rfl
    have hxm : x ∈ TL.additiveLattice (-((aL - aL / 2 : ℕ) : ℤ)) :=
      TL.additiveLattice_mono (by omega) hx
    have h2 := hlin' ⟨x, hxm⟩
    have hu : RankOneStability.oneAddUnit TL hmL ⟨x, hxm⟩ = u := Units.ext rfl
    rw [hu] at h2
    exact h1.symm.trans h2
  have hcd := mul_inv_mem_principalUnits_of_eq_on_lattice TL ψL htA hd h_eq
  have hlin'' : ∀ h' : TL.additiveLattice (-((aL - aL / 2 : ℕ) : ℤ)),
      (χL (RankOneStability.oneAddUnit TL hmL h') : ℂ) = ψL.complex ((d : L.field) * h'.val) :=
    hlin'
  have hd' : TL.ord (d : L.field) = -(TL.additiveConductor ψL + TL.multiplicativeConductor χL) :=
    hd
  rw [abelianEpsilonExpression_mul_of_comparison TL χL η ψL μL haL hη2 d hd' hmL hlin'' cL hcd hη,
    map_inv (E.unitsInclusion L h) c, map_inv η]

/-! ## The depth bookkeeping of DH81 4.7 -/

/-- The integer inequalities of DH81 4.7 for the depth `t = ⌊e_L b / (2 e_E)⌋ + 1`.
Here `b` is the break of `χ`, `B = ψ(b)` the break of its norm pullback, `ψh = ψ(b/2)`,
and the Herbrand inputs are the slope relation `e_E (B - ψh) = e_L b / 2` beyond the
ramification of `L/E`, the bound `e_E B ≤ e_L b`, and `0 < ψh`. -/
theorem depth_conditions {eE eL b B aη : ℕ} {ψh : ℝ} (heE : 0 < eE)
    (hslope : (eE : ℝ) * (B - ψh) = eL * (b / 2)) (hle : eE * B ≤ eL * b) (hpos : 0 < ψh)
    (haη : (aη : ℝ) ≤ ⌈ψh⌉) :
    ((b + 1 : ℕ) - 1 : ℤ) * eL < 2 * eE * ((eL * b / (2 * eE) + 1 : ℕ) : ℤ) ∧
    (((b + 1 - (b + 1) / 2 : ℕ) : ℤ) - 1) * eL < eE * ((eL * b / (2 * eE) + 1 : ℕ) : ℤ) ∧
    2 ≤ B + 1 ∧
    B + 1 - (B + 1) / 2 ≤ eL * b / (2 * eE) + 1 ∧
    eL * b / (2 * eE) + 1 < B + 1 ∧
    aη ≤ B + 1 - (eL * b / (2 * eE) + 1) ∧
    2 * aη ≤ B + 1 := by
  have h2e : 0 < 2 * eE := by omega
  have hqx' : (2 * eE) * (eL * b / (2 * eE)) ≤ eL * b := Nat.mul_div_le (eL * b) (2 * eE)
  have hxq' : eL * b < (2 * eE) * (eL * b / (2 * eE) + 1) := Nat.lt_mul_div_succ (eL * b) h2e
  have hBle : B / 2 ≤ eL * b / (2 * eE) := by
    rw [Nat.le_div_iff_mul_le h2e]
    have := Nat.div_mul_le_self B 2
    calc B / 2 * (2 * eE) = (B / 2 * 2) * eE := by ring
      _ ≤ B * eE := Nat.mul_le_mul_right _ this
      _ = eE * B := by ring
      _ ≤ eL * b := hle
  generalize hq : eL * b / (2 * eE) = q at hqx' hxq' hBle ⊢
  have hqx : (2 * eE) * q ≤ eL * b := hqx'
  have hxq : eL * b < (2 * eE) * (q + 1) := hxq'
  -- `e_E B > e_L b / 2` from the slope and positivity
  have hB : (eE : ℝ) * B > eL * b / 2 := by
    have h1 : (eE : ℝ) * B = eL * (b / 2) + eE * ψh := by linarith
    have h2 : (0 : ℝ) < eE * ψh := mul_pos (by exact_mod_cast heE) hpos
    linarith
  have hBq : q < B := by
    have h3 : ((2 * eE * q : ℕ) : ℝ) ≤ eL * b := by exact_mod_cast hqx
    push_cast at h3
    by_contra hcon
    push Not at hcon
    have h4 : (B : ℝ) ≤ q := by exact_mod_cast hcon
    have h5 : (eE : ℝ) * B ≤ eE * q := mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  -- `⌈ψh⌉ = B - q`
  have hceil : (⌈ψh⌉ : ℤ) ≤ (B : ℤ) - q := by
    rw [Int.ceil_le]
    have h6 : (eE : ℝ) * ψh = eE * B - eL * b / 2 := by linarith
    have h7 : (2 * eE * q : ℝ) ≤ eL * b := by exact_mod_cast hqx
    have heR : (0 : ℝ) < eE := by exact_mod_cast heE
    push_cast
    by_contra hcon
    push Not at hcon
    have h9 : (eE : ℝ) * (B - q) < eE * ψh := mul_lt_mul_of_pos_left hcon heR
    nlinarith
  have haηZ : (aη : ℤ) ≤ (B : ℤ) - q := by
    have : (aη : ℝ) ≤ ((B : ℤ) - q : ℤ) := haη.trans (by exact_mod_cast hceil)
    exact_mod_cast this
  have hleR : eE * B ≤ eL * b := hle
  refine ⟨?_, ?_, by omega, ?_, by omega, by omega, ?_⟩
  · push_cast
    have : (eL * b : ℤ) < 2 * eE * (q + 1) := by exact_mod_cast hxq
    nlinarith
  · have hb2 : b + 1 - (b + 1) / 2 - 1 = b / 2 := by omega
    have hlhs : (((b + 1 - (b + 1) / 2 : ℕ) : ℤ) - 1) = ((b / 2 : ℕ) : ℤ) := by omega
    rw [hlhs]
    have h9 : (2 * (b / 2)) * eL ≤ b * eL := Nat.mul_le_mul_right _ (Nat.mul_div_le b 2)
    have h10 : ((b / 2 : ℕ) : ℤ) * eL * 2 ≤ (eL * b : ℕ) := by
      push_cast
      have : ((2 * (b / 2) * eL : ℕ) : ℤ) ≤ ((b * eL : ℕ) : ℤ) := by exact_mod_cast h9
      push_cast at this
      linarith
    have : (eL * b : ℤ) < 2 * eE * (q + 1) := by exact_mod_cast hxq
    push_cast at h10 ⊢
    nlinarith
  · omega
  · -- `B ≤ 2 q + 1`
    have h12 : B ≤ 2 * q + 1 := by
      by_contra hcon
      push Not at hcon
      have h13 : eE * (2 * q + 2) ≤ eE * B := Nat.mul_le_mul_left _ hcon
      have : eL * b < 2 * eE * (q + 1) := hxq
      nlinarith
    omega

/-! ## Conductors on the larger field -/

open VirtualRepresentation.LocalWeil.Ramification Ramification.Padic

private theorem mem_baseWeil_aux (w : localWeilGroup F) :
    w ∈ weilSubgroup F (baseExtension F) := by
  rw [baseWeil_eq_top]
  trivial

/-- A field character is trivial on a unit group that is the reciprocity image of a
subgroup of the Weil subgroup exactly when its Weil character is trivial on that
subgroup. -/
theorem trivial_iff_of_map_reciprocityUnits {e : ReciprocityFamily F}
    (E : Extension F) (η : FieldCharacter F E) (H : Subgroup (weilSubgroup F E))
    (U : Subgroup E.fieldˣ)
    (hH : letI := (fieldData F E).topology; H.map (reciprocityUnits F e E).toMonoidHom = U) :
    (∀ u ∈ U, η u = 1) ↔ ∀ g ∈ H, weilCharacter F e E η g = 1 := by
  let := (fieldData F E).topology
  constructor
  · intro h g hg
    rw [weilCharacter_apply]
    apply h
    rw [← hH]
    exact ⟨g, hg, rfl⟩
  · intro h u hu
    rw [← hH] at hu
    obtain ⟨g, hg, rfl⟩ := hu
    exact h g hg

/-- DH81 3.3.1 in the case used by 4.7: with `χ` of break `b` on the bottom field and the
upper group of index `b/2` inside `W_L`, the norm pullback of `χ` to `L` is trivial on
the principal units of level `⌈ψ(v)⌉` exactly when `b < v`, for `v ≥ b/2`. Here `ψ` is
any function satisfying Herbrand's subgroup formula for `L`. -/
theorem restrictCharacter_trivial_iff {e : ReciprocityFamily F}
    (L : Extension F) (h : (baseExtension F).field ≤ L.field)
    (χ : FieldCharacter F (baseExtension F)) {b : ℕ}
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor χ = b + 1)
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (ψH : ℝ → ℝ)
    (hmem : ∀ v : ℝ, 0 ≤ v → ∀ w : localWeilGroup (L.asPadicField (p := p)),
      (intermediateWeilEquiv F L w : localWeilGroup F) ∈ upperGroup F v ↔
        w ∈ upperGroup (L.asPadicField (p := p)) (ψH v))
    (hNL : ∀ w ∈ upperGroup F ((b : ℝ) / 2), w ∈ weilSubgroup F L)
    {v : ℝ} (hv : (b : ℝ) / 2 ≤ v) (hψv : 0 ≤ ψH v) :
    (∀ u ∈ (fieldData F L).principalUnits ⌈ψH v⌉₊,
        restrictCharacter F e (baseExtension F) L h χ u = 1) ↔ (b : ℝ) < v := by
  have hv0 : 0 ≤ v := le_trans (by positivity) hv
  rw [trivial_iff_of_map_reciprocityUnits F L _ _ _ (hWL _ hψv),
    weilCharacter_restrictCharacter]
  have hmemL : ∀ g : weilSubgroup F L,
      g ∈ intermediateUpperGroup F L (ψH v) ↔ (g : localWeilGroup F) ∈ upperGroup F v := by
    intro g
    rw [mem_intermediateUpperGroup, ← hmem v hv0]
    simp
  have hstep : (∀ g ∈ intermediateUpperGroup F L (ψH v),
        ((weilCharacter F e (baseExtension F) χ).comp (weilInclusion F (baseExtension F) L h)) g = 1) ↔
      ∀ x ∈ baseUpperGroup F v, weilCharacter F e (baseExtension F) χ x = 1 := by
    constructor
    · intro H x hx
      have hxL : (x : localWeilGroup F) ∈ weilSubgroup F L :=
        hNL _ (upperGroup_antitone F hv hx)
      have := H ⟨x, hxL⟩ ((hmemL _).mpr hx)
      exact this
    · intro H g hg
      exact H _ ((hmemL g).mp hg)
  rw [hstep, ← trivial_iff_of_map_reciprocityUnits F (baseExtension F) χ _ _ (hWK v hv0)]
  change (fieldData F (baseExtension F)).MultiplicativeTrivialAt χ ⌈v⌉₊ ↔ _
  rw [PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le, hcond,
    Nat.add_one_le_iff, Nat.lt_ceil]

/-- The conductor of the norm pullback: under the hypotheses of
`restrictCharacter_trivial_iff`, with `ψ` continuous, strictly increasing and `ψ 0 = 0`,
the value `ψ(b)` is a natural number `B` and the pullback has conductor `B + 1`. -/
theorem conductor_restrictCharacter {e : ReciprocityFamily F}
    (L : Extension F) (h : (baseExtension F).field ≤ L.field)
    (χ : FieldCharacter F (baseExtension F)) {b : ℕ}
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor χ = b + 1)
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (ψH : ℝ → ℝ) (hcont : Continuous ψH) (hmono : StrictMono ψH) (hzero : ψH 0 = 0)
    (hmem : ∀ v : ℝ, 0 ≤ v → ∀ w : localWeilGroup (L.asPadicField (p := p)),
      (intermediateWeilEquiv F L w : localWeilGroup F) ∈ upperGroup F v ↔
        w ∈ upperGroup (L.asPadicField (p := p)) (ψH v))
    (hNL : ∀ w ∈ upperGroup F ((b : ℝ) / 2), w ∈ weilSubgroup F L) :
    ∃ B : ℕ, ψH b = B ∧
      (fieldData F L).multiplicativeConductor (restrictCharacter F e (baseExtension F) L h χ) =
        B + 1 := by
  set T := fieldData F L
  set χL := restrictCharacter F e (baseExtension F) L h χ
  have hb2 : (b : ℝ) / 2 ≤ b := by
    have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  have hψnn : ∀ v : ℝ, 0 ≤ v → 0 ≤ ψH v := fun v hv => hzero ▸ hmono.monotone hv
  have hψb := hψnn b (Nat.cast_nonneg b)
  have key := fun (v : ℝ) (hv : (b : ℝ) / 2 ≤ v) =>
    restrictCharacter_trivial_iff F L h χ hcond hWK hWL ψH hmem hNL hv
      (hψnn v (le_trans (by positivity) hv))
  -- not trivial at `ψ(b)`
  have hnot : ¬ T.MultiplicativeTrivialAt χL ⌈ψH b⌉₊ := by
    intro htr
    exact lt_irrefl _ ((key b hb2).mp htr)
  have hlow : ⌈ψH b⌉₊ < T.multiplicativeConductor χL := by
    by_contra hle
    push Not at hle
    exact hnot ((T.multiplicativeTrivialAt_iff_conductor_le χL _).mpr hle)
  -- trivial just above `ψ(b)`
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

/-! ## The dimension-one exact witness at the bottom field -/

/-- The Herbrand input for one larger field `L`, at the break `b`: a continuous strictly
increasing function `ψ` with `ψ 0 = 0` satisfying Herbrand's subgroup formula for `L`,
with slope `e_L / e_K` between `b/2` and `b`, and bounded by that slope. -/
def HerbrandInput (L : Extension F) (b : ℕ) : Prop :=
  ∃ ψH : ℝ → ℝ, Continuous ψH ∧ StrictMono ψH ∧ ψH 0 = 0 ∧
    (∀ v : ℝ, 0 ≤ v → ∀ w : localWeilGroup (L.asPadicField (p := p)),
      (intermediateWeilEquiv F L w : localWeilGroup F) ∈ upperGroup F v ↔
        w ∈ upperGroup (L.asPadicField (p := p)) (ψH v)) ∧
    ((fieldData F (baseExtension F)).ramificationIndex : ℝ) * (ψH b - ψH ((b : ℝ) / 2)) =
      (fieldData F L).ramificationIndex * ((b : ℝ) / 2) ∧
    ((fieldData F (baseExtension F)).ramificationIndex : ℝ) * ψH b ≤
      (fieldData F L).ramificationIndex * (b : ℝ)

/-- DH81 Lemma 4.7 for a character of the bottom field: if `c` linearizes `χ` (of break
`b ≥ 1`), then `c⁻¹` is an exact witness for `[χ]` relative to the upper group of index
`b/2`. The unit-level theorems at the bottom field and at every larger field `L` whose
Weil subgroup contains that upper group, and the Herbrand input for each such `L`, are
hypotheses. -/
theorem exactWitnessOn_characterClass_of_linearization {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε)
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (χ : FieldCharacter F (baseExtension F)) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor χ = b + 1)
    (ψ : AdditiveCharacter F (baseExtension F)) (c : (baseExtension F).fieldˣ)
    (hlin : letI := (fieldData F (baseExtension F)).topology;
      ∀ z ∈ (fieldData F (baseExtension F)).principalUnits (b + 1 - (b + 1) / 2),
        (χ z : ℂ) = ψ.complex ((c : (baseExtension F).field) * ((z : (baseExtension F).field) - 1)))
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (hL : ∀ L : Extension F, (∀ w ∈ upperGroup F ((b : ℝ) / 2), w ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧ HerbrandInput F L b) :
    ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F ((b : ℝ) / 2)) ψ
      (characterClass F e (baseExtension F) χ) c⁻¹ := by
  have hb2 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  apply exactWitnessOn_characterClass F hsys (baseExtension F) _ (baseUpperGroup_normal F _)
    (baseUpperGroup_le_inertia F hinert hb2) ψ χ c⁻¹
  intro L h η hNL hη μL
  have hNL' : ∀ w ∈ upperGroup F ((b : ℝ) / 2), w ∈ weilSubgroup F L := fun w hw =>
    hNL ⟨w, mem_baseWeil_aux F w⟩ hw
  obtain ⟨hWL, ψH, hcont, hmono, hzero, hmem, hslope, hle⟩ := hL L hNL'
  obtain ⟨B, hBψ, haL⟩ := conductor_restrictCharacter F L h χ hcond hWK hWL ψH hcont hmono
    hzero hmem hNL'
  set η' := CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η with hη'
  have hψh0 : 0 ≤ ψH ((b : ℝ) / 2) := hzero ▸ hmono.monotone hb2
  have hψhpos : 0 < ψH ((b : ℝ) / 2) := by
    rw [← hzero]
    apply hmono
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  -- the conductor of `η'` is at most `⌈ψ(b/2)⌉`
  have hηtriv : (fieldData F L).MultiplicativeTrivialAt η' ⌈ψH ((b : ℝ) / 2)⌉₊ := by
    change ∀ u ∈ (fieldData F L).principalUnits ⌈ψH ((b : ℝ) / 2)⌉₊, η' u = 1
    rw [trivial_iff_of_map_reciprocityUnits F L η' _ _ (hWL _ hψh0), hη',
      CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
    intro g hg
    have hgF : (g : localWeilGroup F) ∈ upperGroup F ((b : ℝ) / 2) := by
      rw [mem_intermediateUpperGroup, ← hmem _ hb2] at hg
      simpa using hg
    have := hη ⟨⟨g, mem_baseWeil_aux F g⟩, hgF⟩
    exact this
  have haη := ((fieldData F L).multiplicativeTrivialAt_iff_conductor_le η' _).mp hηtriv
  -- the depth bookkeeping
  have heK : 0 < (fieldData F (baseExtension F)).ramificationIndex :=
    (fieldData F (baseExtension F)).ramificationIndex_pos
  rw [hBψ] at hslope hle
  have hleN : (fieldData F (baseExtension F)).ramificationIndex * B ≤
      (fieldData F L).ramificationIndex * b := by exact_mod_cast hle
  have haηR : ((fieldData F L).multiplicativeConductor η' : ℝ) ≤ ⌈ψH ((b : ℝ) / 2)⌉ := by
    have h1 : ((fieldData F L).multiplicativeConductor η' : ℝ) ≤ (⌈ψH ((b : ℝ) / 2)⌉₊ : ℝ) := by
      exact_mod_cast haη
    have h2 : ((⌈ψH ((b : ℝ) / 2)⌉₊ : ℕ) : ℤ) = ⌈ψH ((b : ℝ) / 2)⌉ :=
      Int.natCast_ceil_eq_ceil hψh0
    calc ((fieldData F L).multiplicativeConductor η' : ℝ) ≤ (⌈ψH ((b : ℝ) / 2)⌉₊ : ℝ) := h1
      _ = ((⌈ψH ((b : ℝ) / 2)⌉₊ : ℤ) : ℝ) := by norm_cast
      _ = (⌈ψH ((b : ℝ) / 2)⌉ : ℝ) := by rw [h2]
  obtain ⟨hR, hT, h2L, htm, htA, hηt, hη2⟩ := depth_conditions heK hslope hleN hψhpos haηR
  rw [← haL] at h2L htm htA hηt hη2
  have hm : 0 < b + 1 - (b + 1) / 2 := by omega
  have hχA : ∀ z ∈ (fieldData F (baseExtension F)).principalUnits (b + 1), χ z = 1 := by
    rw [← hcond]
    exact (fieldData F (baseExtension F)).multiplicativeConductor_spec χ
  have := abelianEpsilonExpression_restrictCharacter_mul F hsys.1 (baseExtension F) L h χ ψ c
    hm (by omega) hlin hχA η' μL hR hT h2L htm htA hηt hη2
  exact this

/-! ## The target's clauses for a single wild character -/

section Target

/-- A linearizing element in principal-unit form, from the published deep linearization. -/
theorem exists_linearization {G : PadicField.{uF} p} (T : G.TopologicalData)
    (χ : @HarmonicAnalysis.Quasicharacter G.Carrier _ T.topology)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter G.Carrier _ T.topology)
    (ha : 2 ≤ T.multiplicativeConductor χ) :
    letI := T.topology
    ∃ c : G.Carrierˣ, T.ord (c : G.Carrier) =
        -((T.multiplicativeConductor χ : ℤ) + T.additiveConductor ψ) ∧
      ∀ z ∈ T.principalUnits (T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2),
        (χ z : ℂ) = ψ.complex ((c : G.Carrier) * ((z : G.Carrier) - 1)) := by
  let := T.topology
  set a := T.multiplicativeConductor χ
  have hm : 0 < a - a / 2 := by omega
  obtain ⟨c, hc0, hcord, hlin⟩ := RankOneStability.exists_deep_linearization T χ ψ hm
    (by omega) (by omega)
  refine ⟨Units.mk0 c hc0, hcord, fun z hz => ?_⟩
  have hx : (z : G.Carrier) - 1 ∈ T.additiveLattice (-((a - a / 2 : ℕ) : ℤ)) := hz.2
  have h1 := hlin ⟨_, hx⟩
  have hu : RankOneStability.oneAddUnit T hm ⟨_, hx⟩ = z := by
    apply Units.ext
    simp
  rw [hu] at h1
  exact h1

private theorem continuousRestrict_characterClass_aux {G : Type uG} {H : Type uH} [Group G]
    [Group H] [TopologicalSpace G] [TopologicalSpace H] (φ : H →ₜ* G) (η : G →ₜ* ℂˣ) :
    ExactGrothendieckGroup.continuousRestrict.{uG, uH, uW} φ
        (ExactGrothendieckGroup.characterClass.{uG, uW} η) =
      ExactGrothendieckGroup.characterClass.{uH, uW} (η.comp φ) := by
  change ExactGrothendieckGroup.restrict _ _ _ _ (ExactGrothendieckGroup.ofRepresentation _ _) = _
  rw [ExactGrothendieckGroup.restrict_ofRepresentation]
  exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ (Representation.Equiv.refl _)

/-- The bottom field character attached to a character of the local Weil group. -/
def baseFieldCharacter (e : ReciprocityFamily F) (χ : localWeilGroup F →ₜ* ℂˣ) :
    FieldCharacter F (baseExtension F) :=
  CommonClosureSpectralAnalytic.fieldCharacterEquiv F e (baseExtension F)
    (χ.comp (baseWeilInclusion F))

theorem realizeAtBase_generator_lineBasis (e : ReciprocityFamily F)
    (χ : localWeilGroup F →ₜ* ℂˣ) :
    realizeAtBase.{uF, uV} F (generator (lineBasis.{uF, max uF uV} χ)) =
      characterClass F e (baseExtension F) (baseFieldCharacter F e χ) := by
  unfold realizeAtBase
  rw [LinearMap.comp_apply, realizeExact_generator_lineBasis,
    continuousRestrict_characterClass_aux]
  change _ = ExactGrothendieckGroup.characterClass
    (weilCharacter F e (baseExtension F) (baseFieldCharacter F e χ))
  rw [baseFieldCharacter, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]

end Target

/-- The character line is trivial at `r` exactly when the character is trivial on the
upper group of index `r`. -/
theorem isTrivialAt_characterLine_iff (χ : localWeilGroup F →ₜ* ℂˣ) (r : ℝ) :
    IsTrivialAt F (FiniteRepresentation.characterLine.{uF, uW} χ.toMonoidHom) r ↔
      ∀ w ∈ upperGroup F r, χ w = 1 := by
  constructor
  · intro h w hw
    have h1 := LinearMap.congr_fun (h w hw) (ULift.up (1 : ℂ))
    change ((χ w : ℂˣ) : ℂ) • ULift.up (1 : ℂ) = ULift.up 1 at h1
    apply Units.ext
    have h2 := congrArg ULift.down h1
    simpa using h2
  · intro h w hw
    apply LinearMap.ext
    intro v
    change ((χ w : ℂˣ) : ℂ) • v = v
    rw [h w hw, Units.val_one, one_smul]

/-- The label of the line of a character whose bottom-field character has conductor
`b + 1` is `b`, given the unit-level theorem at the bottom field. -/
theorem breakLabel_lineBasis {e : ReciprocityFamily F} (χ : localWeilGroup F →ₜ* ℂˣ) {b : ℕ}
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor
      (baseFieldCharacter F e χ) = b + 1)
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊) :
    breakLabel F (lineBasis.{uF, uW} χ) = b := by
  have hset : trivialityThresholds F (FiniteRepresentation.characterLine.{uF, uW} χ.toMonoidHom) =
      Set.Ioi (b : ℝ) := by
    ext r
    change (0 ≤ r ∧ _) ↔ (b : ℝ) < r
    rw [isTrivialAt_characterLine_iff]
    constructor
    · rintro ⟨hr, htr⟩
      have h1 : ∀ x ∈ baseUpperGroup F r,
          weilCharacter F e (baseExtension F) (baseFieldCharacter F e χ) x = 1 := by
        intro x hx
        rw [baseFieldCharacter, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
        exact htr _ hx
      rw [← trivial_iff_of_map_reciprocityUnits F (baseExtension F) _ _ _ (hWK r hr)] at h1
      have h2 := ((fieldData F (baseExtension F)).multiplicativeTrivialAt_iff_conductor_le
        _ _).mp h1
      rw [hcond, Nat.add_one_le_iff, Nat.lt_ceil] at h2
      exact h2
    · intro hr
      have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg b) hr.le
      refine ⟨hr0, fun w hw => ?_⟩
      have h1 : (fieldData F (baseExtension F)).MultiplicativeTrivialAt
          (baseFieldCharacter F e χ) ⌈r⌉₊ := by
        rw [PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le, hcond,
          Nat.add_one_le_iff, Nat.lt_ceil]
        exact hr
      have h2 := (trivial_iff_of_map_reciprocityUnits F (baseExtension F) _ _ _ (hWK r hr0)).mp h1
      have h3 := h2 ⟨w, mem_baseWeil_aux F w⟩ hw
      rw [baseFieldCharacter, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv] at h3
      exact h3
  change lastBreak F _ = b
  rw [lastBreak, hset, csInf_Ioi]

theorem breakSupport_generator (bb : LocalWeil.Basis.{uF, uW} F) :
    breakSupport F (generator bb) = {breakLabel F bb} := by
  classical
  simp [breakSupport, generator]

theorem minimumBreak_generator (bb : LocalWeil.Basis.{uF, uW} F)
    (hv : (breakSupport F (generator bb)).Nonempty) :
    minimumBreak F (generator bb) hv = breakLabel F bb := by
  simp only [minimumBreak, breakSupport_generator, Finset.min'_singleton]

theorem wildArtinSum_generator_lineBasis (χ : localWeilGroup F →ₜ* ℂˣ) :
    wildArtinSum.{uF, uV} F (generator (lineBasis.{uF, max uF uV} χ)) =
      1 + breakLabel F (lineBasis.{uF, max uF uV} χ) := by
  unfold wildArtinSum generator
  rw [Finsupp.sum_single_index (by simp)]
  have h1 : (((lineBasis.{uF, max uF uV} χ).1 : ℕ+) : ℕ) = 1 := rfl
  rw [h1]
  simp

/-- The exact clause and the valuation of `VirtualStabilityStatement` for the line of a
single wild character `χ` of the local Weil group (DH81 Lemma 4.7 and 4.2.2 in
dimension one), under the unit-level and Herbrand hypotheses of
`exactWitnessOn_characterClass_of_linearization`. -/
theorem exists_exactWitness_lineBasis
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε)
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (χ : localWeilGroup F →ₜ* ℂˣ) {b : ℕ} (hb : 1 ≤ b)
    (hcond : (fieldData F (baseExtension F)).multiplicativeConductor
      (baseFieldCharacter F e χ) = b + 1)
    (ψ : AdditiveCharacter F (baseExtension F))
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (hL : ∀ L : Extension F, (∀ w ∈ upperGroup F ((b : ℝ) / 2), w ∈ weilSubgroup F L) →
      (∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
        (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
          (fieldData F L).principalUnits ⌈s⌉₊) ∧ HerbrandInput F L b) :
    ∃ γ : (baseExtension F).fieldˣ,
      ((fieldData F (baseExtension F)).ord (γ : (baseExtension F).field) : ℝ) =
          wildArtinSum.{uF, uV} F (generator (lineBasis.{uF, max uF uV} χ)) +
            (LocalWeil.degree F (generator (lineBasis.{uF, max uF uV} χ)) : ℝ) *
              (fieldData F (baseExtension F)).additiveConductor ψ ∧
      ∀ hv : (breakSupport F (generator (lineBasis.{uF, max uF uV} χ))).Nonempty,
        ExactWitness F e ε (generator (lineBasis.{uF, max uF uV} χ))
          (minimumBreak F (generator (lineBasis.{uF, max uF uV} χ)) hv) ψ γ := by
  let T := fieldData F (baseExtension F)
  have h2 : 2 ≤ T.multiplicativeConductor (baseFieldCharacter F e χ) := by
    change 2 ≤ (fieldData F (baseExtension F)).multiplicativeConductor _
    omega
  obtain ⟨c, hc, hlin⟩ := exists_linearization T (baseFieldCharacter F e χ) ψ h2
  have hlab := breakLabel_lineBasis.{uF, max uF uV} F χ hcond hWK
  refine ⟨c⁻¹, ?_, fun hv => ?_⟩
  · have hc' := hc
    rw [show T.multiplicativeConductor (baseFieldCharacter F e χ) = b + 1 from hcond] at hc'
    rw [Units.val_inv_eq_inv_val, T.ord_inv, hc', wildArtinSum_generator_lineBasis, hlab,
      degree_generator_lineBasis]
    push_cast
    ring
  · rw [minimumBreak_generator, hlab]
    apply exactWitness_of_exactWitnessOn F hthr
    rw [realizeAtBase_generator_lineBasis F e χ]
    have hlin' := hlin
    rw [show T.multiplicativeConductor (baseFieldCharacter F e χ) = b + 1 from hcond] at hlin'
    exact exactWitnessOn_characterClass_of_linearization F hsys hinert
      (baseFieldCharacter F e χ) hb hcond ψ c hlin' hWK hL

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
