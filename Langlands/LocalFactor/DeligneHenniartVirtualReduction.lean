import Langlands.LocalFactor.DeligneHenniartRelativeHerbrand
import Langlands.LocalFactor.DeligneHenniartLastBreak
import Langlands.LocalFactor.DeligneHenniartApproximateCoset
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor

/-!
# Deligne--Henniart virtual stability from its arithmetic inputs

DH81 4.5 and 4.8 for the generators of the kernel span, then their assembly.

For an inducing character `η` of `W_L` that is nontrivial on `W_F^α` and trivial above `α`
(`α > 0`), this module computes the break `ψ_{L/F}(α)` and conductor of `η`, proves the
valuation identity `e_F (ψ_{L/F}(α) + 1 + n(ψ ∘ Tr)) = e_L (α + 1 + n(ψ))`, and builds
one witness of `Ind_{W_L}^{W_F} [η]` at the bottom field that is exact relative to
`W_F^{α/2}` and approximate relative to `W_F^α` (`IsLabelWitness`). These witnesses are
multiplied over the kernel span of one basis class (DH81 4.5), then over the signed
constituents of a lattice element. With the Library's coset theorems
`exactWitness_iff_mem_coset_of_isSystem` and `approximateWitness_iff_mem_coset_of_isSystem`
this gives `VirtualStabilityStatement` from four arithmetic propositions of the Library
(`virtualStability_of_inputs`).
-/

noncomputable section

set_option linter.style.haveILetI false

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure Weil.Local VirtualRepresentation.LocalWeil.Ramification
open Ramification.HerbrandBridge Ramification.Padic LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-! ## Index and degree -/

/-- Pulling back an open subgroup along a homomorphism with dense image preserves the index. -/
theorem subgroup_index_comap_of_denseRange {G' G : Type*} [Group G'] [Group G]
    [TopologicalSpace G] [ContinuousMul G] {φ : G' →* G} (hφ : DenseRange φ)
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (H.comap φ).index = H.index := by
  have key : ∀ x y : G',
      QuotientGroup.leftRel (H.comap φ) x y ↔ QuotientGroup.leftRel H (φ x) (φ y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· ∈ H) (by rw [φ.map_mul, φ.map_inv]))
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' φ fun x y => (key x y).mp) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun x => ?_
    have hopen : IsOpen ((fun g => x⁻¹ * g) ⁻¹' (H : Set G)) :=
      hH.preimage (continuous_const_mul _)
    obtain ⟨y, hy⟩ := hφ.exists_mem_open hopen ⟨x, by simp [H.one_mem]⟩
    refine ⟨Quotient.mk'' y, ?_⟩
    change Quotient.mk'' (φ y) = Quotient.mk'' x
    rw [Quotient.eq'', QuotientGroup.leftRel_apply]
    simpa using H.inv_mem hy

/-- `[W_F : W_L] = [L : F]`. -/
theorem weilSubgroup_index (L : Extension F) :
    (weilSubgroup F L).index = Module.finrank F.Carrier L.field := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact subgroup_index_comap_of_denseRange (φ := (localProjection F).toMonoidHom)
    (localProjection_denseRange F) _ (IntermediateField.fixingSubgroup_isOpen L.field)

/-- Induction from `W_L` to the base Weil group multiplies the degree by `[L : F]`. -/
theorem degree_induce_base (L : Extension F) (hL : (baseExtension F).field ≤ L.field)
    (x : Virtual.{uF, uV} F L) :
    degree F (baseExtension F) (induce F (baseExtension F) L hL x) =
      (Module.finrank F.Carrier L.field : ℤ) * degree F L x := by
  rw [degree_induce, ← weilSubgroup_index F L]
  congr 2
  change (weilSubgroup F L).relIndex (weilSubgroup F (baseExtension F)) = _
  rw [baseWeil_eq_top, Subgroup.relIndex_top_right]

/-- The tower formula `[E : ℚ_p] = [E : F] [F : ℚ_p]` for a `p`-adic field over `F`. -/
theorem finrank_padic_tower {E : PadicField.{uF} p} [Algebra F.Carrier E.Carrier]
    (h : ∀ q : Padic p, algebraMap (Padic p) E.Carrier q =
      algebraMap F.Carrier E.Carrier (algebraMap (Padic p) F.Carrier q)) :
    Module.finrank (Padic p) E.Carrier =
      Module.finrank F.Carrier E.Carrier * Module.finrank (Padic p) F.Carrier := by
  letI : IsScalarTower (Padic p) F.Carrier E.Carrier := IsScalarTower.of_algebraMap_eq h
  rw [← Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier, mul_comm]

/-- `e_L f_L = [L : F] e_K f_K`, where `K` is the bottom field. -/
theorem ramificationIndex_mul_residueDegree_eq (L : Extension F) :
    (fieldData F L).ramificationIndex * (fieldData F L).residueDegree =
      Module.finrank F.Carrier L.field *
        ((fieldData F (baseExtension F)).ramificationIndex *
          (fieldData F (baseExtension F)).residueDegree) := by
  have hL := (fieldData F L).ramificationIndex_mul_residueDegree.trans
    (finrank_padic_tower F (E := L.asPadicField (p := p)) fun _ => rfl)
  have hK := (fieldData F (baseExtension F)).ramificationIndex_mul_residueDegree.trans
    (finrank_padic_tower F (E := (baseExtension F).asPadicField (p := p)) fun _ => rfl)
  have hb : Module.finrank F.Carrier ((baseExtension F).asPadicField (p := p)).Carrier = 1 :=
    IntermediateField.finrank_bot
  rw [hL, hK, hb, one_mul]

/-- `f_K ord_K(N_{L/K} y) = f_L ord_L(y)` at the bottom field `K`. -/
theorem residueDegree_mul_ord_unitsNorm (L : Extension F)
    (hL : (baseExtension F).field ≤ L.field) (y : L.fieldˣ) :
    ((fieldData F (baseExtension F)).residueDegree : ℤ) *
        (fieldData F (baseExtension F)).ord
          ((baseExtension F).unitsNorm L hL y : (baseExtension F).field) =
      ((fieldData F L).residueDegree : ℤ) * (fieldData F L).ord (y : L.field) := by
  letI : Algebra (Padic p) (baseExtension F).field :=
    ((baseExtension F).asPadicField (p := p)).algebra
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra (baseExtension F).field L.field := (IntermediateField.inclusion hL).toAlgebra
  letI : IsScalarTower (Padic p) (baseExtension F).field L.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F.Carrier (baseExtension F).field L.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (baseExtension F).field L.field :=
    FiniteDimensional.right F.Carrier (baseExtension F).field L.field
  exact residueDegree_mul_ord_relative_norm ((baseExtension F).asPadicField (p := p))
    (L.asPadicField (p := p)) (fieldData F (baseExtension F)) (fieldData F L) (y : L.field)

/-- `e_K ord_L(c) = e_L ord_K(c)` for `c` in the bottom field `K`. -/
theorem ramificationIndex_mul_ord_unitsInclusion (L : Extension F)
    (hL : (baseExtension F).field ≤ L.field) (c : (baseExtension F).fieldˣ) :
    ((fieldData F (baseExtension F)).ramificationIndex : ℤ) *
        (fieldData F L).ord ((baseExtension F).unitsInclusion L hL c : L.field) =
      ((fieldData F L).ramificationIndex : ℤ) *
        (fieldData F (baseExtension F)).ord (c : (baseExtension F).field) := by
  letI : Algebra (Padic p) (baseExtension F).field :=
    ((baseExtension F).asPadicField (p := p)).algebra
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra (baseExtension F).field L.field := (IntermediateField.inclusion hL).toAlgebra
  letI : IsScalarTower (Padic p) (baseExtension F).field L.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F.Carrier (baseExtension F).field L.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (baseExtension F).field L.field :=
    FiniteDimensional.right F.Carrier (baseExtension F).field L.field
  exact ramificationIndex_mul_ord_relative_algebraMap ((baseExtension F).asPadicField (p := p))
    (L.asPadicField (p := p)) (fieldData F (baseExtension F)) (fieldData F L)
    (c : (baseExtension F).field)

/-- The bottom field has the ramification index of the base field. -/
theorem ramificationIndex_baseExtension_real :
    ((fieldData F (baseExtension F)).ramificationIndex : ℝ) =
      F.canonicalTopologicalData.ramificationIndex := by
  rw [fieldData_ramificationIndex_eq (baseExtension F)]
  have h1 : (baseExtension F).field.fixingSubgroup.relIndex
      (F.absoluteInertia F.canonicalTopologicalData) = 1 := by
    change (⊥ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)).fixingSubgroup.relIndex
      _ = 1
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.relIndex_eq_one.mpr le_top
  rw [h1, Nat.cast_one, one_mul]

/-! ## Characters of a given conductor -/

/-- For `M ≥ 1` there is a character of conductor exactly `M + 1`. -/
theorem exists_multiplicativeConductor_eq {G : PadicField.{uF} p} (T : G.TopologicalData)
    {M : ℕ} (hM : 0 < M) :
    ∃ χ : @HarmonicAnalysis.Quasicharacter G.Carrier _ T.topology,
      T.multiplicativeConductor χ = M + 1 := by
  let := T.topology
  have hϖ : T.uniformizer ^ M ∈ T.additiveLattice (-(M : ℤ)) := by
    change T.discreteValuation (T.uniformizer ^ M) ≤ WithZero.exp (-(M : ℤ))
    rw [map_pow, T.discreteValuation_uniformizer, ← WithZero.exp_nsmul]
    simp
  set u := RankOneStability.oneAddUnit T hM ⟨_, hϖ⟩ with hu_def
  have hu : u ∉ T.principalUnits (M + 1) := by
    intro h
    have h2 := h.2
    rw [hu_def, RankOneStability.oneAddUnit_val, add_sub_cancel_left, map_pow,
      T.discreteValuation_uniformizer, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at h2
    simp at h2
  rw [PadicAbelian.mem_principalUnits_iff_bounded_characters T] at hu
  push Not at hu
  obtain ⟨χ, hχ, hχu⟩ := hu
  refine ⟨χ, le_antisymm hχ ?_⟩
  by_contra hlt
  push Not at hlt
  exact hχu ((T.multiplicativeTrivialAt_iff_conductor_le χ M).mpr (by omega) u
    (RankOneStability.oneAddUnit_mem T hM _))

/-! ## The break and conductor of the inducing character -/

/-- A field character of `L` whose Weil character is nontrivial on `W_L^{B₀}` (`B₀ ≥ 0`) and
trivial on `W_L^s` for every `s > B₀` has an integer break `B₀ = B` and conductor `B + 1`,
given the unit-level theorem at `L`. -/
theorem conductor_eq_of_break {e : ReciprocityFamily F} (L : Extension F)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (χ : FieldCharacter F L) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hnt : ∃ g ∈ intermediateUpperGroup F L B₀, weilCharacter F e L χ g ≠ 1)
    (htriv : ∀ s : ℝ, B₀ < s → ∀ g ∈ intermediateUpperGroup F L s,
      weilCharacter F e L χ g = 1) :
    ∃ B : ℕ, B₀ = B ∧ (fieldData F L).multiplicativeConductor χ = B + 1 := by
  set T := fieldData F L
  have key : ∀ s : ℝ, 0 ≤ s → (T.MultiplicativeTrivialAt χ ⌈s⌉₊ ↔
      ∀ g ∈ intermediateUpperGroup F L s, weilCharacter F e L χ g = 1) := fun s hs =>
    trivial_iff_of_map_reciprocityUnits F L χ _ _ (hWL s hs)
  have hlow : ⌈B₀⌉₊ < T.multiplicativeConductor χ := by
    by_contra hle
    push Not at hle
    obtain ⟨g, hg, hne⟩ := hnt
    exact hne (((key B₀ hB₀).mp ((T.multiplicativeTrivialAt_iff_conductor_le χ _).mpr hle)) g hg)
  set B := ⌊B₀⌋₊ with hB
  have hlt : B₀ < (B : ℝ) + 1 := Nat.lt_floor_add_one _
  have hup : T.multiplicativeConductor χ ≤ B + 1 := by
    have h1 := (key ((B : ℝ) + 1) (by positivity)).mpr (htriv _ hlt)
    have h2 := (T.multiplicativeTrivialAt_iff_conductor_le χ _).mp h1
    have h3 : ⌈((B : ℝ) + 1)⌉₊ = B + 1 := by exact_mod_cast Nat.ceil_natCast (B + 1)
    rwa [h3] at h2
  have hfc : ⌈B₀⌉₊ ≤ B := by omega
  have hint : B₀ = B := by
    have h1 : B₀ ≤ ⌈B₀⌉₊ := Nat.le_ceil _
    have h2 : (B : ℝ) ≤ B₀ := Nat.floor_le hB₀
    have h3 : ((⌈B₀⌉₊ : ℕ) : ℝ) ≤ B := by exact_mod_cast hfc
    linarith
  refine ⟨B, hint, ?_⟩
  have h4 : ⌈B₀⌉₊ = B := by rw [hint, Nat.ceil_natCast]
  have h5 : B < T.multiplicativeConductor χ := h4 ▸ hlow
  exact le_antisymm hup h5

section Inducing

variable (L : Extension F) (hL : (baseExtension F).field ≤ L.field)
  (η : weilSubgroup F L →ₜ* ℂˣ)

/-- An inducing character trivial on the part of `W_L` above `α` is trivial on
`W_L^{s'}` for every `s' > ψ_{L/F}(α)`. -/
theorem eq_one_of_baseUpperAbove {α : ℝ} (hα : 0 ≤ α)
    (hK : ∀ g : weilSubgroup F L,
      weilInclusion F (baseExtension F) L hL g ∈ baseUpperAbove F α → η g = 1)
    {s' : ℝ} (hs' : relativeHerbrandPsi L α < s') (g : weilSubgroup F L)
    (hg : g ∈ intermediateUpperGroup F L s') : η g = 1 := by
  have hψα := relativeHerbrandPsi_nonneg L hα
  obtain ⟨s, hs0, rfl⟩ := exists_relativeHerbrandPsi_eq F L (hψα.trans hs'.le)
  have hαs : α < s := (relativeHerbrandPsi_strictMono L).lt_iff_lt.mp hs'
  apply hK
  have hmem : weilInclusion F (baseExtension F) L hL g ∈ baseUpperGroup F s := by
    rw [intermediateUpperGroup_eq_weilUpperSubgroup,
      ← coe_mem_upperGroup_iff F L (by linarith)] at hg
    exact hg
  exact (le_iSup₂ (f := fun (t : ℝ) (_ : α < t) => baseUpperGroup F t) s hαs) hmem

/-- An inducing character nontrivial on `W_F^α` is nontrivial on `W_L^{ψ_{L/F}(α)}`. -/
theorem exists_ne_one_of_baseUpperGroup {α : ℝ} (hα : 0 ≤ α)
    (hN : ∀ n ∈ baseUpperGroup F α, (n : localWeilGroup F) ∈ weilSubgroup F L)
    (hnt : ∃ n : baseUpperGroup F α,
      η ⟨((n : weilSubgroup F (baseExtension F)) : localWeilGroup F), hN n n.2⟩ ≠ 1) :
    ∃ g ∈ intermediateUpperGroup F L (relativeHerbrandPsi L α), η g ≠ 1 := by
  obtain ⟨n, hn⟩ := hnt
  refine ⟨_, ?_, hn⟩
  rw [intermediateUpperGroup_eq_weilUpperSubgroup, ← coe_mem_upperGroup_iff F L (by linarith)]
  exact n.2

/-- The field character of an inducing character `η` (nontrivial on `W_F^α`, trivial
above `α > 0`) has integer break `B = ψ_{L/F}(α) ≥ 1` and conductor `B + 1`. -/
theorem conductor_fieldCharacterEquiv {e : ReciprocityFamily F}
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    {α : ℝ} (hα : 0 < α)
    (hN : ∀ n ∈ baseUpperGroup F α, (n : localWeilGroup F) ∈ weilSubgroup F L)
    (hnt : ∃ n : baseUpperGroup F α,
      η ⟨((n : weilSubgroup F (baseExtension F)) : localWeilGroup F), hN n n.2⟩ ≠ 1)
    (hK : ∀ g : weilSubgroup F L,
      weilInclusion F (baseExtension F) L hL g ∈ baseUpperAbove F α → η g = 1) :
    ∃ B : ℕ, 1 ≤ B ∧ relativeHerbrandPsi L α = B ∧
      (fieldData F L).multiplicativeConductor
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) = B + 1 := by
  have hw := CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv F e L η
  obtain ⟨B, hB, hcond⟩ := conductor_eq_of_break F L hWL
    (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)
    (relativeHerbrandPsi_nonneg L hα.le)
    (by rw [hw]; exact exists_ne_one_of_baseUpperGroup F L η hα.le hN hnt)
    (fun s hs g hg => by rw [hw]; exact eq_one_of_baseUpperAbove F L hL η hα.le hK hs g hg)
  refine ⟨B, ?_, hB, hcond⟩
  have hpos : (0 : ℝ) < B := by
    rw [← hB, ← relativeHerbrandPsi_zero L]
    exact relativeHerbrandPsi_strictMono L hα
  exact_mod_cast hpos

end Inducing

/-! ## The valuation identity -/

/-- The valuation identity behind DH81 4.2.2 for an induction: if `W_F^α ⊆ W_L` with
`α ≥ 0`, then `e_K (ψ_{L/F}(α) + 1 + n(ψ ∘ Tr)) = e_L (α + 1 + n(ψ))`, where `K` is the
bottom field. It compares the linearizers of a character of `K` of large conductor and of
its norm pullback to `L`. -/
theorem ramificationIndex_mul_relativeHerbrandPsi_add_conductor {e : ReciprocityFamily F}
    (he : NormalizedReciprocity F e)
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (L : Extension F) (hL : (baseExtension F).field ≤ L.field)
    (hWL : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    {α : ℝ} (hα : 0 ≤ α) (hN : ∀ w ∈ upperGroup F α, w ∈ weilSubgroup F L)
    (ψ : AdditiveCharacter F (baseExtension F)) :
    ((fieldData F (baseExtension F)).ramificationIndex : ℝ) *
        (relativeHerbrandPsi L α + 1 +
          (fieldData F L).additiveConductor (traceCharacter F (baseExtension F) L hL ψ)) =
      (fieldData F L).ramificationIndex *
        (α + 1 + (fieldData F (baseExtension F)).additiveConductor ψ) := by
  set TK := fieldData F (baseExtension F) with hTK
  set TL := fieldData F L with hTL
  let := TK.topology
  let := TL.topology
  set ψL := traceCharacter F (baseExtension F) L hL ψ with hψL
  -- a large integer break `M > 2α`
  set M : ℕ := ⌈2 * α⌉₊ + 1 with hMdef
  have hM2α : 2 * α < M := by
    have := Nat.le_ceil (2 * α)
    rw [hMdef]
    push_cast
    linarith
  have hM0 : 0 < M := by omega
  -- a character of conductor `M + 1` and its linearizer
  obtain ⟨χ, hχcond⟩ := exists_multiplicativeConductor_eq TK hM0
  have h2 : 2 ≤ TK.multiplicativeConductor χ := by omega
  obtain ⟨c, hc, hlin⟩ := exists_linearization TK χ ψ h2
  rw [hχcond] at hc hlin
  have hχA : ∀ z ∈ TK.principalUnits (M + 1), χ z = 1 := by
    rw [← hχcond]
    exact TK.multiplicativeConductor_spec χ
  -- the norm pullback to `L`
  have hNL : ∀ w ∈ upperGroup F ((M : ℝ) / 2), w ∈ weilSubgroup F L := fun w hw =>
    hN w (upperGroup_antitone F (by linarith) hw)
  obtain ⟨B, hBψ, hBcond⟩ := conductor_restrictCharacter F L hL χ hχcond hWK hWL
    (relativeHerbrandPsi L) (relativeHerbrandPsi_continuous L)
    (relativeHerbrandPsi_strictMono L) (relativeHerbrandPsi_zero L)
    (fun v hv w => intermediateWeilEquiv_mem_upperGroup_iff L (by linarith) w) hNL
  -- the slope from `α` to `M`
  have hslope := ramificationIndex_mul_relativeHerbrandPsi_sub_of_upperGroup_le L hα
    (fun w hw => hN w hw) le_rfl (by linarith : α ≤ (M : ℝ))
  rw [← ramificationIndex_baseExtension_real F, hBψ] at hslope
  have hψα := relativeHerbrandPsi_nonneg L hα
  have heK : (0 : ℝ) < TK.ramificationIndex := by exact_mod_cast TK.ramificationIndex_pos
  have heL : (0 : ℝ) < TL.ramificationIndex := by exact_mod_cast TL.ramificationIndex_pos
  have hBR : (TL.ramificationIndex : ℝ) * (M - α) ≤ TK.ramificationIndex * B := by
    nlinarith
  have hB1 : 1 ≤ B := by
    have : (0 : ℝ) < B := by
      have h1 : (0 : ℝ) < TL.ramificationIndex * (M - α) := by
        apply mul_pos heL
        linarith
      have h2 := lt_of_lt_of_le h1 hBR
      exact pos_of_mul_pos_right h2 heK.le
    exact_mod_cast this
  -- the depth conditions at `t = B`
  set m := M + 1 - (M + 1) / 2 with hmdef
  have hm : 0 < m := by omega
  have hR : (((M + 1 : ℕ) : ℤ) - 1) * TL.ramificationIndex <
      2 * TK.ramificationIndex * B := by
    have hR' : ((M : ℝ)) * TL.ramificationIndex < 2 * TK.ramificationIndex * B := by
      nlinarith
    have : (((M + 1 : ℕ) : ℤ) - 1) = (M : ℤ) := by push_cast; ring
    rw [this]
    exact_mod_cast hR'
  have hT : ((m : ℤ) - 1) * TL.ramificationIndex < TK.ramificationIndex * B := by
    have h2m : 2 * ((m : ℤ) - 1) ≤ M := by omega
    have heLz : (0 : ℤ) < TL.ramificationIndex := by exact_mod_cast TL.ramificationIndex_pos
    have hR2 : (M : ℤ) * TL.ramificationIndex < 2 * TK.ramificationIndex * B := by
      have := hR
      push_cast at this
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h2m heLz.le]
  -- the linearizer of the pullback
  set χL := restrictCharacter F e (baseExtension F) L hL χ with hχL
  set aL := TL.multiplicativeConductor χL with haLdef
  have haL : aL = B + 1 := hBcond
  have hmL : 0 < aL - aL / 2 := by omega
  obtain ⟨c', hc'0, hc'ord, hlin'⟩ := RankOneStability.exists_deep_linearization TL χL ψL
    hmL (by omega) (by omega)
  let d : L.fieldˣ := Units.mk0 c' hc'0
  have hd : TL.ord (d : L.field) = -(TL.additiveConductor ψL + aL) := by
    change TL.ord c' = _
    rw [hc'ord]
    ring
  set cL := (baseExtension F).unitsInclusion L hL c with hcL
  have h_eq : ∀ x ∈ TL.additiveLattice (-(B : ℤ)),
      ψL.complex ((cL : L.field) * x) = ψL.complex ((d : L.field) * x) := by
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
    have hord' : (B : ℤ) ≤ (fieldData F L).ord x := hord
    have heKz : (0 : ℤ) ≤ TK.ramificationIndex := by positivity
    have h1 := restrictCharacter_one_add F he (baseExtension F) L hL χ ψ c hm (by omega) hlin hχA x hx0
      (by omega) (by nlinarith) (by nlinarith) u rfl
    have hxm : x ∈ TL.additiveLattice (-((aL - aL / 2 : ℕ) : ℤ)) :=
      TL.additiveLattice_mono (by omega) hx
    have h2 := hlin' ⟨x, hxm⟩
    have hu : RankOneStability.oneAddUnit TL hmL ⟨x, hxm⟩ = u := Units.ext rfl
    rw [hu] at h2
    exact h1.symm.trans h2
  have hcd := mul_inv_mem_principalUnits_of_eq_on_lattice TL ψL (by omega : B < aL) hd h_eq
  -- equal orders
  have hordcd : TL.ord (cL : L.field) = TL.ord (d : L.field) := by
    have h1 : TL.ord ((cL * d⁻¹ : L.fieldˣ) : L.field) = 0 := by
      have hv := hcd.1
      simp only [PadicField.TopologicalData.ord, hv, WithZero.log_one, neg_zero]
    rw [Units.val_mul, TL.ord_mul cL.ne_zero (d⁻¹).ne_zero, Units.val_inv_eq_inv_val,
      TL.ord_inv] at h1
    linarith
  have hrel := ramificationIndex_mul_ord_unitsInclusion F L hL c
  rw [← hcL, hordcd, hd, hc, haL] at hrel
  have hrelR : ((TK.ramificationIndex : ℤ) : ℝ) *
      ((-(TL.additiveConductor ψL + ((B + 1 : ℕ) : ℤ)) : ℤ) : ℝ) =
      ((TL.ramificationIndex : ℤ) : ℝ) *
        ((-(((M + 1 : ℕ) : ℤ) + TK.additiveConductor ψ) : ℤ) : ℝ) := by
    exact_mod_cast hrel
  push_cast at hrelR hslope
  linear_combination -hrelR - hslope

/-! ## Witnesses at a label -/

/-- A witness at the label `α` for `x ∈ R(W_F)` (the form of the witnesses built in DH81 4.5
and 4.8): a unit `γ` of the bottom field `K` with `ord_K γ = deg x · (α + 1 + n(ψ))` that is
an exact witness for `x` relative to `W_F^{α/2}` and an approximate witness for `x` relative
to `W_F^α`. -/
def IsLabelWitness (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (ψ : AdditiveCharacter F (baseExtension F)) (α : ℝ)
    (x : Virtual.{uF, uV} F (baseExtension F)) (γ : (baseExtension F).fieldˣ) : Prop :=
  ((fieldData F (baseExtension F)).ord (γ : (baseExtension F).field) : ℝ) =
      CommonClosure.degree F (baseExtension F) x *
        (α + 1 + (fieldData F (baseExtension F)).additiveConductor ψ) ∧
    ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F (α / 2)) ψ x γ ∧
    ApproximateWitnessOn F e ε (baseExtension F) (baseUpperGroup F α) ψ x γ

section LabelWitness

variable {F} {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
  {ψ : AdditiveCharacter F (baseExtension F)} {α : ℝ}

theorem isLabelWitness_zero (hε : AdditiveRelation F ε) :
    IsLabelWitness F e ε ψ α 0 1 := by
  refine ⟨?_, exactWitnessOn_zero hε, approximateWitnessOn_zero hε⟩
  rw [Units.val_one, (fieldData F (baseExtension F)).ord_one, map_zero]
  simp

theorem IsLabelWitness.add (hε : AdditiveRelation F ε)
    {x y : Virtual.{uF, uV} F (baseExtension F)} {γ γ' : (baseExtension F).fieldˣ}
    (hx : IsLabelWitness F e ε ψ α x γ) (hy : IsLabelWitness F e ε ψ α y γ') :
    IsLabelWitness F e ε ψ α (x + y) (γ * γ') := by
  obtain ⟨hγ, hxe, hxa⟩ := hx
  obtain ⟨hγ', hye, hya⟩ := hy
  refine ⟨?_, exactWitnessOn_add hε hxe hye, approximateWitnessOn_add hε hxa hya⟩
  rw [Units.val_mul, (fieldData F (baseExtension F)).ord_mul γ.ne_zero γ'.ne_zero, map_add]
  push_cast
  rw [hγ, hγ']
  ring

theorem IsLabelWitness.zsmul (hε : AdditiveRelation F ε) (n : ℤ)
    {x : Virtual.{uF, uV} F (baseExtension F)} {γ : (baseExtension F).fieldˣ}
    (hx : IsLabelWitness F e ε ψ α x γ) :
    IsLabelWitness F e ε ψ α (n • x) (γ ^ n) := by
  obtain ⟨hγ, hxe, hxa⟩ := hx
  refine ⟨?_, exactWitnessOn_zsmul hε n hxe, approximateWitnessOn_zsmul hε n hxa⟩
  rw [Units.val_zpow_eq_zpow_val, (fieldData F (baseExtension F)).ord_zpow, map_zsmul,
    smul_eq_mul]
  push_cast
  rw [hγ]
  ring

end LabelWitness

/-! ## The witness of one generator -/

/-- DH81 4.5, 4.7 and 4.8 for one generator `Ind_{W_L}^{W_F} [η]` of the kernel span at a
label `α > 0`: for a linearizer `c` of the field character of `η`, the norm
`γ = N_{L/K}(c⁻¹)` to the bottom field `K` is a witness at the label `α`, that is, an
exact witness relative to `W_F^{α/2}` and an approximate witness relative to `W_F^α` with
`ord_K γ = [L : F] (α + 1 + n(ψ))`. The unit-level theorems at the bottom field and at every
`L`, and the first-order norm–trace congruence, are hypotheses. -/
theorem exists_witness_kernelGenerator {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε)
    (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
    (hWL : ∀ (L : Extension F) (s : ℝ), 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊)
    (htop : TopLayerNormTraceStatement.{uF, uF, uF})
    (ψ : AdditiveCharacter F (baseExtension F)) {α : ℝ} (hα : 0 < α)
    {x : Virtual.{uF, uV} F (baseExtension F)}
    (hx : x ∈ kernelInductionGenerators.{uF, uV} F (baseExtension F) (baseUpperGroup F α)
      (baseUpperAbove F α)) :
    ∃ γ : (baseExtension F).fieldˣ, IsLabelWitness F e ε ψ α x γ := by
  unfold IsLabelWitness
  obtain ⟨L, hL, η, hN, hnt, hK, rfl⟩ := hx
  have hinert : AbsoluteUpperInertia (L.asPadicField (p := p))
      (L.asPadicField (p := p)).canonicalTopologicalData :=
    absoluteUpperInertia (L.asPadicField (p := p)) _
  obtain ⟨B, hB1, hBψ, hcond⟩ := conductor_fieldCharacterEquiv F L hL η (hWL L) hα hN hnt hK
  have h2 : 2 ≤ (fieldData F L).multiplicativeConductor
      (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) := by
    rw [hcond]
    omega
  obtain ⟨c, hc, hlin⟩ := exists_linearization (fieldData F L)
    (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η)
    (traceCharacter F (baseExtension F) L hL ψ) h2
  rw [hcond] at hc hlin
  have hclass : characterClass F e L (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) =
      VirtualRepresentation.ExactGrothendieckGroup.characterClass η := by
    rw [characterClass, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
  -- the exact witness over `L`, then induced
  have hexL := exactWitnessOn_characterClass_of_linearization_rel F hsys L hinert
    (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) hB1 hcond
    (traceCharacter F (baseExtension F) L hL ψ) c hlin (hWL L)
    (fun L' h' hW => ⟨hWL L', herbrandInputRel_of_le F L L' h' hW⟩)
  rw [hclass, intermediateUpperGroup_eq_weilUpperSubgroup, ← hBψ] at hexL
  have hex := exactWitnessOn_induce_upper hsys L hL hα.le ψ _ c⁻¹ hexL
  -- the approximate witness over `L`, then induced
  have happL := approximateWitnessOn_characterClass_of_linearization_rel F hsys L hinert
    (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L η) hB1 hcond
    (traceCharacter F (baseExtension F) L hL ψ) c hlin (hWL L)
    (fun L' h' hW => ⟨hWL L', approximateHerbrandInput_of_le F L L' h' htop hB1 hW⟩)
  rw [hclass, intermediateUpperGroup_eq_weilUpperSubgroup, ← hBψ] at happL
  have happ := approximateWitnessOn_induce_upper hsys L hL (by linarith) ψ _ c⁻¹ happL
  refine ⟨(baseExtension F).unitsNorm L hL c⁻¹, ?_, hex, happ⟩
  -- the valuation
  have hNα : ∀ w ∈ upperGroup F α, w ∈ weilSubgroup F L := fun w hw =>
    hN ⟨w, mem_baseWeil F w⟩ hw
  have h1 := residueDegree_mul_ord_unitsNorm F L hL c⁻¹
  have hordc : (fieldData F L).ord ((c⁻¹ : L.fieldˣ) : L.field) =
      ((B + 1 : ℕ) : ℤ) + (fieldData F L).additiveConductor
        (traceCharacter F (baseExtension F) L hL ψ) := by
    rw [Units.val_inv_eq_inv_val, (fieldData F L).ord_inv, hc]
    ring
  rw [hordc] at h1
  have h1' : (((fieldData F (baseExtension F)).residueDegree : ℤ) : ℝ) *
        (((fieldData F (baseExtension F)).ord
          ((baseExtension F).unitsNorm L hL c⁻¹ : (baseExtension F).field) : ℤ) : ℝ) =
      (((fieldData F L).residueDegree : ℤ) : ℝ) *
        ((((B + 1 : ℕ) : ℤ) + (fieldData F L).additiveConductor
          (traceCharacter F (baseExtension F) L hL ψ) : ℤ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h1'
  have h2 := ramificationIndex_mul_relativeHerbrandPsi_add_conductor F hsys.1 hWK L hL (hWL L)
    hα.le hNα ψ
  rw [hBψ] at h2
  have h3 : ((fieldData F L).ramificationIndex : ℝ) * (fieldData F L).residueDegree =
      (Module.finrank F.Carrier L.field : ℝ) *
        ((fieldData F (baseExtension F)).ramificationIndex *
          (fieldData F (baseExtension F)).residueDegree) := by
    exact_mod_cast ramificationIndex_mul_residueDegree_eq F L
  have heK : ((fieldData F (baseExtension F)).ramificationIndex : ℝ) *
      (fieldData F (baseExtension F)).residueDegree ≠ 0 := by
    have h1 := (fieldData F (baseExtension F)).ramificationIndex_pos
    have h2 := (fieldData F (baseExtension F)).residueDegree_pos
    positivity
  rw [← hclass, degree_induce_base, CommonClosure.degree_characterClass]
  push_cast
  apply mul_left_cancel₀ heK
  linear_combination ((fieldData F (baseExtension F)).ramificationIndex : ℝ) * h1' +
    ((fieldData F L).residueDegree : ℝ) * h2 +
    (α + 1 + ((fieldData F (baseExtension F)).additiveConductor ψ : ℝ)) * h3

/-! ## Assembly -/

section Assembly

open VirtualRepresentation

/-- The lattice degree of a basis class is its rank. -/
theorem degree_generator (b : LocalWeil.Basis.{uF, max uF uV} F) :
    LocalWeil.degree F (generator b) = ((b.1 : ℕ) : ℤ) := by
  rw [LocalWeil.degree, VirtualRepresentation.Weil.degree, rankedDegree,
    VirtualRepresentation.degree, extend, generator, Finsupp.linearCombination_single, one_smul]

variable {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
  (hsys : IsSystem F e ε)
  (hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
    (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
      (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊)
  (hWL : ∀ (L : Extension F) (s : ℝ), 0 ≤ s → letI := (fieldData F L).topology;
    (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
      (fieldData F L).principalUnits ⌈s⌉₊)
  (htop : TopLayerNormTraceStatement.{uF, uF, uF})
  (ψ : AdditiveCharacter F (baseExtension F))

include hsys hWK hWL htop

/-- DH81 4.5 and 4.8 on the kernel span at a label `α > 0`: every element of the span has a
witness at the label `α`. -/
theorem exists_isLabelWitness_kernelSpan {α : ℝ} (hα : 0 < α)
    {x : Virtual.{uF, uV} F (baseExtension F)}
    (hx : x ∈ Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F (baseExtension F)
      (baseUpperGroup F α) (baseUpperAbove F α))) :
    ∃ γ : (baseExtension F).fieldˣ, IsLabelWitness F e ε ψ α x γ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact exists_witness_kernelGenerator F hsys hWK hWL htop ψ hα hx
  | zero => exact ⟨1, isLabelWitness_zero hsys.2.1⟩
  | add x y _ _ hx hy =>
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨γ', hγ'⟩ := hy
    exact ⟨γ * γ', hγ.add hsys.2.1 hγ'⟩
  | smul n x _ hx =>
    obtain ⟨γ, hγ⟩ := hx
    exact ⟨γ ^ n, hγ.zsmul hsys.2.1 n⟩

/-- DH81 4.5 and 4.8 for one basis class of positive label `α ≥ a`: one witness, exact
relative to `W_F^{a/2}` and approximate relative to `W_F^a`, of valuation
`rank · (α + 1 + n(ψ))`. -/
theorem exists_witness_generator (b : LocalWeil.Basis.{uF, max uF uV} F)
    (hb : 0 < breakLabel F b) {a : ℝ} (ha : a ≤ breakLabel F b) :
    ∃ γ : (baseExtension F).fieldˣ,
      ((fieldData F (baseExtension F)).ord (γ : (baseExtension F).field) : ℝ) =
        ((b.1 : ℕ) : ℝ) *
          (breakLabel F b + 1 + (fieldData F (baseExtension F)).additiveConductor ψ) ∧
      ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F (a / 2)) ψ
        (realizeAtBase F (generator b)) γ ∧
      ApproximateWitnessOn F e ε (baseExtension F) (baseUpperGroup F a) ψ
        (realizeAtBase F (generator b)) γ := by
  obtain ⟨γ, hγ, hex, happ⟩ := exists_isLabelWitness_kernelSpan F hsys hWK hWL htop ψ hb
    (realizeAtBase_generator_mem_kernelSpan F b hb)
  refine ⟨γ, ?_, exactWitnessOn_mono (baseUpperGroup_antitone F (by linarith)) hex,
    approximateWitnessOn_mono (baseUpperGroup_antitone F ha) happ⟩
  rw [hγ, degree_realizeAtBase, degree_generator]
  push_cast
  ring

/-- The witness of a lattice element with positive constituent labels, all at least `a`:
exact relative to `W_F^{a/2}`, approximate relative to `W_F^a`, of valuation
`wildArtinSum F v + deg v · n(ψ)` (DH81 4.2.2). -/
theorem exists_witness_lattice (v : LocalWeil.Lattice.{uF, max uF uV} F)
    (hpos : PositiveBreakSupport F v) {a : ℝ} (ha : AllBreaksAtLeast F v a) :
    ∃ γ : (baseExtension F).fieldˣ,
      ((fieldData F (baseExtension F)).ord (γ : (baseExtension F).field) : ℝ) =
        wildArtinSum F v + (LocalWeil.degree F v : ℝ) *
          (fieldData F (baseExtension F)).additiveConductor ψ ∧
      ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F (a / 2)) ψ
        (realizeAtBase F v) γ ∧
      ApproximateWitnessOn F e ε (baseExtension F) (baseUpperGroup F a) ψ
        (realizeAtBase F v) γ := by
  set T := fieldData F (baseExtension F)
  induction v using Finsupp.induction with
  | zero =>
    refine ⟨1, ?_, ?_, ?_⟩
    · rw [Units.val_one, T.ord_one, map_zero]
      simp [wildArtinSum]
    · rw [map_zero]
      exact exactWitnessOn_zero hsys.2.1
    · rw [map_zero]
      exact approximateWitnessOn_zero hsys.2.1
  | single_add b n f hb hn ih =>
    have hfb : f b = 0 := Finsupp.notMem_support_iff.mp hb
    have hbv : (Finsupp.single b n + f) b ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfb, add_zero]
      exact hn
    have hsub : ∀ c, f c ≠ 0 → (Finsupp.single b n + f) c ≠ 0 := by
      intro c hc
      have hcb : c ≠ b := fun h => hc (h ▸ hfb)
      rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hcb, zero_add]
    obtain ⟨γ', hγ', hfe, hfa⟩ := ih (fun c hc => hpos c (hsub c hc))
      (fun c hc => ha c (hsub c hc))
    obtain ⟨γ, hγ, hbe, hba⟩ := exists_witness_generator F hsys hWK hWL htop ψ b
      (hpos b hbv) (ha b hbv)
    have hsingle : Finsupp.single b n = n • generator b := by
      simp [generator]
    refine ⟨γ ^ n * γ', ?_, ?_, ?_⟩
    · rw [Units.val_mul, T.ord_mul (γ ^ n).ne_zero γ'.ne_zero, Units.val_zpow_eq_zpow_val,
        T.ord_zpow]
      have hw : wildArtinSum F (Finsupp.single b n + f) =
          (n : ℝ) * (b.1 : ℕ) * (1 + breakLabel F b) + wildArtinSum F f := by
        unfold wildArtinSum
        rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
          Finsupp.sum_single_index (by simp)]
      rw [hw, map_add, hsingle, map_zsmul, degree_generator, smul_eq_mul]
      push_cast
      rw [hγ, hγ']
      ring
    · rw [hsingle, map_add, map_zsmul]
      exact exactWitnessOn_add hsys.2.1 (exactWitnessOn_zsmul hsys.2.1 n hbe) hfe
    · rw [hsingle, map_add, map_zsmul]
      exact approximateWitnessOn_add hsys.2.1 (approximateWitnessOn_zsmul hsys.2.1 n hba) hfa

end Assembly

/-- DH81 4.6 with 4.2.2 and the compatibility with 4.2: `VirtualStabilityStatement`, given
the real unit images of absolute reciprocity, the geometricity of normalized
common-closure families at the base field and at every intermediate field, and the
first-order norm–trace congruence DH81 3.12(i). -/
theorem virtualStability_of_inputs
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hgeo : CommonClosureGeometricStatement.{uF, uF})
    (hint : IntermediateGeometricStatement.{uF})
    (htop : TopLayerNormTraceStatement.{uF, uF, uF}) :
    VirtualStabilityStatement.{uF, uV} := by
  intro p _ F e ε hsys ψ v hv hpos a
  have hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F :=
    weilTrivialityThresholdsNonempty F
  have hinert : AbsoluteUpperInertia F F.canonicalTopologicalData :=
    absoluteUpperInertia F _
  have hcmp : UnitFiltrationComparison.{uF} := LocalClassField.unitFiltrationComparison
  have hWK : ∀ s : ℝ, 0 ≤ s → letI := (fieldData F (baseExtension F)).topology;
      (baseUpperGroup F s).map (reciprocityUnits F e (baseExtension F)).toMonoidHom =
        (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊ := fun s hs =>
    baseUpperGroup_map_reciprocityUnits F hreal hinert hcmp e
      (geometric_baseReciprocityCandidate F hgeo e hsys.1) hs
  have hWL : ∀ (L : Extension F) (s : ℝ), 0 ≤ s → letI := (fieldData F L).topology;
      (intermediateUpperGroup F L s).map (reciprocityUnits F e L).toMonoidHom =
        (fieldData F L).principalUnits ⌈s⌉₊ := fun L s hs =>
    intermediateUpperGroup_map_reciprocityUnits F hreal hcmp e L
      (absoluteUpperInertia _ _) (hint p F e hsys.1 L) hs
  have ha : AllBreaksAtLeast F v a := (allBreaksAtLeast_iff_le_minimumBreak F v hv a).mpr le_rfl
  obtain ⟨γ, hord, hex, happ⟩ := exists_witness_lattice F hsys hWK hWL htop ψ v hpos ha
  have hexW : ExactWitness F e ε v a ψ γ := exactWitness_of_exactWitnessOn F hthr hex
  have happW : ApproximateWitness F e ε v a ψ γ :=
    approximateWitness_of_approximateWitnessOn F hthr happ
  refine ⟨γ, hord, hexW,
    exactWitness_iff_mem_coset_of_isSystem F hthr hreal hinert hcmp hgeo hsys hv hpos hexW,
    γ, happW, ?_,
    approximateWitness_iff_mem_coset_of_isSystem F hthr hreal hinert hcmp hgeo hsys hv hpos
      happW⟩
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
