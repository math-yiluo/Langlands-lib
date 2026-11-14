import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnfolding
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
/-!
# Matrix integrals of a Whittaker model as rank-one integrals

For `σ` smooth on `GL_(m+2)`, a standard functional `ℓ`, a matrix test function `Φ` and
a model function `W`, there is one model function `W'` such that for every `s` with
absolutely convergent shifted matrix integral `Z(Φ, s + (m+1)/2, W)`, the rank-one
integral `Ψ(s, W')` converges absolutely and the two agree. Hence the shifted
matrix values of the model lie in `rankOneModelValues`.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_anti congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint diagPoint_mul diagonalUnits_mem_congruenceGroup elemUnipotent elemUnipotent_val exists_compact_hFamily exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_model_congruence exists_model_hFamily exists_ne_zero_of_unipotentTransform_ne_zero exists_rankOneModel_of_matrix exists_schwartz_congruence glLocallyCompact glLocallyCompactU glModelFunction_sum glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableE glSecondCountableU hFamily hFamily_finite hFamily_mul_right hProduct hProduct_mul_right instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instBorelSpaceUnitsCarrier_2 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instIsNonarchimedeanLocalFieldCarrier_5 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instMeasurableSpaceUnitsCarrier_2 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyCarrier_2 instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instTopologicalSpaceCarrier_5 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 instValuativeRelCarrier_5 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_integralSet isCompact_lattice isCompact_unitBox isOpen_congruenceGroup isOpen_lattice isOpen_matLattice isOpen_outerCongruence isOpen_unitsCongruence iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactE matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero one_mem_outerCongruence outerCongruence outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusCoord_one_mem torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsCongruence unitsSecondCountable unitsSecondCountableE weight weight_apply weight_glOne weight_smul_determinantWeight weight_split whittakerRationalValues_subset_rankOneModelValues
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneMatrixWhittakerComparisonStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneMatrixWhittakerComparison_zero singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.Conductor

universe uF uV

section Expansion

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance (k : ℕ) : MeasurableSpace (Langlands.GeneralLinear (k + 1) F) := borel _
local instance (k : ℕ) : BorelSpace (Langlands.GeneralLinear (k + 1) F) := ⟨rfl⟩
local instance : MeasurableSpace Fˣ := borel _
local instance : BorelSpace Fˣ := ⟨rfl⟩

local instance glSecondCountableE (k : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear k F) := by
  have : SecondCountableTopology (Matrix (Fin k) (Fin k) F) :=
    inferInstanceAs (SecondCountableTopology (Fin k → Fin k → F))
  have : SecondCountableTopology (Matrix (Fin k) (Fin k) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance unitsSecondCountableE : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local instance matrixLocallyCompactE (k : ℕ) :
    LocallyCompactSpace (Matrix (Fin k) (Fin k) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin k → Fin k → F))

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))

/-! ### Principal units -/

/-- The principal units of level `M`: `x - 1` and `x⁻¹ - 1` lie in `πᴹ O`. -/
def unitsCongruence (M : ℕ) : Subgroup Fˣ where
  carrier := {x | (x : F) - 1 ∈ 𝓛 (-(M : ℤ)) ∧ ((x⁻¹ : Fˣ) : F) - 1 ∈ 𝓛 (-(M : ℤ))}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have key : ∀ x y : F, x - 1 ∈ 𝓛 (-(M : ℤ)) → y - 1 ∈ 𝓛 (-(M : ℤ)) →
        x * y - 1 ∈ 𝓛 (-(M : ℤ)) := by
      intro x y hx hy
      have h : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
      rw [h]
      refine add_mem (add_mem ?_ hx) hy
      exact lattice_mono F (by omega) (lattice_mul F hx hy)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact key _ _ ha.1 hb.1
    · rw [mul_inv_rev, Units.val_mul]
      exact key _ _ hb.2 ha.2
  inv_mem' {a} ha := ⟨ha.2, by simpa using ha.1⟩

theorem isOpen_unitsCongruence (M : ℕ) : IsOpen (unitsCongruence F M : Set Fˣ) := by
  have hS : IsOpen {x : F | x - 1 ∈ 𝓛 (-(M : ℤ))} :=
    (isOpen_lattice F _).preimage (continuous_id.sub continuous_const)
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

/-- A diagonal matrix of principal units lies in the congruence subgroup. -/
theorem diagonalUnits_mem_congruenceGroup {n M : ℕ} (t : Fin (n + 1) → Fˣ)
    (ht : ∀ i, t i ∈ unitsCongruence F M) :
    Iwasawa.diagonalUnits t ∈ congruenceGroup F n M := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Iwasawa.diagonalUnits_val, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact (ht i).1
    · simp
  · rw [← map_inv, Iwasawa.diagonalUnits_val, Matrix.sub_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
    split_ifs with h
    · subst h
      exact (ht i).2
    · simp

/-- The torus coordinate of a principal-unit tail is a principal-unit vector. -/
theorem torusCoord_one_mem {n M : ℕ} (ε : Fin n → Fˣ)
    (hε : ∀ i, ε i ∈ unitsCongruence F M) (i : Fin (n + 1)) :
    torusCoord n ((1 : Langlands.GeneralLinear (0 + 1) F), ε) i ∈ unitsCongruence F M := by
  induction i using Fin.cases with
  | zero =>
    rw [torusCoord_zero, map_one, one_mul]
    exact inv_mem (Subgroup.prod_mem _ fun i _ => hε i)
  | succ i => exact hε i

/-! ### The integrand family -/

variable (ψ : UnitaryAdditiveCharacter F) {m : ℕ} {V : Type uV} [AddCommGroup V]
  [Module ℂ V] (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)

/-- A model function of a smooth representation is right invariant under a congruence
subgroup. -/
theorem exists_model_congruence (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) :
    ∃ M : ℕ, ∀ κ ∈ congruenceGroup F (m + 1) M, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * κ) = glModelFunction ψ (m + 1) σ ℓ w g := by
  obtain ⟨H, hH⟩ := model_isSmooth σ hσ ℓ w
  obtain ⟨M, hM⟩ := exists_congruenceGroup_le F H.toSubgroup H.isOpen
  refine ⟨M, fun κ hκ g => ?_⟩
  rw [← glModelFunction_translate]
  congr 1
  exact (Representation.mem_invariants _ _).1 hH ⟨κ, hM hκ⟩

/-- The product `J(y) W(y)` of the unipotent transform and the model function. -/
def hProduct (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F))
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (y : Langlands.GeneralLinear (m + 1 + 1) F) : ℂ :=
  unipotentTransform F ψ Φ y.val * glModelFunction ψ (m + 1) σ ℓ w y

/-- The family `(a, k) ↦ (g ↦ J(D(g,a) k) W(D(g,a) k))`, cut off to integral `k`. -/
def hFamily (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F))
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (y : (Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F)
    (g : Langlands.GeneralLinear (0 + 1) F) : ℂ := by
  classical
  exact if y.2 ∈ integralSet F (m + 1) then hProduct F ψ σ Φ ℓ w (diagPoint F (g, y)) else 0

theorem diagPoint_mul (g : Langlands.GeneralLinear (0 + 1) F)
    (y u : (Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F) :
    diagPoint F (g, y * u) = diagPoint F (g, y) *
      (y.2⁻¹ * Iwasawa.diagonalUnits (torusCoord (m + 1) (1, u.1)) * y.2 * u.2) := by
  have ht : torusCoord (m + 1) (g, y.1 * u.1) =
      torusCoord (m + 1) (g, y.1) * torusCoord (m + 1) (1, u.1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [diagPoint, Prod.fst_mul, Prod.snd_mul, ht, map_mul]
  group

theorem hProduct_mul_right
    {Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F)}
    {ℓ : glFunctionals ψ (m + 1) σ} {w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule} {M : ℕ}
    (hΦ : ∀ κ ∈ congruenceGroup F (m + 1) M, ∀ X, Φ (X * κ.val) = Φ X)
    (hW : ∀ κ ∈ congruenceGroup F (m + 1) M, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * κ) = glModelFunction ψ (m + 1) σ ℓ w g)
    {κ : Langlands.GeneralLinear (m + 1 + 1) F} (hκ : κ ∈ congruenceGroup F (m + 1) M)
    (y : Langlands.GeneralLinear (m + 1 + 1) F) :
    hProduct F ψ σ Φ ℓ w (y * κ) = hProduct F ψ σ Φ ℓ w y := by
  unfold hProduct
  rw [Units.val_mul, unipotentTransform_mul_right F ψ Φ κ.val (hΦ κ hκ), hW κ hκ]

/-- The open subgroup `(U_M)ⁿ × K_M` of the outer parameters. -/
def outerCongruence (M : ℕ) :
    Set ((Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F) :=
  (Set.univ.pi fun _ => (unitsCongruence F M : Set Fˣ)) ×ˢ
    (congruenceGroup F (m + 1) M : Set (Langlands.GeneralLinear (m + 1 + 1) F))

theorem isOpen_outerCongruence (M : ℕ) : IsOpen (outerCongruence F (m := m) M) :=
  (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_unitsCongruence F M).prod
    (isOpen_congruenceGroup F (m + 1) M)

theorem one_mem_outerCongruence (M : ℕ) : (1 : (Fin (m + 1) → Fˣ) ×
    Langlands.GeneralLinear (m + 1 + 1) F) ∈ outerCongruence F M :=
  ⟨fun _ _ => (unitsCongruence F M).one_mem, (congruenceGroup F (m + 1) M).one_mem⟩

theorem hFamily_mul_right
    {Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F)}
    {ℓ : glFunctionals ψ (m + 1) σ} {w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule} {M : ℕ}
    (hΦ : ∀ κ ∈ congruenceGroup F (m + 1) M, ∀ X, Φ (X * κ.val) = Φ X)
    (hW : ∀ κ ∈ congruenceGroup F (m + 1) M, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * κ) = glModelFunction ψ (m + 1) σ ℓ w g)
    (y u : (Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F)
    (hu : u ∈ outerCongruence F M) :
    hFamily F ψ σ Φ ℓ w (y * u) = hFamily F ψ σ Φ ℓ w y := by
  funext g
  have hu2 : u.2 ∈ integralSet F (m + 1) := congruenceGroup_le_integral F (m + 1) M hu.2
  unfold hFamily
  by_cases hk : y.2 ∈ integralSet F (m + 1)
  · have hk' : (y * u).2 ∈ integralSet F (m + 1) := by
      rw [Prod.snd_mul]
      exact mul_mem hk hu2
    rw [ite_eq_left hk', ite_eq_left hk, diagPoint_mul]
    have hδ := diagonalUnits_mem_congruenceGroup F _
      (torusCoord_one_mem F u.1 fun i => hu.1 i (Set.mem_univ i))
    have hκ : y.2⁻¹ * Iwasawa.diagonalUnits (torusCoord (m + 1) (1, u.1)) * y.2 * u.2 ∈
        congruenceGroup F (m + 1) M :=
      mul_mem (conj_mem_congruenceGroup F hk hδ) hu.2
    exact hProduct_mul_right F ψ σ hΦ hW hκ _
  · have hk' : (y * u).2 ∉ integralSet F (m + 1) := by
      intro h
      apply hk
      have : y.2 = (y * u).2 * u.2⁻¹ := by rw [Prod.snd_mul, mul_inv_cancel_right]
      rw [this]
      exact mul_mem h (inv_mem hu2)
    rw [ite_eq_right hk', ite_eq_right hk]

theorem isCompact_integralSet (n : ℕ) : IsCompact (integralSet F n) := by
  unfold integralSet
  rw [← levelSubgroup_zero]
  exact isCompact_levelOpenSubgroup F n 0

theorem isCompact_unitBox (R E : ℤ) :
    IsCompact {x : Fˣ | (x : F) ∈ 𝓛 R ∧ ((x⁻¹ : Fˣ) : F) ∈ 𝓛 E} := by
  have hK : IsCompact ((𝓛 R : Set F) ×ˢ
      (MulOpposite.opHomeomorph.symm ⁻¹' (𝓛 E : Set F))) :=
    (isCompact_lattice F R).prod
      ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (isCompact_lattice F E))
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage hK
  convert this using 1
  ext x
  exact Iff.rfl

/-- The family vanishes outside a compact set of outer parameters. -/
theorem exists_compact_hFamily
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F))
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) :
    ∃ C : Set ((Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F),
      IsCompact C ∧ ∀ y ∉ C, hFamily F ψ σ Φ ℓ w y = 0 := by
  obtain ⟨R, E, hRE⟩ := unipotentTransform_diag_bounds F ψ (n := m + 1) Φ
  refine ⟨(Set.univ.pi fun _ => {x : Fˣ | (x : F) ∈ 𝓛 R ∧
      ((x⁻¹ : Fˣ) : F) ∈ 𝓛 E}) ×ˢ integralSet F (m + 1),
    (isCompact_univ_pi fun _ => isCompact_unitBox F R E).prod (isCompact_integralSet F _), ?_⟩
  intro y hy
  funext g
  unfold hFamily
  split_ifs with hk
  · by_contra hne
    apply hy
    have hJ : unipotentTransform F ψ Φ (diagPoint F (g, y)).val ≠ 0 := by
      intro h0
      apply hne
      unfold hProduct
      rw [h0, zero_mul]
      rfl
    have hval : (diagPoint F (g, y)).val = Matrix.diagonal (fun j =>
        (torusCoord (m + 1) (g, y.1) j : F)) * y.2.val := by
      rw [diagPoint, Units.val_mul, Iwasawa.diagonalUnits_val]
    rw [hval] at hJ
    obtain ⟨h1, h2⟩ := hRE _ y.2 hk hJ
    refine ⟨fun i _ => ⟨?_, ?_⟩, hk⟩
    · simpa using h1 i.succ
    · have := h2 i
      rwa [torusCoord_succ, ← Units.val_inv_eq_inv_val] at this
  · rfl

theorem congruenceGroup_anti {n M M' : ℕ} (h : M ≤ M') :
    congruenceGroup F n M' ≤ congruenceGroup F n M := fun _ hk =>
  ⟨matLattice_mono F (n + 1) (by omega) hk.1, matLattice_mono F (n + 1) (by omega) hk.2⟩

/-- For smooth `σ`, the family takes finitely many values and has measurable fibres. -/
theorem hFamily_finite (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F))
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) :
    (Set.range (hFamily F ψ σ Φ ℓ w)).Finite ∧
      ∀ v, MeasurableSet (hFamily F ψ σ Φ ℓ w ⁻¹' {v}) := by
  obtain ⟨M₁, hW⟩ := exists_model_congruence F ψ σ hσ ℓ w
  obtain ⟨m₀, hΦ₀⟩ := exists_schwartz_congruence F Φ
  have hΦ := hΦ₀ (max M₁ m₀) (le_max_right _ _)
  have hW' : ∀ κ ∈ congruenceGroup F (m + 1) (max M₁ m₀), ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * κ) = glModelFunction ψ (m + 1) σ ℓ w g :=
    fun κ hκ => hW κ (congruenceGroup_anti F (le_max_left _ _) hκ)
  have hloc : IsLocallyConstant (hFamily F ψ σ Φ ℓ w) :=
    isLocallyConstant_of_mul_right_invariant (isOpen_outerCongruence F (max M₁ m₀))
      (one_mem_outerCongruence F (max M₁ m₀))
      (fun y u hu => hFamily_mul_right F ψ σ hΦ hW' y u hu)
  obtain ⟨C, hC, hout⟩ := exists_compact_hFamily F ψ σ Φ ℓ w
  exact ⟨finite_range_of_isLocallyConstant hloc hC hout,
    fun v => measurableSet_fiber_of_isLocallyConstant hloc v⟩

/-- Every value of the family is the restriction to `diag(det g, 1, …, 1)` of a model
function: the corner transform is a Schwartz–Bruhat function of `det g`, and the Fourier
cutoff absorbs it into a right translate of `W`. -/
theorem exists_model_hFamily (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F))
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (y : (Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F) :
    ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) = hFamily F ψ σ Φ ℓ w y g := by
  classical
  by_cases hk : y.2 ∈ integralSet F (m + 1)
  · obtain ⟨φ₀, hφ₀⟩ := exists_cornerSchwartz F ψ Φ (fun i => (y.1 i : F)) hk
    set c : Fˣ := (∏ i, y.1 i)⁻¹ with hc
    let φ := schwartzBruhatComap (Homeomorph.mulRight₀ (c : F) c.ne_zero) φ₀
    let t : Langlands.GeneralLinear (m + 1 + 1) F := Iwasawa.diagonalUnits (Fin.cons c y.1)
    obtain ⟨w', hw'⟩ := exists_rankOneCutoff F ψ σ hσ ℓ
      (glModelRepresentation ψ (m + 1) σ ℓ (t * y.2) w) φ
    refine ⟨w', fun g => ?_⟩
    have hcoord : torusCoord (m + 1) (g, y.1) =
        Fin.cons (Matrix.GeneralLinearGroup.det g) 1 * Fin.cons c y.1 := by
      funext i
      induction i using Fin.cases with
      | zero => simp [hc]
      | succ i => simp
    have hD : diagPoint F (g, y) = rankOneEmbedding m g * (t * y.2) := by
      rw [diagPoint, hcoord, map_mul, rankOneEmbedding, mul_assoc]
    have hJ : φ ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) =
        unipotentTransform F ψ Φ (diagPoint F (g, y)).val := by
      have hdiag : (fun j => ((torusCoord (m + 1) (g, y.1) j : Fˣ) : F)) =
          Fin.cons (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * (c : F))
            (fun i => (y.1 i : F)) := by
        funext j
        induction j using Fin.cases with
        | zero => simp [hc]
        | succ j => simp
      simp only [φ, schwartzBruhatComap_apply, Homeomorph.coe_mulRight₀, hφ₀]
      rw [diagPoint, Units.val_mul, Iwasawa.diagonalUnits_val, hdiag]
    rw [hw', hFamily, ite_eq_left hk, hProduct, hJ, glModelFunction_translate, ← hD]
  · refine ⟨0, fun g => ?_⟩
    rw [hFamily, ite_eq_right hk]
    rfl

/-! ### The expansion -/

/-- The density identity `|det g|⁻ⁿ · |det g|^(s + n/2) = |det g|^(s - n/2)`, `n = m + 1`. -/
theorem weight_smul_determinantWeight (g : Langlands.GeneralLinear (0 + 1) F) (s z : ℂ) :
    (weight F (m + 1) (g, 1)) • (z * determinantWeight abv g (s + GodementJacquet.jpssShift (m + 1))) =
      z * determinantWeight abv g (s - ((m + 1 : ℕ) : ℂ) / 2) := by
  set r : ℝ := abv (Matrix.det g.val) with hr
  have hr' : r = (((⟨⟩ : LocalFieldData F).normalizedAbsUnits
      (Matrix.GeneralLinearGroup.det g) : ℝ≥0) : ℝ) := by
    rw [hr, (⟨⟩ : LocalFieldData F).normalizedAbsUnits_coe, normalizedAbsoluteValue_apply,
      Matrix.GeneralLinearGroup.val_det_apply]
  have hr0 : (r : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, hr, normalizedAbsoluteValue_apply]
    exact ((⟨⟩ : LocalFieldData F).normalizedAbs_pos (Matrix.GeneralLinearGroup.det_ne_zero g)).ne'
  rw [weight_glOne, NNReal.smul_def, Complex.real_smul]
  unfold determinantWeight GodementJacquet.jpssShift
  rw [← hr]
  have hexp : s - ((m + 1 : ℕ) : ℂ) / 2 = (s + ((m + 1 : ℕ) : ℂ) / 2) + (-((m + 1 : ℕ) : ℂ)) := by
    ring
  rw [hexp, Complex.cpow_add (s + ((m + 1 : ℕ) : ℂ) / 2) (-((m + 1 : ℕ) : ℂ)) hr0,
    Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [← hr']
  ring

theorem glModelFunction_sum (ℓ : glFunctionals ψ (m + 1) σ) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (x : ι → (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (m + 1 + 1) F) :
    glModelFunction ψ (m + 1) σ ℓ (∑ i ∈ S, c i • x i) g =
      ∑ i ∈ S, c i * glModelFunction ψ (m + 1) σ ℓ (x i) g := by
  simp [glModelFunction, Finset.sum_apply]

/-- **Expansion of the matrix integral.** For smooth `σ`, a matrix test function `Φ` and a
model vector `w`, one model vector `w'` (independent of `s`) satisfies: whenever the shifted
matrix integral `Z(Φ, s + (m+1)/2, W)` converges absolutely, the rank-one integral
`Ψ(s, W')` converges absolutely and equals it. -/
theorem exists_rankOneModel_of_matrix (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F))
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) :
    ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule, ∀ s : ℂ,
      Integrable (GodementJacquet.matrixIntegrand abv Φ (s + GodementJacquet.jpssShift (m + 1))
        (glModelFunction ψ (m + 1) σ ℓ w)) (generalLinearHaar F (m + 1)) →
      Integrable (rankOneModelIntegrand ψ abv σ ℓ w' s) (generalLinearHaar F 0) ∧
        ∫ y, GodementJacquet.matrixIntegrand abv Φ (s + GodementJacquet.jpssShift (m + 1))
          (glModelFunction ψ (m + 1) σ ℓ w) y ∂(generalLinearHaar F (m + 1)) =
        ∫ g, rankOneModelIntegrand ψ abv σ ℓ w' s g ∂(generalLinearHaar F 0) := by
  classical
  obtain ⟨hfin, hmeas⟩ := hFamily_finite F ψ σ hσ Φ ℓ w
  set Hf := hFamily F ψ σ Φ ℓ w with hHf
  have hrep : ∀ v ∈ Set.range Hf, ∃ w' : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ g, glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g) = v g := by
    rintro v ⟨y, rfl⟩
    exact exists_model_hFamily F ψ σ hσ Φ ℓ w y
  let wstar : (Langlands.GeneralLinear (0 + 1) F → ℂ) →
      (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule := fun v =>
    if hv : v ∈ Set.range Hf then Classical.choose (hrep v hv) else 0
  have hwstar : ∀ v ∈ Set.range Hf, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ (wstar v) (rankOneEmbedding m g) = v g := by
    intro v hv g
    simp only [wstar, dite_eq_left hv]
    exact Classical.choose_spec (hrep v hv) g
  set ν := (tailMeasure F (m + 1)).prod ((generalLinearHaar F (m + 1)).restrict
    (integralSet F (m + 1))) with hν
  set c : (Langlands.GeneralLinear (0 + 1) F → ℂ) → ℂ := fun v => (ν.real (Hf ⁻¹' {v}) : ℂ)
    with hc
  refine ⟨∑ v ∈ hfin.toFinset, c v • wstar v, fun s hint => ?_⟩
  set h : Langlands.GeneralLinear (0 + 1) F → ℂ :=
    fun g => determinantWeight abv g (s + GodementJacquet.jpssShift (m + 1)) with hh
  obtain ⟨hI, hEq⟩ := integral_matrixIntegrand_unfold F ψ Φ (glModelFunction ψ (m + 1) σ ℓ w)
    (fun u y => glModelFunction_equivariance ψ (m + 1) σ ℓ w u y)
    (s + GodementJacquet.jpssShift (m + 1)) hint
  have hae : (fun x => unipotentTransform F ψ Φ (diagPoint F x).val *
      (glModelFunction ψ (m + 1) σ ℓ w (diagPoint F x) *
        determinantWeight abv (diagPoint F x) (s + GodementJacquet.jpssShift (m + 1))))
      =ᵐ[outerMeasure F (m + 1)] (fun p => Hf p.2 p.1 * h p.1) := by
    filter_upwards [ae_outerMeasure_mem F] with x hx
    simp only [hHf, hFamily, ite_eq_left hx, hProduct, hh,
      determinantWeight_diagPoint F _ x hx]
    ring
  have hIprod : Integrable (fun p : Langlands.GeneralLinear (0 + 1) F ×
      ((Fin (m + 1) → Fˣ) × Langlands.GeneralLinear (m + 1 + 1) F) =>
      Hf p.2 p.1 * h p.1) ((glOneMeasure F (m + 1)).prod ν) := hI.congr hae
  have hsum := integral_prod_eq_sum_levelSets hfin hmeas h hIprod
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F => weight F (m + 1) (g, 1) :=
    (continuous_weight F (m + 1)).measurable.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ v ∈ Set.range Hf, ∀ g, weight F (m + 1) (g, 1) • (v g * h g) =
      rankOneModelIntegrand ψ abv σ ℓ (wstar v) s g := by
    intro v hv g
    rw [rankOneModelIntegrand, hwstar v hv g, hh]
    exact weight_smul_determinantWeight F g s (v g)
  have hval : ∀ v ∈ hfin.toFinset, ∫ g, v g * h g ∂(glOneMeasure F (m + 1)) =
      ∫ g, rankOneModelIntegrand ψ abv σ ℓ (wstar v) s g ∂(generalLinearHaar F 0) := by
    intro v hv
    rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (hpt v ((Set.Finite.mem_toFinset hfin).1 hv)))
  have hterm : ∀ v ∈ hfin.toFinset, Integrable (fun g => c v *
      rankOneModelIntegrand ψ abv σ ℓ (wstar v) s g) (generalLinearHaar F 0) := by
    intro v hv
    by_cases h0 : ν (Hf ⁻¹' {v}) = 0
    · have : c v = 0 := by simp [hc, Measure.real, h0]
      simp only [this, zero_mul]
      exact integrable_zero _ _ _
    · have hvi := integrable_of_integrable_prod_levelSet h hIprod h0
      rw [glOneMeasure, integrable_withDensity_iff_integrable_smul hwm] at hvi
      refine (hvi.congr (Filter.Eventually.of_forall fun g => ?_)).const_mul (c v)
      exact hpt v ((Set.Finite.mem_toFinset hfin).1 hv) g
  have hlin : rankOneModelIntegrand ψ abv σ ℓ (∑ v ∈ hfin.toFinset, c v • wstar v) s =
      fun g => ∑ v ∈ hfin.toFinset, c v * rankOneModelIntegrand ψ abv σ ℓ (wstar v) s g := by
    funext g
    rw [rankOneModelIntegrand, glModelFunction_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [rankOneModelIntegrand]
    ring
  refine ⟨?_, ?_⟩
  · rw [hlin]
    exact integrable_finsetSum _ hterm
  · rw [hEq, integral_congr_ae hae]
    change ∫ p, Hf p.2 p.1 * h p.1 ∂((glOneMeasure F (m + 1)).prod ν) = _
    rw [hsum, hlin, integral_finsetSum _ hterm]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [integral_const_mul, hval v hv]

/-- **Right ⊆ Left.** The shifted matrix values of the model of `ℓ` lie in the rank-one
model values. -/
theorem whittakerRationalValues_subset_rankOneModelValues (hσ : IsSmooth σ)
    (ℓ : glFunctionals ψ (m + 1) σ) :
    Langlands.AllField.GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ ⊆
      rankOneModelValues (⟨⟩ : LocalFieldData F).residueCardinality ψ abv
        (generalLinearHaar F 0) σ ℓ := by
  rintro R ⟨Φ, w, ⟨a, ha⟩, hcont⟩
  obtain ⟨w', hw'⟩ := exists_rankOneModel_of_matrix F ψ σ hσ ℓ Φ w
  refine ⟨w', ⟨a, fun s hs => (hw' s (ha s hs)).1⟩, ?_⟩
  obtain ⟨a₁, ha₁⟩ := hcont
  refine ⟨max a a₁, fun s hs => ?_⟩
  obtain ⟨hden, heq⟩ := ha₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
  refine ⟨hden, ?_⟩
  change (∫ g, rankOneModelIntegrand ψ abv σ ℓ w' s g ∂(generalLinearHaar F 0)) = _
  rw [← (hw' s (ha s (lt_of_le_of_lt (le_max_left _ _) hs))).2]
  exact heq

end Expansion

end Langlands.AllField.RankinSelberg.RankOneIwasawa
