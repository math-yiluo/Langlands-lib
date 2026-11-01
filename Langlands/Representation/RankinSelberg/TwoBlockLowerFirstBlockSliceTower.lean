import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberKernels
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# The first-block slice tower of the lower mixed quotient

For every determinant order `k`, the unweighted first-block slice kernel composed with
the zero slice of a compatible lower mixed quotient measure is, after the density
`q^(-k b)`, the slice `k` of the compatible lower quotient measure.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
open scoped ENNReal NNReal CompactlySupported ProbabilityTheory

universe uF

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (K : Type*) [CommRing K]

/-- `diag(u, y) R(Z) I(v) = diag(u v, y) R(Z v)`. -/
theorem leviEmbedding_mul_lowerRadical_mul_firstBlockEmbedding
    (u : GeneralLinear (m 0 + 1) K) (y : GeneralLinear (m 1 + 1) K)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K) (v : GeneralLinear (m 0 + 1) K) :
    (succBlockShape m h).leviEmbedding K (blockPair (m := m) K (u, y)) * lowerRadical h K Z *
        firstBlockEmbedding h K v =
      (succBlockShape m h).leviEmbedding K (blockPair (m := m) K (u * v, y)) *
        lowerRadical h K (Z * v.val) := by
  have hc := firstBlockEmbedding_mul_lowerRadical h K v (Z * v.val)
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at hc
  rw [mul_assoc, ← hc, ← mul_assoc, firstBlockEmbedding_apply, ← map_mul, ← map_mul,
    Prod.mk_mul_mk, mul_one]

/-- `I(z) diag(u, y) = diag(z u, y)`. -/
theorem firstBlockEmbedding_mul_leviEmbedding
    (z u : GeneralLinear (m 0 + 1) K) (y : GeneralLinear (m 1 + 1) K) :
    firstBlockEmbedding h K z * (succBlockShape m h).leviEmbedding K (blockPair (m := m) K (u, y)) =
      (succBlockShape m h).leviEmbedding K (blockPair (m := m) K (z * u, y)) := by
  rw [firstBlockEmbedding_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, one_mul]

end Algebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance lowerSliceTowerInstance01 : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance lowerSliceTowerInstance02 : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance lowerSliceTowerInstance03 : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance lowerSliceTowerInstance04 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance lowerSliceTowerInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerSliceTowerInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerSliceTowerInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerSliceTowerInstance08 (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerSliceTowerInstance09 (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerSliceTowerInstance10 (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerSliceTowerInstance11 (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerSliceTowerInstance12 (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerSliceTowerInstance13 (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerSliceTowerInstance14 (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerSliceTowerInstance15 (n : ℕ) :
    MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerSliceTowerInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerSliceTowerInstance17 (n : ℕ) :
    SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance18 (n : ℕ) :
    LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerSliceTowerInstance19 (n : ℕ) :
    MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerSliceTowerInstance20 (n : ℕ) :
    BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerSliceTowerInstance21 (n : ℕ) :
    SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance22 (n : ℕ) :
    LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerSliceTowerInstance23 (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance lowerSliceTowerInstance24 (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance lowerSliceTowerInstance25 (n : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient n F.Carrier) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)

section Slices

/-- The ambient determinant slice `G^k = {g | ord(det g) = k}` of `GL_n`. -/
def ambientSlice (n : ℕ) (k : ℤ) : Set (GeneralLinear n F.Carrier) :=
  {g | F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k}

theorem isClopen_ambientSlice (n : ℕ) (k : ℤ) : IsClopen (ambientSlice F n k) :=
  (isClopen_discrete ({k} : Set ℤ)).preimage
    ((RankinSelberg.continuous_ord_units F.canonicalTopologicalData).comp
      (F.canonicalTopologicalData.generalLinearDeterminant n).continuous)

/-- Left multiplication by a norm-one matrix preserves the determinant order. -/
theorem ord_determinant_mul_of_mem {n : ℕ} {u : GeneralLinear n F.Carrier}
    (hu : u ∈ normOneSubgroup F n) (g : GeneralLinear n F.Carrier) :
    F.canonicalTopologicalData.ord (GeneralLinear.determinant (u * g) : F.Carrier) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  rw [map_mul, Units.val_mul, F.canonicalTopologicalData.ord_mul
    (GeneralLinear.determinant u).ne_zero (GeneralLinear.determinant g).ne_zero,
    ord_determinant_eq_zero F hu, zero_add]

/-- Averaging over a subgroup of `GL_n^0` commutes with cutting by an ambient slice. -/
theorem quotientAverageReal_indicator_ambientSlice {n : ℕ}
    (S : Subgroup (GeneralLinear n F.Carrier)) (hS : S ≤ normOneSubgroup F n)
    [MeasurableSpace S] [MeasurableMul S] (μS : Measure S) [μS.IsMulRightInvariant]
    (f : GeneralLinear n F.Carrier → ℝ) (k : ℤ) (g : GeneralLinear n F.Carrier) :
    quotientAverageReal S μS ((ambientSlice F n k).indicator f) (Quotient.mk _ g) =
      (ambientSlice F n k).indicator
        (fun x => quotientAverageReal S μS f (Quotient.mk _ x)) g := by
  have hmem : ∀ s : S, s.val * g ∈ ambientSlice F n k ↔ g ∈ ambientSlice F n k := by
    intro s
    change F.canonicalTopologicalData.ord _ = k ↔ F.canonicalTopologicalData.ord _ = k
    rw [ord_determinant_mul_of_mem F (hS s.property)]
  rw [quotientAverageReal_mk]
  by_cases hg : g ∈ ambientSlice F n k
  · rw [Set.indicator_of_mem hg, quotientAverageReal_mk]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
      Set.indicator_of_mem ((hmem s).2 hg) f)
  · rw [Set.indicator_of_notMem hg]
    have hz : (fun s : S => (ambientSlice F n k).indicator f (s.val * g)) = fun _ => 0 :=
      funext fun s => Set.indicator_of_notMem (fun hs => hg ((hmem s).1 hs)) f
    rw [hz, integral_zero]

end Slices

section Scaling

variable {a b : ℕ}

/-- Right multiplication by `v` with `ord(det v) = k` scales every rectangular additive
Haar on `b × a` matrices by `q^(k b)`; the density `q^(-k b)` compensates it. -/
theorem lintegral_mul_right_of_ord
    (μR : Measure (Matrix (Fin b) (Fin a) F.Carrier)) [μR.IsAddHaarMeasure]
    (φ : Matrix (Fin b) (Fin a) F.Carrier → ℝ≥0∞) (hφ : Measurable φ)
    (v : GeneralLinear a F.Carrier) (k : ℤ)
    (hv : F.canonicalTopologicalData.ord (GeneralLinear.determinant v : F.Carrier) = k) :
    ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(k * (b : ℤ)))) *
        ∫⁻ Z, φ (Z * v.val) ∂μR =
      ∫⁻ Z, φ Z ∂μR := by
  have hs := HarmonicAnalysis.padicRectangularHaarScaling F F.canonicalTopologicalData b a μR
    1 v⁻¹
  simp only [inv_inv, Units.val_one, Matrix.one_mul] at hs
  have hm : Measurable (fun X : Matrix (Fin b) (Fin a) F.Carrier => X * v.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one)
  have hc : ((((F.canonicalTopologicalData.determinantNorm b 1 : ℝ≥0) ^ a /
      (F.canonicalTopologicalData.determinantNorm a v⁻¹ : ℝ≥0) ^ b)⁻¹ : ℝ≥0) : ℝ) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (k * (b : ℤ)) := by
    rw [map_one, map_inv, Units.val_one, Units.val_inv_eq_inv_val, one_pow, one_div, inv_inv,
      NNReal.coe_pow, NNReal.coe_inv,
      F.canonicalTopologicalData.determinantNorm_eq_residue_pow a v, hv, zpow_neg, inv_inv,
      ← zpow_natCast, ← zpow_mul]
  rw [← lintegral_map hφ hm, hs, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_coe_nnreal, hc,
    ← ENNReal.ofReal_mul (zpow_pos hq _).le, ← zpow_add₀ hq.ne', neg_add_cancel, zpow_zero,
    ENNReal.ofReal_one, one_mul]

end Scaling

section SmallOrbit

/-- The small orbital measure restricted to slice `k` is the left translate by `z` of the
norm-one Haar, for any `z` with `ord(det z) = k`. -/
theorem small_orbitKernel_comp_slice (n : ℕ)
    (νA : Measure (LeftUnipotentQuotient n F.Carrier))
    (hνA : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) νA)
    (z : GeneralLinear (n + 1) F.Carrier) (k : ℤ)
    (hz : F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k) :
    orbitKernel (upperUnipotent (n + 1) F.Carrier) (UpperUnipotent.isClosed (R := F.Carrier))
        (unipotentHaar F.Carrier n) ∘ₘ
      νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData n k) =
        Measure.map (fun u : normOneSubgroup F (n + 1) => z * u.val) (normOneHaar F n) := by
  let N := upperUnipotent (n + 1) F.Carrier
  let κ := orbitKernel N (UpperUnipotent.isClosed (R := F.Carrier)) (unipotentHaar F.Carrier n)
  let s := RankinSelberg.determinantSlice F.canonicalTopologicalData n k
  let π : GeneralLinear (n + 1) F.Carrier → LeftUnipotentQuotient n F.Carrier := Quotient.mk _
  have hs : MeasurableSet s := RankinSelberg.isClosed_determinantSlice _ n k |>.measurableSet
  have hπ : Measurable π := continuous_quotient_mk'.measurable
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ π ⁻¹' s) = s.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk N _ _ g,
        Measure.map_apply (continuous_subtype_val.mul_const g).measurable (hA.inter (hπ hs))]
      have he : ∀ a : N, π (a.val * g) = π g := fun a =>
        TwoBlockUnipotentQuotient.mk_mul_of_mem N a.property g
      by_cases hq : π g ∈ s
      · rw [Set.indicator_of_mem hq, show κ (Quotient.mk _ g) = _ from orbitKernel_mk N _ _ g,
          Measure.map_apply (continuous_subtype_val.mul_const g).measurable hA]
        congr 1
        ext a
        simp [he, hq]
      · rw [Set.indicator_of_notMem hq]
        have hempty : (fun a : N => a.val * g) ⁻¹' (A ∩ π ⁻¹' s) = ∅ := by
          ext a
          simp [he, hq]
        rw [hempty, measure_empty]
  have hcomp : κ ∘ₘ νA.restrict s = (generalLinearHaar F.Carrier n).restrict (π ⁻¹' s) := by
    ext A hA
    rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.restrict_apply hA,
      ← lintegral_indicator hs]
    rw [show (∫⁻ q, s.indicator (fun q => κ q A) q ∂νA) =
      ∫⁻ q, κ q (A ∩ π ⁻¹' s) ∂νA from
        lintegral_congr fun q => (hpt A hA q).symm]
    rw [← Measure.bind_apply (hA.inter (hπ hs)) κ.measurable.aemeasurable,
      show κ ∘ₘ νA = generalLinearHaar F.Carrier n from
        orbitKernel_comp N (UpperUnipotent.isClosed (R := F.Carrier)) _ _ νA hνA]
  let e := MeasurableEquiv.mulLeft z
  have hpre : e ⁻¹' (π ⁻¹' s) = (normOneSubgroup F (n + 1) : Set _) := by
    ext u
    change F.canonicalTopologicalData.ord (GeneralLinear.determinant (z * u) : F.Carrier) = k ↔ _
    rw [map_mul, Units.val_mul, F.canonicalTopologicalData.ord_mul
      (GeneralLinear.determinant z).ne_zero (GeneralLinear.determinant u).ne_zero, hz,
      add_eq_left, PadicField.TopologicalData.ord_eq_zero_iff_normalizedAbs,
      Matrix.GeneralLinearGroup.val_det_apply, ← mem_normOneSubgroup_iff_normalizedAbs]
    rfl
  have hmap : Measure.map e (generalLinearHaar F.Carrier n) = generalLinearHaar F.Carrier n :=
    map_mul_left_eq_self (generalLinearHaar F.Carrier n) z
  calc κ ∘ₘ νA.restrict s = (generalLinearHaar F.Carrier n).restrict (π ⁻¹' s) := hcomp
    _ = (Measure.map e (generalLinearHaar F.Carrier n)).restrict (π ⁻¹' s) := by rw [hmap]
    _ = Measure.map e ((generalLinearHaar F.Carrier n).restrict (e ⁻¹' (π ⁻¹' s))) :=
      e.measurableEmbedding.restrict_map _ _
    _ = Measure.map e (Measure.map Subtype.val (normOneHaar F n)) := by
      rw [hpre, map_normOneHaar]
    _ = _ := Measure.map_map e.measurable continuous_subtype_val.measurable

end SmallOrbit

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerSliceTowerInstance26 : MeasurableSpace (lowerBlockUnipotent h F.Carrier) :=
  borel _
local instance lowerSliceTowerInstance27 : BorelSpace (lowerBlockUnipotent h F.Carrier) := ⟨rfl⟩
local instance lowerSliceTowerInstance28 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerSliceTowerInstance29 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceTowerInstance30 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance31 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace
local instance lowerSliceTowerInstance32 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerSliceTowerInstance33 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceTowerInstance34 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceTowerInstance35 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerSliceTowerInstance36 : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance lowerSliceTowerInstance37 : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance lowerSliceTowerInstance38 : T2Space (LowerQuotient h F.Carrier) :=
  t2Space_lowerQuotient_canonical F h
local instance lowerSliceTowerInstance39 : LocallyCompactSpace (LowerQuotient h F.Carrier) :=
  leftQuotient_locallyCompactSpace _
local instance lowerSliceTowerInstance40 : SecondCountableTopology (LowerQuotient h F.Carrier) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerSliceTowerInstance41 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerSliceTowerInstance42 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local notation "O" => Valuation.integer (ValuativeRel.valuation F.Carrier)

section PerPoint

/-- **Per-point slice identity.** Over the small slice `k`, the density times the integral
of the `H⁻` averages at the first-block fiber points of `g` is the lower mixed average at
`g` of the left translate `x ↦ f(I(z) x)`, for any `z` with `ord(det z) = k`. -/
theorem lintegral_firstBlockFiberPoint_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [μR.IsAddHaarMeasure]
    (f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (k : ℤ) (z : GeneralLinear (m 0 + 1) F.Carrier)
    (hz : F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k)
    (g : GeneralLinear (t + 1) F.Carrier) :
    ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
          (lowerHaar F h) f (firstBlockFiberPoint F h q g))
        ∂νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k) =
      ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
        (fun x => f (firstBlockEmbedding h F.Carrier z * x)) (Quotient.mk _ g)) := by
  have hδT : ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
      (-(k * ((m 1 + 1 : ℕ) : ℤ)))) ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨hc0, hcT⟩ :=
    TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F (m 1 + 1) (m 0 + 1) μR
  have hR : Continuous (lowerRadical h F.Carrier :
      Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier → GeneralLinear (t + 1) F.Carrier) :=
    continuous_lowerRadical h F.Carrier
  have hD : Continuous (fun x : GeneralLinear (m 0 + 1) F.Carrier ×
      upperUnipotent (m 1 + 1) F.Carrier =>
        (succBlockShape m h).leviEmbedding F.Carrier (blockPair (m := m) F.Carrier
          (x.1, x.2.val))) :=
    ((succBlockShape m h).leviEmbeddingContinuous F.Carrier).continuous.comp
      ((continuous_blockPair F.Carrier).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hΨ : Measurable (fun p : (GeneralLinear (m 0 + 1) F.Carrier ×
      upperUnipotent (m 1 + 1) F.Carrier) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier =>
        ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
          (blockPair (m := m) F.Carrier (p.1.1, p.1.2.val)) * lowerRadical h F.Carrier p.2 * g))) :=
    (ENNReal.continuous_ofReal.comp (f.continuous.comp
      (((hD.comp continuous_fst).mul (hR.comp continuous_snd)).mul continuous_const))).measurable
  have hG2 : Measurable (fun x : GeneralLinear (m 0 + 1) F.Carrier ×
      upperUnipotent (m 1 + 1) F.Carrier =>
        ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
          (blockPair (m := m) F.Carrier (x.1, x.2.val)) * lowerRadical h F.Carrier Z * g))
          ∂μR) :=
    hΨ.lintegral_prod_right'
  let Φ : GeneralLinear (m 0 + 1) F.Carrier → ℝ≥0∞ := fun u =>
    ∫⁻ y : upperUnipotent (m 1 + 1) F.Carrier, ∫⁻ Z,
      ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
        (blockPair (m := m) F.Carrier (u, y.val)) * lowerRadical h F.Carrier Z * g))
      ∂μR ∂unipotentHaar F.Carrier (m 1)
  have hΦ : Measurable Φ := hG2.lintegral_prod_right'
  -- Step 1: the `H⁻` average at `[I(v) g]` in block coordinates, rescaled on slice `k`.
  have hpt : ∀ v : GeneralLinear (m 0 + 1) F.Carrier,
      F.canonicalTopologicalData.ord (GeneralLinear.determinant v : F.Carrier) = k →
      ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
        (μR {Z | ∀ i j, Z i j ∈ O} *
          ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f
            (firstBlockFiberPoint F h (Quotient.mk _ v) g))) =
      ∫⁻ x : upperUnipotent (m 0 + 1) F.Carrier, Φ (x.val * v)
        ∂unipotentHaar F.Carrier (m 0) := by
    intro v hv
    have hψ : Measurable (fun x : GeneralLinear (t + 1) F.Carrier =>
        ENNReal.ofReal (f (x * (firstBlockEmbedding h F.Carrier v * g)))) :=
      (ENNReal.continuous_ofReal.comp
        (f.continuous.comp (continuous_id.mul continuous_const))).measurable
    have hav : ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
        (lowerHaar F h) f (firstBlockFiberPoint F h (Quotient.mk _ v) g)) =
        ∫⁻ x : lowerBlockUnipotent h F.Carrier,
          ENNReal.ofReal (f (x.val * (firstBlockEmbedding h F.Carrier v * g))) ∂lowerHaar F h := by
      rw [firstBlockFiberPoint_mk, quotientAverageReal_mk]
      exact ofReal_integral_eq_lintegral_ofReal
        (integrable_subgroup_mul _ (isClosed_lowerBlockUnipotent_canonical F h)
          (lowerHaar F h) f _)
        (Filter.Eventually.of_forall fun _ => hf0 _)
    have hinner : ∀ (y : upperUnipotent (m 1 + 1) F.Carrier)
        (x : upperUnipotent (m 0 + 1) F.Carrier),
        ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
            (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
          ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
            (blockPair (m := m) F.Carrier (x.val, y.val)) * lowerRadical h F.Carrier Z *
              (firstBlockEmbedding h F.Carrier v * g))) ∂μR =
        ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
          (blockPair (m := m) F.Carrier (x.val * v, y.val)) * lowerRadical h F.Carrier Z * g))
          ∂μR := by
      intro y x
      have hφ : Measurable (fun Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier =>
          ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
            (blockPair (m := m) F.Carrier (x.val * v, y.val)) * lowerRadical h F.Carrier Z *
              g))) :=
        (ENNReal.continuous_ofReal.comp (f.continuous.comp
          ((continuous_const.mul hR).mul continuous_const))).measurable
      refine Eq.trans ?_ (lintegral_mul_right_of_ord F μR _ hφ v k hv)
      refine congrArg (HMul.hMul _) (lintegral_congr fun Z => ?_)
      rw [← mul_assoc, leviEmbedding_mul_lowerRadical_mul_firstBlockEmbedding]
    have hswap : AEMeasurable (Function.uncurry fun (y : upperUnipotent (m 1 + 1) F.Carrier)
        (x : upperUnipotent (m 0 + 1) F.Carrier) =>
          ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
            (blockPair (m := m) F.Carrier (x.val * v, y.val)) * lowerRadical h F.Carrier Z * g))
            ∂μR)
        ((unipotentHaar F.Carrier (m 1)).prod (unipotentHaar F.Carrier (m 0))) :=
      (Measurable.lintegral_prod_right' (ν := μR)
        (f := fun p : (upperUnipotent (m 1 + 1) F.Carrier × upperUnipotent (m 0 + 1) F.Carrier) ×
          Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier =>
            ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
              (blockPair (m := m) F.Carrier (p.1.2.val * v, p.1.1.val)) *
                lowerRadical h F.Carrier p.2 * g)))
        (ENNReal.continuous_ofReal.comp (f.continuous.comp
          (((((succBlockShape m h).leviEmbeddingContinuous F.Carrier).continuous.comp
            ((continuous_blockPair F.Carrier).comp
              (((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).mul
                continuous_const).prodMk
                (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))))).mul
            (hR.comp continuous_snd)).mul continuous_const))).measurable).aemeasurable
    rw [hav, lintegral_lowerHaar F h μR _ hψ, ← lintegral_const_mul' _ _ hδT]
    calc
      _ = ∫⁻ y : upperUnipotent (m 1 + 1) F.Carrier, ∫⁻ x : upperUnipotent (m 0 + 1) F.Carrier,
          ∫⁻ Z, ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
            (blockPair (m := m) F.Carrier (x.val * v, y.val)) * lowerRadical h F.Carrier Z * g))
            ∂μR ∂unipotentHaar F.Carrier (m 0) ∂unipotentHaar F.Carrier (m 1) := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ hδT]
        exact lintegral_congr fun x => hinner y x
      _ = _ := lintegral_lintegral_swap hswap
  -- Step 2: integrate over the small slice; the orbit kernel unfolds to `z GL^0`.
  let κA := orbitKernel (upperUnipotent (m 0 + 1) F.Carrier)
    (UpperUnipotent.isClosed (R := F.Carrier)) (unipotentHaar F.Carrier (m 0))
  have hslice : MeasurableSet (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k) :=
    RankinSelberg.isClosed_determinantSlice _ (m 0) k |>.measurableSet
  have hAQ : ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
      (μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
            (lowerHaar F h) f (firstBlockFiberPoint F h q g))
          ∂νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) =
      ∫⁻ u, Φ u ∂(κA ∘ₘ
        νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) := by
    rw [Measure.lintegral_bind κA.measurable.aemeasurable hΦ.aemeasurable,
      ← lintegral_const_mul' _ _ hcT.ne, ← lintegral_const_mul' _ _ hδT]
    refine setLIntegral_congr_fun hslice fun q hq => ?_
    revert hq
    induction q using Quotient.inductionOn with
    | h v =>
      intro hv
      rw [show κA (Quotient.mk _ v) = _ from orbitKernel_mk _ _ _ v,
        lintegral_map hΦ (continuous_subtype_val.mul_const v).measurable]
      exact hpt v hv
  -- Step 3: the norm-one integral of `Φ(z ·)` is the cube times the lower mixed average.
  have hψz : Measurable (fun x : GeneralLinear (t + 1) F.Carrier =>
      ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z * (x * g)))) :=
    (ENNReal.continuous_ofReal.comp (f.continuous.comp
      (continuous_const.mul (continuous_id.mul continuous_const)))).measurable
  have hm : Measurable (mixedSubgroupEquiv F h) :=
    (mixedSubgroupHomeomorph F h).continuous.measurable
  have hDm : Continuous (fun d : normOneSubgroup F (m 0 + 1) ×
      upperUnipotent (m 1 + 1) F.Carrier => mixedEmbedding F h d) :=
    continuous_subtype_val.comp (mixedSubgroupHomeomorph F h).continuous
  have hprod : Measurable (fun p : (normOneSubgroup F (m 0 + 1) ×
      upperUnipotent (m 1 + 1) F.Carrier) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier =>
        ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z *
          (mixedEmbedding F h p.1 * lowerRadical h F.Carrier p.2 * g)))) :=
    hψz.comp ((hDm.comp continuous_fst).mul (hR.comp continuous_snd)).measurable
  have hmix : ∫⁻ a0 : normOneSubgroup F (m 0 + 1), Φ (z * a0.val) ∂normOneHaar F (m 0) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ l : lowerMixedSubgroup F h,
          ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z * (l.val * g)))
          ∂lowerMixedHaar F h := by
    calc
      _ = ∫⁻ a0 : normOneSubgroup F (m 0 + 1), ∫⁻ y : upperUnipotent (m 1 + 1) F.Carrier,
            ∫⁻ Z, ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z *
              (mixedEmbedding F h (a0, y) * lowerRadical h F.Carrier Z * g)))
            ∂μR ∂unipotentHaar F.Carrier (m 1) ∂normOneHaar F (m 0) := by
          refine lintegral_congr fun a0 => lintegral_congr fun y => lintegral_congr fun Z => ?_
          show ENNReal.ofReal (f ((succBlockShape m h).leviEmbedding F.Carrier
              (blockPair (m := m) F.Carrier (z * a0.val, y.val)) * lowerRadical h F.Carrier Z *
                g)) = _
          rw [mixedEmbedding_apply, ← mul_assoc, ← mul_assoc,
            firstBlockEmbedding_mul_leviEmbedding]
      _ = ∫⁻ d, ∫⁻ Z, ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z *
              (mixedEmbedding F h d * lowerRadical h F.Carrier Z * g))) ∂μR
            ∂(normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1)) :=
          (lintegral_prod _ hprod.lintegral_prod_right'.aemeasurable).symm
      _ = ∫⁻ Z, ∫⁻ d, ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z *
              (mixedEmbedding F h d * lowerRadical h F.Carrier Z * g)))
            ∂(normOneHaar F (m 0)).prod (unipotentHaar F.Carrier (m 1)) ∂μR :=
          lintegral_lintegral_swap hprod.aemeasurable
      _ = ∫⁻ Z, ∫⁻ a : mixedSubgroup F h, ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z *
              (a.val * lowerRadical h F.Carrier Z * g))) ∂mixedHaar F h ∂μR := by
          refine lintegral_congr fun Z => ?_
          rw [mixedHaar, lintegral_map (f := fun a : mixedSubgroup F h =>
              ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z *
                (a.val * lowerRadical h F.Carrier Z * g))))
            (hψz.comp (continuous_subtype_val.mul_const _).measurable) hm]
          rfl
      _ = _ := lintegral_mixedHaar_radical F h μR _ hψz
  have hLavg : ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
      (fun x => f (firstBlockEmbedding h F.Carrier z * x)) (Quotient.mk _ g)) =
      ∫⁻ l : lowerMixedSubgroup F h,
        ENNReal.ofReal (f (firstBlockEmbedding h F.Carrier z * (l.val * g)))
        ∂lowerMixedHaar F h := by
    rw [quotientAverageReal_mk]
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_subgroup_mul_of_hasCompactSupport (lowerMixedSubgroup F h)
        (isClosed_lowerMixedSubgroup F h) (lowerMixedHaar F h) _
        (f.continuous.comp (continuous_const.mul continuous_id))
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft _)) g)
      (Filter.Eventually.of_forall fun _ => hf0 _)
  have key : μR {Z | ∀ i j, Z i j ∈ O} *
      (ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
            (lowerHaar F h) f (firstBlockFiberPoint F h q g))
          ∂νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) k)) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
          (fun x => f (firstBlockEmbedding h F.Carrier z * x)) (Quotient.mk _ g)) := by
    rw [mul_left_comm, hAQ, small_orbitKernel_comp_slice F (m 0) νA hνA z k hz,
      lintegral_map hΦ (show Measurable (fun u : normOneSubgroup F (m 0 + 1) => z * u.val) from
        (continuous_const.mul continuous_subtype_val).measurable), hmix, hLavg]
  exact (ENNReal.mul_right_inj hc0.ne' hcT.ne).mp key

/-- The composite first-block slice kernel integrates `H⁻` averages to the lower mixed
averages of the left translate `x ↦ f(I(z) x)`, after the density, for every outer measure. -/
theorem lintegral_firstBlockKernel_comp_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (ν : Measure (LowerMixedQuotient F h))
    (f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (k : ℤ) (z : GeneralLinear (m 0 + 1) F.Carrier)
    (hz : F.canonicalTopologicalData.ord (GeneralLinear.determinant z : F.Carrier) = k) :
    ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) *
      ∫⁻ x, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
          (lowerHaar F h) f x) ∂(firstBlockKernel F h νA hInv k ∘ₘ ν) =
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
        (fun x => f (firstBlockEmbedding h F.Carrier z * x)) q) ∂ν := by
  have hHm : Measurable (fun x => ENNReal.ofReal (quotientAverageReal
      (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f x)) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (isClosed_lowerBlockUnipotent_canonical F h) _ f)).measurable
  rw [Measure.lintegral_bind (firstBlockKernel F h νA hInv k).measurable.aemeasurable
    hHm.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun a => firstBlockFiberPoint F h a g) :=
      ((continuous_firstBlockFiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockKernel_mk, lintegral_map hHm hfm]
    exact lintegral_firstBlockFiberPoint_quotientAverageReal F h νA hνA
      (Measure.addHaar : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))
      f hf0 k z hz g

end PerPoint

section Extension

/-- Two measures on `H⁻ \ G` that integrate every nonnegative `H⁻` average to the same
finite value coincide. -/
theorem eq_of_lintegral_lowerQuotientAverageReal
    (μ₁ μ₂ : Measure (LowerQuotient h F.Carrier))
    (I : C_c(GeneralLinear (t + 1) F.Carrier, ℝ) → ℝ≥0∞)
    (hI : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ x, 0 ≤ f x) → I f < ⊤)
    (h₁ : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ x, 0 ≤ f x) →
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
        (lowerHaar F h) f q) ∂μ₁ = I f)
    (h₂ : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ x, 0 ≤ f x) →
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
        (lowerHaar F h) f q) ∂μ₂ = I f) :
    μ₁ = μ₂ := by
  let H := lowerBlockUnipotent h F.Carrier
  let μH := lowerHaar F h
  have hH := isClosed_lowerBlockUnipotent_canonical F h
  have hlift : ∀ φ : C_c(LowerQuotient h F.Carrier, ℝ), (∀ q, 0 ≤ φ q) →
      ∃ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ y, 0 ≤ f y) ∧
        ∀ q, quotientAverageReal H μH f q = φ q := by
    intro φ hφ
    obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting H hH μH φ
    refine ⟨f, hf0 hφ, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have hfin : ∀ μ' : Measure (LowerQuotient h F.Carrier),
      (∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ x, 0 ≤ f x) →
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' = I f) →
      IsFiniteMeasureOnCompacts μ' := by
    intro μ' hμ'
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(LowerQuotient h F.Carrier, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := hlift φ fun q => (hu01 q).1
    calc μ' C = ∫⁻ q, C.indicator 1 q ∂μ' :=
          (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' := by
          apply lintegral_mono
          intro q
          dsimp only
          rw [hfavg q]
          by_cases hq : q ∈ C
          · rw [Set.indicator_of_mem hq]
            change (1 : ENNReal) ≤ ENNReal.ofReal (u q)
            rw [hu1 hq, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hq]
            exact zero_le
      _ = I f := hμ' f hf0
      _ < ⊤ := hI f hf0
  have : IsFiniteMeasureOnCompacts μ₁ := hfin μ₁ h₁
  have : IsFiniteMeasureOnCompacts μ₂ := hfin μ₂ h₂
  have : μ₁.Regular := inferInstance
  have : μ₂.Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(LowerQuotient h F.Carrier, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := hlift φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (LowerQuotient h F.Carrier),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' = I f →
      ∫ q, (φ q : ℝ) ∂μ' = (I f).toReal := by
    intro μ' h'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h']
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key _ (h₁ f hf0), key _ (h₂ f hf0)]

end Extension

section Tower

/-- **First-block slice tower.** For compatible measures and every determinant order `k`,
the density `q^(-k b)` times the first-block slice-`k` kernel composed with the zero slice
of the lower mixed quotient measure is the slice `k` of the lower quotient measure. -/
theorem firstBlockKernel_comp_zeroSlice
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (νL : Measure (LowerMixedQuotient F h))
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (νMinus : Measure (LowerQuotient h F.Carrier))
    (hνMinus : IsCompatible (lowerBlockUnipotent h F.Carrier) (generalLinearHaar F.Carrier t)
      (lowerHaar F h) νMinus)
    (k : ℤ) :
    ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) •
      (firstBlockKernel F h νA hInv k ∘ₘ
        νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)) =
      νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k) := by
  obtain ⟨z, hz⟩ := TwoBlockFirstBlockQuotient.exists_determinantOrder F (m 0) k
  refine eq_of_lintegral_lowerQuotientAverageReal F h _ _
    (fun f => ∫⁻ x, ENNReal.ofReal ((ambientSlice F (t + 1) k).indicator f x)
      ∂generalLinearHaar F.Carrier t)
    (fun f hf0 => ?_) (fun f hf0 => ?_) (fun f hf0 => ?_)
  · -- Finiteness of the common value.
    calc _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂generalLinearHaar F.Carrier t :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            (Set.indicator_le_self' (fun x _ => hf0 x) x)
      _ < ⊤ := (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  · -- The tower side: unfold, cut by `G^0`, apply compatibility of `νL`, translate by `I(z)`.
    have hfzc : Continuous (fun x => f (firstBlockEmbedding h F.Carrier z * x)) :=
      f.continuous.comp (continuous_const.mul continuous_id)
    have hfzs : HasCompactSupport (fun x => f (firstBlockEmbedding h F.Carrier z * x)) :=
      f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft _)
    have hpt : ∀ q : LowerMixedQuotient F h,
        (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0).indicator
          (fun q => ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h)
            (lowerMixedHaar F h) (fun x => f (firstBlockEmbedding h F.Carrier z * x)) q)) q =
        ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h)
          ((ambientSlice F (t + 1) 0).indicator
            (fun x => f (firstBlockEmbedding h F.Carrier z * x))) q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [quotientAverageReal_indicator_ambientSlice F (lowerMixedSubgroup F h)
          (lowerMixedSubgroup_le_normOneSubgroup F h)]
        by_cases hg : g ∈ ambientSlice F (t + 1) 0
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show (Quotient.mk _ g :
            LowerMixedQuotient F h) ∈ TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
              from hg)]
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show (Quotient.mk _ g :
            LowerMixedQuotient F h) ∉ TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
              from hg), ENNReal.ofReal_zero]
    have hshift : ∀ x, (ambientSlice F (t + 1) 0).indicator
        (fun x => f (firstBlockEmbedding h F.Carrier z * x)) x =
        (ambientSlice F (t + 1) k).indicator f (firstBlockEmbedding h F.Carrier z * x) := by
      intro x
      have hmem : firstBlockEmbedding h F.Carrier z * x ∈ ambientSlice F (t + 1) k ↔
          x ∈ ambientSlice F (t + 1) 0 := by
        change F.canonicalTopologicalData.ord (GeneralLinear.determinant
            (firstBlockEmbedding h F.Carrier z * x) : F.Carrier) = k ↔
          F.canonicalTopologicalData.ord (GeneralLinear.determinant x : F.Carrier) = 0
        rw [map_mul, Units.val_mul, F.canonicalTopologicalData.ord_mul
          (GeneralLinear.determinant (firstBlockEmbedding h F.Carrier z)).ne_zero
          (GeneralLinear.determinant x).ne_zero, determinant_firstBlockEmbedding, hz,
          add_eq_left]
      by_cases hx : x ∈ ambientSlice F (t + 1) 0
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.1 h'))]
    rw [lintegral_smul_measure, smul_eq_mul,
      lintegral_firstBlockKernel_comp_quotientAverageReal F h νA hInv hνA _ f hf0 k z hz,
      ← lintegral_indicator (TwoBlockLowerFirstBlockQuotient.measurableSet_determinantSlice F h 0)]
    refine (lintegral_congr hpt).trans ?_
    rw [RecursiveIntegration.lintegral_quotientAverageReal _ _ _ νL hνL _
      ((isClopen_ambientSlice F (t + 1) 0).continuous_indicator hfzc)
      (hfzs.mono fun x hx h0 => hx (Set.indicator_apply_eq_zero.mpr fun _ => h0))
      (fun x => Set.indicator_nonneg (fun y _ => hf0 _) x)]
    refine (lintegral_congr fun x => by rw [hshift x]).trans ?_
    exact lintegral_mul_left_eq_self
      (fun x => ENNReal.ofReal ((ambientSlice F (t + 1) k).indicator f x))
      (firstBlockEmbedding h F.Carrier z)
  · -- The lower quotient side: cut by `G^k` and apply compatibility of `νMinus`.
    have hpt : ∀ q : LowerQuotient h F.Carrier,
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h k).indicator
          (fun q => ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier)
            (lowerHaar F h) f q)) q =
        ENNReal.ofReal (quotientAverageReal (lowerBlockUnipotent h F.Carrier) (lowerHaar F h)
          ((ambientSlice F (t + 1) k).indicator f) q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [quotientAverageReal_indicator_ambientSlice F (lowerBlockUnipotent h F.Carrier)
          ((lowerBlockUnipotent_le_lowerMixedSubgroup F h).trans
            (lowerMixedSubgroup_le_normOneSubgroup F h))]
        have hmem : (Quotient.mk _ g : LowerQuotient h F.Carrier) ∈
            TwoBlockLowerUnipotentQuotient.determinantSlice F h k ↔
              g ∈ ambientSlice F (t + 1) k :=
          TwoBlockLowerUnipotentQuotient.mk_mem_determinantSlice F h
        by_cases hg : g ∈ ambientSlice F (t + 1) k
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h' => hg (hmem.1 h')),
            ENNReal.ofReal_zero]
    rw [← lintegral_indicator (TwoBlockLowerUnipotentQuotient.measurableSet_determinantSlice F h k)]
    refine (lintegral_congr hpt).trans ?_
    exact RecursiveIntegration.lintegral_quotientAverageReal _ _ _ νMinus hνMinus _
      ((isClopen_ambientSlice F (t + 1) k).continuous_indicator f.continuous)
      (f.hasCompactSupport.mono fun x hx h0 =>
        hx (Set.indicator_apply_eq_zero.mpr fun _ => h0))
      (fun x => Set.indicator_nonneg (fun y _ => hf0 y) x)

/-- The first-block slice tower for `F` and the shape `h`: for every s-finite, norm-one
right-invariant small quotient measure `νA` compatible with the Haar measures of `GL_a` and
`N_a`, every lower mixed quotient measure `νL` compatible with the Haar of `G` and the fixed
lower mixed Haar, every lower quotient measure `νMinus` compatible with the Haar of `G` and
the prescribed lower-unipotent Haar, and every determinant order `k`, the density
`q^(-k b)` times the first-block slice-`k` kernel composed with the zero slice of `νL` is the
slice `k` of `νMinus`. -/
def FirstBlockSliceTowerStatement : Prop :=
  ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA),
    IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA →
    ∀ νL : Measure (LowerMixedQuotient F h),
    IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL →
    ∀ νMinus : Measure (LowerQuotient h F.Carrier),
    IsCompatible (lowerBlockUnipotent h F.Carrier) (generalLinearHaar F.Carrier t)
      (lowerHaar F h) νMinus →
    ∀ k : ℤ,
    ENNReal.ofReal ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-(k * ((m 1 + 1 : ℕ) : ℤ)))) •
      (firstBlockKernel F h νA hInv k ∘ₘ
        νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)) =
      νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)

theorem firstBlockSliceTower : FirstBlockSliceTowerStatement F h :=
  fun νA _ hInv hνA νL hνL νMinus hνMinus k =>
    firstBlockKernel_comp_zeroSlice F h νA hInv hνA νL hνL νMinus hνMinus k

end Tower

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
