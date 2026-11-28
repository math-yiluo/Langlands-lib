import Langlands.HarmonicAnalysis.Bicharacter.DualMeasure
import Langlands.HarmonicAnalysis.FiniteDimensionalQuotient
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizerPairing
import Mathlib.MeasureTheory.Integral.Prod

/-! # The Fourier transform of the idempotent parabolic constant term -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open Function MeasureTheory
open scoped NNReal

universe u v

section Algebra

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e
local notation "Lower" => offDiagonalCorner F (1 - e)
local notation "Coordinates" => (Levi × Upper) × Lower

private theorem cornerProjection_of_commute (he : IsIdempotentElem e) {a : A}
    (ha : e * a = a * e) : cornerProjection F e a = 0 := by
  rw [cornerProjection_apply, ha, mul_assoc, (idempotent_mul_rules he).2.2.1, mul_zero]

private theorem cornerProjection_cornerProjection (he : IsIdempotentElem e) (a : A) :
    cornerProjection F e (cornerProjection F e a) = cornerProjection F e a := by
  obtain ⟨_, _, _, h₄, h₅, _, _, _⟩ := idempotent_mul_rules he
  simp only [cornerProjection_apply, mul_assoc, h₄, h₅]

private theorem cornerProjection_cornerProjection_compl (he : IsIdempotentElem e) (a : A) :
    cornerProjection F e (cornerProjection F (1 - e) a) = 0 := by
  obtain ⟨_, _, _, _, _, _, h₇, _⟩ := idempotent_mul_rules he
  simp only [cornerProjection_apply, mul_assoc, h₇, zero_mul]

private theorem diagonalProjection_cornerProjection (he : IsIdempotentElem e) (a : A) :
    diagonalProjection F e (cornerProjection F e a) = 0 := by
  obtain ⟨_, h₂, _, _, _, h₆, _, _⟩ := idempotent_mul_rules he
  simp only [diagonalProjection_apply, cornerProjection_apply, mul_assoc, h₂, mul_zero,
    h₆, zero_mul, add_zero]

private theorem diagonalProjection_compl (e a : A) :
    diagonalProjection F (1 - e) a = diagonalProjection F e a := by
  simp only [diagonalProjection_apply, sub_sub_cancel, add_comm]

/-- The direct-sum coordinates given by the diagonal, upper and opposite components. -/
def parabolicFourierCoordinates (he : IsIdempotentElem e) : Coordinates ≃ₗ[F] A where
  toFun p := (p.1.1 : A) + (p.1.2 : A) + (p.2 : A)
  invFun a := ((⟨diagonalProjection F e a,
      (mem_centralizer_singleton_iff F).2 (commute_diagonalProjection he a)⟩,
    ⟨cornerProjection F e a, cornerProjection_mem F e a⟩),
    ⟨cornerProjection F (1 - e) a, cornerProjection_mem F (1 - e) a⟩)
  left_inv := by
    rintro ⟨⟨y, z⟩, w⟩
    obtain ⟨b, hb⟩ := z.property
    obtain ⟨c, hc⟩ := w.property
    have hy := (mem_centralizer_singleton_iff F).1 y.property
    have hy' : (1 - e) * (y : A) = (y : A) * (1 - e) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hy]
    have hdiag : diagonalProjection F e (cornerProjection F (1 - e) c) = 0 := by
      rw [← diagonalProjection_compl F e, diagonalProjection_cornerProjection F he.one_sub]
    have hop : cornerProjection F (1 - e) (cornerProjection F e b) = 0 := by
      simpa only [sub_sub_cancel] using cornerProjection_cornerProjection_compl F he.one_sub b
    refine Prod.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)) (Subtype.ext ?_)
    · change diagonalProjection F e ((y : A) + (z : A) + (w : A)) = _
      rw [map_add, map_add, diagonalProjection_of_commute he hy, ← hb, ← hc,
        diagonalProjection_cornerProjection F he, hdiag, add_zero, add_zero]
    · change cornerProjection F e ((y : A) + (z : A) + (w : A)) = (z : A)
      rw [map_add, map_add, cornerProjection_of_commute F he hy, ← hb, ← hc,
        cornerProjection_cornerProjection F he, cornerProjection_cornerProjection_compl F he,
        zero_add, add_zero]
    · change cornerProjection F (1 - e) ((y : A) + (z : A) + (w : A)) = (w : A)
      rw [map_add, map_add, cornerProjection_of_commute F he.one_sub hy', ← hb, ← hc,
        hop, cornerProjection_cornerProjection F he.one_sub, zero_add, zero_add]
  right_inv a := diagonal_add_corners F e a
  map_add' p q := by
    change (p.1.1 : A) + (q.1.1 : A) + ((p.1.2 : A) + (q.1.2 : A)) +
        ((p.2 : A) + (q.2 : A)) =
      (p.1.1 : A) + (p.1.2 : A) + (p.2 : A) + ((q.1.1 : A) + (q.1.2 : A) + (q.2 : A))
    abel
  map_smul' c p := by
    change c • (p.1.1 : A) + c • (p.1.2 : A) + c • (p.2 : A) =
      c • ((p.1.1 : A) + (p.1.2 : A) + (p.2 : A))
    rw [smul_add, smul_add]

end Algebra

section ConstantTerm

variable (F : Type u) [Field F] [TopologicalSpace F]
  {A : Type v} [Ring A] [Algebra F A] [TopologicalSpace A] [IsModuleTopology F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e
local notation "Lower" => offDiagonalCorner F (1 - e)
local notation "Coordinates" => (Levi × Upper) × Lower

/-- The additive homeomorphism of the block coordinates. -/
def parabolicFourierHomeomorph (he : IsIdempotentElem e) : Coordinates ≃ₜ+ A :=
  haveI : IsModuleTopology F Levi := isModuleTopology_submodule (Levi).toSubmodule
  linearEquivToContinuousAddEquiv (parabolicFourierCoordinates F he)

@[simp] theorem parabolicFourierHomeomorph_apply (he : IsIdempotentElem e) (p : Coordinates) :
    parabolicFourierHomeomorph F he p = (p.1.1 : A) + (p.1.2 : A) + (p.2 : A) := rfl

variable [T2Space A] [MeasurableSpace A]

/-- Restrict a test to the upper triangular subspace and integrate the upper coordinate. -/
def parabolicConstantTerm (he : IsIdempotentElem e) (ν : Measure Upper)
    [IsFiniteMeasureOnCompacts ν] [OpensMeasurableSpace Upper] (f : SchwartzBruhat A) :
    SchwartzBruhat Levi :=
  let E := parabolicFourierHomeomorph F he
  (f.compLeftInverse (fun p : Levi × Upper => E (p, 0)) (Prod.fst ∘ E.symm)
    (E.continuous.comp (continuous_id.prodMk continuous_const))
    (continuous_fst.comp E.symm.continuous)
    (fun p => congrArg Prod.fst (E.symm_apply_apply (p, 0)))).partialIntegral ν

theorem parabolicConstantTerm_apply (he : IsIdempotentElem e) (ν : Measure Upper)
    [IsFiniteMeasureOnCompacts ν] [OpensMeasurableSpace Upper] (f : SchwartzBruhat A)
    (y : Levi) : parabolicConstantTerm F he ν f y = ∫ z : Upper, f ((y : A) + (z : A)) ∂ν := by
  change (∫ z : Upper, f ((y : A) + (z : A) + 0) ∂ν) = _
  simp only [add_zero]

end ConstantTerm

section Fourier

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [TopologicalSpace A]
  [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A] (e : A)

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e
local notation "Lower" => offDiagonalCorner F (1 - e)
local notation "Coordinates" => (Levi × Upper) × Lower

/-- For a fixed ambient and upper-corner Haar measure, the Levi Haar measure can be
normalized so that the parabolic constant term commutes with the Fourier transform. -/
def IdempotentParabolicFourierStatement : Prop :=
  haveI : T2Space A := t2Space_of_finiteDimensional F A
  haveI : IsModuleTopology F Levi := isModuleTopology_submodule (Levi).toSubmodule
  ∀ (he : IsIdempotentElem e) (ψ : UnitaryAdditiveCharacter F)
    (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
    (μ : AdditiveHaarMeasure A) (ν : Measure Upper) [ν.IsAddHaarMeasure],
    let hM := invariantPairing_centralizer he hB
    ∃ μM : AdditiveHaarMeasure Levi, ∀ f : SchwartzBruhat A,
      parabolicConstantTerm F he ν (pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f) =
        pairingFourierSB ψ hM.isSymm hM.nondegenerate μM (parabolicConstantTerm F he ν f)

theorem idempotentParabolicFourier : IdempotentParabolicFourierStatement F e := by
  have : T2Space A := t2Space_of_finiteDimensional F A
  have : IsModuleTopology F Levi := isModuleTopology_submodule (Levi).toSubmodule
  have : IsTopologicalAddGroup A := IsModuleTopology.isTopologicalAddGroup F A
  have : IsTopologicalAddGroup Levi := IsModuleTopology.isTopologicalAddGroup F Levi
  have : IsTopologicalAddGroup Upper := IsModuleTopology.isTopologicalAddGroup F Upper
  have : IsTopologicalAddGroup Lower := IsModuleTopology.isTopologicalAddGroup F Lower
  have : LocallyCompactSpace A := locallyCompactSpace_of_finiteDimensional F A
  have : LocallyCompactSpace Levi := locallyCompactSpace_of_finiteDimensional F Levi
  have : LocallyCompactSpace Upper := locallyCompactSpace_of_finiteDimensional F Upper
  have : LocallyCompactSpace Lower := locallyCompactSpace_of_finiteDimensional F Lower
  have : SecondCountableTopology A := secondCountableTopology_of_finiteDimensional F A
  have : SecondCountableTopology Levi := secondCountableTopology_of_finiteDimensional F Levi
  have : SecondCountableTopology Upper := secondCountableTopology_of_finiteDimensional F Upper
  have : SecondCountableTopology Lower := secondCountableTopology_of_finiteDimensional F Lower
  have : CompactOpenExhaustion Upper := compactOpenExhaustion_of_finiteDimensional F Upper
  have : CompactOpenExhaustion Lower := compactOpenExhaustion_of_finiteDimensional F Lower
  intro he ψ B hB μ ν _
  let β := B.domRestrict₁₂ Upper Lower
  let α : Upper → Lower → ℂ := fun z w => ψ.complex (β z w)
  have hβ := opposite_corner_nondegenerate he hB
  have hα : IsPerfectBicharacter α := isPerfectBicharacter_of_nondegenerate ψ.continuous_complex
    ψ.norm_complex ψ.complex_ne_one β hβ.2 hβ.1
  let ξ := pairingDualMeasure ν α
  have : ξ.IsAddHaarMeasure := isAddHaarMeasure_pairingDualMeasure hα ν
  let E := parabolicFourierHomeomorph F he
  let m : Measure Levi := Measure.addHaar
  have : m.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure Levi).IsAddHaarMeasure
  have : m.Regular := inferInstanceAs (Measure.addHaar : Measure Levi).Regular
  let μ₀ := ((m.prod ν).prod ξ).map E
  have : μ₀.IsAddHaarMeasure := E.isAddHaarMeasure_map _
  let c := Measure.addHaarScalarFactor μ.measure μ₀
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have : (c • m).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul _ hc.ne'
  let μM : AdditiveHaarMeasure Levi := ⟨c • m, inferInstance, inferInstance⟩
  have hμ : μ.measure = ((μM.measure.prod ν).prod ξ).map E := by
    change μ.measure = (((c • m).prod ν).prod ξ).map E
    rw [Measure.prod_smul_left, Measure.prod_smul_left,
      Measure.map_smul (f := (E : Coordinates → A)) _ E.continuous.measurable.aemeasurable]
    exact Measure.isAddLeftInvariant_eq_smul μ.measure μ₀
  refine ⟨μM, fun f => ?_⟩
  ext y
  let fcoord := f.compLeftInverse E E.symm E.continuous E.symm.continuous E.symm_apply_apply
  let fr := fcoord.compLeftInverse Prod.swap Prod.swap continuous_swap continuous_swap Prod.swap_swap
  have hChar : IsLocallyConstant (fun p : Lower × (Levi × Upper) => ψ.complex (B (y : A) p.2.1)) :=
    (isLocallyConstant_of_continuous_addChar ψ.complex ψ.continuous_complex).comp_continuous
      ((continuous_of_linearMap' (B (y : A))).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  let T : SchwartzBruhat (Lower × (Levi × Upper)) :=
    ⟨fun p => ψ.complex (B (y : A) p.2.1) * fr p,
      hChar.comp₂ fr.locallyConstant (· * ·), fr.hasCompactSupport.mul_left⟩
  let W := T.partialIntegral (μM.measure.prod ν)
  have hTransform (z : Upper) :
      pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f ((y : A) + (z : A)) =
        pairingFourierDual ξ α W z := by
    let k : Coordinates → ℂ := fun p => ψ.complex (B ((y : A) + (z : A)) (E p))
    have hk : Continuous k := ψ.continuous_complex.comp
      ((continuous_of_linearMap' (B ((y : A) + (z : A)))).comp E.continuous)
    have hi : Integrable (fun p => k p * fcoord p) ((μM.measure.prod ν).prod ξ) :=
      (hk.mul fcoord.continuous).integrable_of_hasCompactSupport fcoord.hasCompactSupport.mul_left
    rw [pairingFourierSB_apply, hμ]
    change (∫ X : A, ψ.complex (B ((y : A) + (z : A)) X) * f X
      ∂((μM.measure.prod ν).prod ξ).map E.toHomeomorph.toMeasurableEquiv) = _
    rw [integral_map_equiv]
    change (∫ p : Coordinates, k p * fcoord p ∂(μM.measure.prod ν).prod ξ) = _
    rw [integral_prod_symm _ hi, pairingFourierDual_apply]
    apply integral_congr_ae
    filter_upwards [] with w
    rw [SchwartzBruhat.partialIntegral_apply, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    change ψ.complex (B ((y : A) + (z : A)) ((p.1 : A) + (p.2 : A) + (w : A))) *
      fcoord (p, w) = ψ.complex (B (z : A) w) *
        (ψ.complex (B (y : A) p.1) * fcoord (p, w))
    rw [pairing_add_corners he hB, AddChar.map_add_eq_mul, mul_assoc, mul_left_comm]
  rw [parabolicConstantTerm_apply]
  simp_rw [hTransform]
  have hInv := pairingFourier_pairingFourierDual_pairingDualMeasure hα ν W.property (0 : Lower)
  rw [pairingFourier_apply, neg_zero] at hInv
  simp only [hα.flip.map_zero_left, one_mul] at hInv
  rw [hInv, pairingFourierSB_apply]
  have hT₀ : Integrable (fun p : Levi × Upper => T (0, p)) (μM.measure.prod ν) :=
    (T.sliceSnd (0 : Lower)).integrable _
  rw [show W 0 = ∫ p : Levi × Upper, T (0, p) ∂μM.measure.prod ν from
    SchwartzBruhat.partialIntegral_apply T _ _, integral_prod _ hT₀]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [parabolicConstantTerm_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  change ψ.complex (B (y : A) x) * f (E ((x, z), 0)) =
    ψ.complex (B (y : A) x) * f ((x : A) + (z : A))
  simp only [E, parabolicFourierHomeomorph_apply, Submodule.coe_zero, add_zero]

end Fourier

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
