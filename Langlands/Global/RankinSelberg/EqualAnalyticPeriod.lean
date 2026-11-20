import Langlands.Global.RankinSelberg.EqualAnalyticResidue
import Langlands.Global.RankinSelberg.EqualUnfoldingCusp
import Langlands.Automorphic.CuspidalInvariantPairingCriterion

/-! # The equal-rank cuspidal residue period -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Automorphic ContinuousRationalFunctions OperatorDeterminantSlice
open NumberField MeasureTheory Filter Set
open scoped CategoryTheory.MonObj NNReal _root_.Topology

local instance slabSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance slabSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "Q" => OperatorDeterminantSlice.Quotient F n
local notation "slab" => determinantSlab F n 1 (Real.exp n)

/-- Quotient Haar measure on the determinant slab of the residue period. -/
abbrev residueSlabMeasure : Measure Q := (quotientHaarMeasure F n).restrict slab

private theorem mem_slab_point_iff (x : AdelicGL F n) :
    point F n x ∈ slab ↔ 1 ≤ absDet F n x ∧ absDet F n x < Real.exp n := by
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  change e.symm x ∈ LeftCosetSpace.mk (glRational F n) ⁻¹' slab ↔ _
  rw [preimage_determinantSlab]
  change (1 ≤ detNorm F n (e.symm x) ∧ detNorm F n (e.symm x) < Real.exp n) ↔ _
  change (1 ≤ absDet F n (e (e.symm x)) ∧ absDet F n (e (e.symm x)) < Real.exp n) ↔ _
  rw [e.apply_symm_apply]

private theorem translate_slab_preserving (a : AdelicGL F n) (ha : absDet F n a = 1) :
    MeasurePreserving (translate F n a) (residueSlabMeasure F n) (residueSlabMeasure F n) := by
  have hpre : translate F n a ⁻¹' slab = slab := by
    ext q
    obtain ⟨x, rfl⟩ := point_surjective F n q
    simp only [Set.mem_preimage, translate_point, mem_slab_point_iff, absDet_mul, ha, mul_one]
  simpa only [residueSlabMeasure, hpre] using
    (measurePreserving_translate F n a).restrict_preimage (measurableSet_determinantSlab F n)

section SquareIntegrability

variable [CompactSpace (AdeleQuotient F)]

/-- The uniform bound on the translates of a cuspidal vector along the Lie curve is
square integrable on the residue slab. -/
theorem memLp_supNorm_residueSlab (S : OperatorRealization F n) (hS : S.IsCuspidal)
    (X : ArchimedeanGL.RealLieAlgebra F n) (h : S.Space) :
    MemLp (supNorm F n S X h) 2 (residueSlabMeasure F n) := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfin⟩ := S.exists_band_cover_uniform hS (lo := 1) (hi := Real.exp n)
    one_pos (curve F n X '' Icc (-1) 1) (isCompact_Icc.image (continuous_curve F n X))
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let φ := supNorm F n S X h
  have hφ : Continuous φ := continuous_supNorm F n S X h
  have hcov (g : Points F n) (hg : LeftCosetSpace.mk (glRational F n) g ∈ slab) :
      ∃ c : glRational F n, (c : Points F n) * g ∈ e ⁻¹' t := by
    rw [← point_adelicHomeomorph F n g, mem_slab_point_iff] at hg
    obtain ⟨c, hc⟩ := hcover (e g) hg.1 hg.2.le
    let b := (GeneralLinearGroupPoints.rationalEquiv F n).symm c
    refine ⟨⟨AdelicGroupPoints.rational F (Scheme F n) b, ⟨b, rfl⟩⟩, ?_⟩
    change e (AdelicGroupPoints.rational F (Scheme F n) b * g) ∈ t
    simpa only [e, b, map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      MulEquiv.apply_symm_apply] using hc
  have hle := LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le (glRational F n)
    (isDiscrete_glRational F n) Measure.haar slab (measurableSet_determinantSlab F n) (e ⁻¹' t)
    (ht.preimage e.continuous.measurable) hcov (fun q => ‖φ q‖ₑ ^ 2)
      (hφ.measurable.enorm.pow_const 2)
  have hchange : (∫⁻ g in e ⁻¹' t, ‖φ (LeftCosetSpace.mk (glRational F n) g)‖ₑ ^ 2
      ∂(Measure.haar : Measure (Points F n))) =
      ∫⁻ x in t, ‖φ (point F n x)‖ₑ ^ 2 ∂matrixHaarMeasure F n := by
    rw [matrixHaarMeasure, setLIntegral_map (f := fun x => ‖φ (point F n x)‖ₑ ^ 2)
      (g := ⇑(GeneralLinearGroupPoints.adelicHomeomorph F n)) ht
      ((hφ.comp (continuous_point F n)).measurable.enorm.pow_const 2)
      (map_continuous (GeneralLinearGroupPoints.adelicHomeomorph F n)).measurable]
    exact lintegral_congr fun g => by rw [point_adelicHomeomorph]
  have hfin' := hfin (matrixHaarMeasure F n) h (fun x => ‖φ (point F n x)‖ₑ) (fun x => by
    obtain ⟨s, hs, heq⟩ := exists_supNorm_eq F n S X h x
    refine ⟨curve F n X s, Set.mem_image_of_mem _ hs, ?_⟩
    dsimp only [φ]
    rw [heq, enorm_norm])
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    hφ.aestronglyMeasurable).mpr
  simpa only [residueSlabMeasure, quotientHaarMeasure,
    AdelicGroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (hle.trans_eq hchange).trans_lt hfin'

private theorem memLp_toQuotient_residueSlab (S : OperatorRealization F n) (hS : S.IsCuspidal)
    (f : S.Space) : MemLp (toQuotient F n S f) 2 (residueSlabMeasure F n) := by
  apply (memLp_supNorm_residueSlab F n S hS 0 f).mono' (toQuotient F n S f).continuous.aestronglyMeasurable
  filter_upwards [] with q
  simpa only [curve_zero, translate_one] using
    norm_le_supNorm F n S 0 f q (s := 0) ⟨by norm_num, by norm_num⟩

variable {S T : OperatorRealization F n}

private theorem integrable_toQuotient_mul (hS : S.IsCuspidal) (hT : T.IsCuspidal)
    (f : S.Space) (g : T.Space) :
    Integrable (fun q => toQuotient F n S f q * toQuotient F n T g q) (residueSlabMeasure F n) :=
  (memLp_toQuotient_residueSlab F n S hS f).integrable_mul
    (memLp_toQuotient_residueSlab F n T hT g)

/-- The bilinear integral of two realized cusp forms on the residue slab. -/
def residuePairing (hS : S.IsCuspidal) (hT : T.IsCuspidal) :
    S.Space →ₗ[ℂ] T.Space →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun g => ∫ q, toQuotient F n S f q * toQuotient F n T g q ∂residueSlabMeasure F n
      map_add' := fun g g' => by
        simp only [map_add, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_toQuotient_mul F n hS hT f g)
          (integrable_toQuotient_mul F n hS hT f g')
      map_smul' := fun c g => by
        simp only [map_smul, ContinuousMap.smul_apply, mul_smul_comm, integral_smul,
          RingHom.id_apply] }
  map_add' f f' := by
    ext g
    change (∫ q, toQuotient F n S (f + f') q * toQuotient F n T g q ∂residueSlabMeasure F n) = _
    simp only [map_add, ContinuousMap.add_apply, add_mul, LinearMap.add_apply]
    exact integral_add (integrable_toQuotient_mul F n hS hT f g)
      (integrable_toQuotient_mul F n hS hT f' g)
  map_smul' c f := by
    ext g
    change (∫ q, toQuotient F n S (c • f) q * toQuotient F n T g q ∂residueSlabMeasure F n) = _
    simp only [map_smul, ContinuousMap.smul_apply, smul_mul_assoc, integral_smul, LinearMap.smul_apply,
      RingHom.id_apply]
    rfl

omit [CompactSpace (AdeleQuotient F)] in
private theorem ideleOf_surjective : Function.Surjective (ideleOf F) := by
  intro z
  let e := GeneralLinearGroupPoints.adelicHomeomorph F 1
  refine ⟨e.symm (AdelicGL.scalar F 1 z), ?_⟩
  change AdelicGL.determinant F 1 (e (e.symm (AdelicGL.scalar F 1 z))) = z
  simp only [e.apply_symm_apply, AdelicGL.determinant_scalar, pow_one]

omit [CompactSpace (AdeleQuotient F)] in
private theorem integral_product_translate (hn : n ≠ 0)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hω : S.HasCentralCharacter ω) (hω' : T.HasCentralCharacter ω')
    (htriv : ∀ z, ideleChar F (ω * ω') z = 1)
    (a : AdelicGL F n) (f : S.Space) (g : T.Space) :
    ∫ q, toQuotient F n S f (translate F n a q) *
        toQuotient F n T g (translate F n a q) ∂residueSlabMeasure F n =
      ∫ q, toQuotient F n S f q * toQuotient F n T g q ∂residueSlabMeasure F n := by
  obtain ⟨z, hz⟩ := exists_normalized_rightTranslate F n hn a
  let b := AdelicGL.scalar F n z * a
  have hb : absDet F n b = 1 := congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hz
  have hprod : (centralIdeleCharacter F ω z : ℂ) * (centralIdeleCharacter F ω' z : ℂ) = 1 := by
    obtain ⟨w, hw⟩ := ideleOf_surjective F z
    rw [← EqualUnfolding.centralIdeleCharacter_mul_val]
    simpa only [ideleChar, hw] using htriv w
  calc
    _ = ∫ q, toQuotient F n S f (translate F n b q) *
        toQuotient F n T g (translate F n b q) ∂residueSlabMeasure F n := by
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [b]
      rw [toQuotient_central F n S ω hω, toQuotient_central F n T ω' hω',
        mul_mul_mul_comm, hprod, one_mul]
    _ = _ := (translate_slab_preserving F n b hb).integral_comp
      (translate F n b).toMeasurableEquiv.measurableEmbedding
      (fun q => toQuotient F n S f q * toQuotient F n T g q)

omit [CompactSpace (AdeleQuotient F)] in
private theorem hasDerivAt_toQuotient_curve (R : OperatorRealization F n)
    (X : ArchimedeanGL.RealLieAlgebra F n) (f : R.Space) (q : Q) (s : ℝ) :
    HasDerivAt (fun t => toQuotient F n R f (translate F n (curve F n X t) q))
      (toQuotient F n R (R.lieAction X f) (translate F n (curve F n X s) q)) s := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  simp only [translate_point, toQuotient_point]
  exact R.hasDerivAt_evaluate_oneParameter X f x s

private theorem residuePairing_lie_add (hn : n ≠ 0)
    (hS : S.IsCuspidal) (hT : T.IsCuspidal)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hω : S.HasCentralCharacter ω) (hω' : T.HasCentralCharacter ω')
    (htriv : ∀ z, ideleChar F (ω * ω') z = 1)
    (X : ArchimedeanGL.RealLieAlgebra F n) (f : S.Space) (g : T.Space) :
    residuePairing F n hS hT (S.lieAction X f) g +
      residuePairing F n hS hT f (T.lieAction X g) = 0 := by
  let c := curve F n X
  let G (s : ℝ) (q : Q) := toQuotient F n S f (translate F n (c s) q) *
    toQuotient F n T g (translate F n (c s) q)
  let D (s : ℝ) (q : Q) :=
    toQuotient F n S (S.lieAction X f) (translate F n (c s) q) *
      toQuotient F n T g (translate F n (c s) q) +
    toQuotient F n S f (translate F n (c s) q) *
      toQuotient F n T (T.lieAction X g) (translate F n (c s) q)
  have hderiv (q : Q) (s : ℝ) : HasDerivAt (fun t => G t q) (D s q) s :=
    (hasDerivAt_toQuotient_curve F n S X f q s).mul
      (hasDerivAt_toQuotient_curve F n T X g q s)
  have hzero (q : Q) : translate F n (c 0) q = q := by
    rw [show c = curve F n X from rfl, curve_zero, translate_one]
  have hG : G 0 = fun q => toQuotient F n S f q * toQuotient F n T g q :=
    funext fun q => by simp only [G, hzero]
  have hD : D 0 = fun q =>
      toQuotient F n S (S.lieAction X f) q * toQuotient F n T g q +
        toQuotient F n S f q * toQuotient F n T (T.lieAction X g) q :=
    funext fun q => by simp only [D, hzero]
  have hGint : Integrable (G 0) (residueSlabMeasure F n) :=
    hG ▸ integrable_toQuotient_mul F n hS hT f g
  have hleft := integrable_toQuotient_mul F n hS hT (S.lieAction X f) g
  have hright := integrable_toQuotient_mul F n hS hT f (T.lieAction X g)
  have hDint : Integrable (D 0) (residueSlabMeasure F n) := hD ▸ hleft.add hright
  let bound (q : Q) := supNorm F n S X (S.lieAction X f) q * supNorm F n T X g q +
    supNorm F n S X f q * supNorm F n T X (T.lieAction X g) q
  have hbound (q : Q) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) : ‖D s q‖ ≤ bound q := by
    have hs' := Ioo_subset_Icc_self hs
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (norm_le_supNorm F n S X _ q hs') (norm_le_supNorm F n T X _ q hs')
        (norm_nonneg _) (supNorm_nonneg F n S X _ q)
    · rw [norm_mul]
      exact mul_le_mul (norm_le_supNorm F n S X _ q hs') (norm_le_supNorm F n T X _ q hs')
        (norm_nonneg _) (supNorm_nonneg F n S X _ q)
  have hboundInt : Integrable bound (residueSlabMeasure F n) :=
    ((memLp_supNorm_residueSlab F n S hS X _).integrable_mul
      (memLp_supNorm_residueSlab F n T hT X g)).add
      ((memLp_supNorm_residueSlab F n S hS X f).integrable_mul
        (memLp_supNorm_residueSlab F n T hT X _))
  have hcont (s : ℝ) : Continuous (G s) :=
    ((toQuotient F n S f).continuous.comp (translate F n (c s)).continuous).mul
      ((toQuotient F n T g).continuous.comp (translate F n (c s)).continuous)
  have hJ := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := G) (F' := D)
    (x₀ := (0 : ℝ)) (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable) hGint
    hDint.aestronglyMeasurable (ae_of_all _ hbound) hboundInt
    (ae_of_all _ fun q s _ => hderiv q s)).2
  have hconst : (fun s => ∫ q, G s q ∂residueSlabMeasure F n) =
      fun _ => residuePairing F n hS hT f g :=
    funext fun s => integral_product_translate F n hn hω hω' htriv (c s) f g
  rw [hconst] at hJ
  have heq := hJ.unique (hasDerivAt_const _ _)
  rw [hD, integral_add hleft hright] at heq
  exact heq

/-- Triviality of the product central character makes the residue period invariant under
both translation actions and every real Lie direction. -/
theorem residuePairing_invariant (hn : n ≠ 0) (hS : S.IsCuspidal) (hT : T.IsCuspidal)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hω : S.HasCentralCharacter ω) (hω' : T.HasCentralCharacter ω')
    (htriv : ∀ z, ideleChar F (ω * ω') z = 1) :
    S.IsInvariantPairing T (residuePairing F n hS hT) := by
  refine ⟨?_, ?_, residuePairing_lie_add F n hn hS hT hω hω' htriv⟩
  · intro d f g
    change (∫ q, toQuotient F n S (S.finiteRepresentation d f) q *
        toQuotient F n T (T.finiteRepresentation d g) q ∂residueSlabMeasure F n) = _
    simp only [toQuotient_finite]
    exact integral_product_translate F n hn hω hω' htriv _ f g
  · intro k f g
    change (∫ q, toQuotient F n S (S.compactRepresentation k f) q *
        toQuotient F n T (T.compactRepresentation k g) q ∂residueSlabMeasure F n) = _
    simp only [toQuotient_compact]
    exact integral_product_translate F n hn hω hω' htriv _ f g

end SquareIntegrability

section Cuspidal

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- This pairing is the exponent-zero period of the global equal-rank theta splitting. -/
theorem residuePairing_eq_residueConstant (S T : CuspidalOperatorRealization F r)
    (f : S.Space) (g : T.Space) :
    residuePairing F (r + 1) S.cuspidal T.cuspidal f g =
      residueConstant F r (fun x => cuspFunction F S f x * cuspFunction F T g x) 0 := by
  let H (q : OperatorDeterminantSlice.Quotient F (r + 1)) :=
    toQuotient F (r + 1) S.realization f q * toQuotient F (r + 1) T.realization g q
  have hH : Continuous H :=
    (toQuotient F (r + 1) S.realization f).continuous.mul
      (toQuotient F (r + 1) T.realization g).continuous
  change (∫ q, H q ∂residueSlabMeasure F (r + 1)) = _
  rw [residueSlabMeasure, quotientHaarMeasure, restrict_determinantSlab,
    integral_map (LeftCosetSpace.measurable_mk _).aemeasurable hH.aestronglyMeasurable]
  simp only [residueConstant, zero_div, neg_zero, zero_mul, Complex.exp_zero, mul_one,
    H, toQuotient_mk, EqualUnfolding.cuspFunction_eq_evaluate]

/-- A nonzero equal-rank residue period for a trivial product central character
forces the first cuspidal realization to be the contragredient of the second. -/
theorem isContragredientOf_of_residueConstant_ne_zero (T T' : CuspidalOperatorRealization F r)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω')
    (htriv : ∀ z, ideleChar F (ω * ω') z = 1) (v : T.Space) (v' : T'.Space)
    (hres : residueConstant F r (fun x => cuspFunction F T v x * cuspFunction F T' v' x) 0 ≠ 0) :
    T.realization.IsContragredientOf T'.realization := by
  let B := residuePairing F (r + 1) T'.cuspidal T.cuspidal
  have htriv' : ∀ z, ideleChar F (ω' * ω) z = 1 := fun z => by
    rw [mul_comm ω' ω, htriv]
  have hB : T'.realization.IsInvariantPairing T.realization B :=
    residuePairing_invariant F (r + 1) (Nat.succ_ne_zero r) T'.cuspidal T.cuspidal hω' hω htriv'
  apply CuspidalOperatorRealization.isContragredientOf_of_nonzero_invariant hB
  intro hB0
  apply hres
  have heq : B v' v = 0 := by rw [hB0, LinearMap.zero_apply, LinearMap.zero_apply]
  simpa only [B, residuePairing_eq_residueConstant, mul_comm (cuspFunction F T' v' _)] using heq

end Cuspidal

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
