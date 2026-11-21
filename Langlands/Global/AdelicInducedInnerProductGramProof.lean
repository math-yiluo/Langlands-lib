import Langlands.Global.AdelicInducedInnerProductGramStatement
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.AdelicSquareIntegrableInducedSubmodule
import Langlands.Global.AdelicInducedL2Inner
import Langlands.Global.AdelicWeylParameterEquivalence

/-! # Positivity of the adelic induced inner product in Gram form -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Topology
open scoped CategoryTheory.MonObj TensorProduct ComplexOrder NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InducedInnerProductSesquilinear PositiveRealTorus RestrictionSplitCentre

section Coordinates

variable {F : Type} [Field F]
  {P M : GroupScheme (Spec (CommRingCat.of F))}
  {l : M ⟶ P} {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)

/-- Each tuple of coordinates is realized by an additive real functional on the characters. -/
private theorem coordinateMap_surjective : Function.Surjective (coordinateMap e) := by
  intro y
  let b := (Pi.basisFun ℝ (Fin n)).map e
  let L : RealCharacterParameter F P →ₗ[ℝ] ℝ := b.constr ℝ y
  let H : RealCharacterDual F P :=
    { toFun := fun χ => L ((1 : ℝ) ⊗ₜ[ℤ] χ)
      map_zero' := by simp
      map_add' χ ψ := by simp only [tmul_add, map_add] }
  have hL : (realParameterPairing F P).flip H = L := by
    apply AlgebraTensorModule.ext
    intro s χ
    rw [LinearMap.flip_apply, realParameterPairing_tmul]
    change s * L ((1 : ℝ) ⊗ₜ[ℤ] χ) = L (s ⊗ₜ[ℤ] χ)
    rw [← smul_eq_mul, ← map_smul, smul_tmul', smul_eq_mul, mul_one]
  refine ⟨H, funext fun j => ?_⟩
  change (realParameterPairing F P).flip H (e (Pi.single j 1)) = y j
  rw [hL]
  simpa only [b, Module.Basis.map_apply, Pi.basisFun_apply] using b.constr_basis ℝ y j

private theorem leviDualMap_surjective (hl : IsRationalLeviSubgroup l) :
    Function.Surjective (realCharacterDualMap F M P l) := by
  let r := AddEquiv.ofBijective (characterRestrict l) hl.characterRestrict_bijective
  intro H
  refine ⟨H.comp r.symm.toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro χ
  change H (r.symm (r χ)) = H χ
  rw [r.symm_apply_apply]

variable [NumberField F] [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The signed weight has a positive integral on the actual positive factor. -/
private theorem integral_positive_weight_pos (hl : IsRationalLeviSubgroup l) (hc : IsCentral i)
    {β : (Fin n → ℝ) → ℝ} (hβint : ∫ y, β y = 1) :
    0 < ∫ a : intrinsicSubgroup F T, β (InducedInnerProductIntegrable.positiveCoordinates i e l a)
      ∂normalizedPositiveHaarMeasure F M T i hi I e₀ hc := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  let L : (I → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofBijective (torusCoordinateMap l e T i I e₀)
      ⟨torusCoordinateMap_injective l e T i hi I e₀ hπ,
        (coordinateMap_surjective e).comp ((leviDualMap_surjective hl).comp
          ((realCharacterDualRestrictionEquiv F M T.toGrp i hi).surjective.comp
            (dualCoordinatesContinuousEquiv F T I e₀).symm.surjective))⟩).toContinuousLinearEquiv
  let h := (positiveCoordinates T I e₀).trans L.toHomeomorph
  have hcoord (a : intrinsicSubgroup F T) :
      h a = InducedInnerProductIntegrable.positiveCoordinates i e l a :=
    (parameterCoordinates_positivePointMap l e T i I e₀ a).symm
  let := positiveIsTopologicalGroup F T I e₀
  let ν := normalizedPositiveHaarMeasure F M T i hi I e₀ hc
  let : ν.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e₀ hc
  let νE := Measure.map h ν
  let : νE.IsAddHaarMeasure :=
    { map_add_left_eq_self := by
        intro y
        obtain ⟨a, rfl⟩ := h.surjective y
        have h_translate : (h a + ·) ∘ h = h ∘ (a * ·) := by
          funext b
          simp only [Function.comp_apply, hcoord,
            InducedInnerProductIntegrable.positiveCoordinates_mul]
        have h_add : Measurable (h a + ·) := (continuous_const.add continuous_id).measurable
        have h_mul : Measurable (a * ·) := (continuous_const.mul continuous_id).measurable
        change Measure.map (h a + ·) (Measure.map h ν) = Measure.map h ν
        rw [Measure.map_map h_add h.continuous.measurable, h_translate,
          ← Measure.map_map h.continuous.measurable h_mul, map_mul_left_eq_self ν a]
      lt_top_of_isCompact := by
        intro s hs
        change Measure.map h ν s < ⊤
        rw [← hs.measure_closure, Measure.map_apply h.continuous.measurable
          isClosed_closure.measurableSet]
        exact (h.isCompact_preimage.mpr hs.closure).measure_lt_top
      toIsOpenPosMeasure := h.continuous.isOpenPosMeasure_map h.surjective }
  let c := Measure.addHaarScalarFactor νE volume
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hνE : νE = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  have hEq : (∫ a : intrinsicSubgroup F T, β (h a) ∂ν) = (c : ℝ) := by
    calc
      _ = ∫ y, β y ∂νE := (integral_map_equiv h.toMeasurableEquiv β).symm
      _ = (c : ℝ) := by
        rw [hνE, integral_smul_nnreal_measure, hβint, NNReal.smul_def, smul_eq_mul, mul_one]
  rw [← show ν = normalizedPositiveHaarMeasure F M T i hi I e₀ hc from rfl]
  simp_rw [← hcoord, hEq]
  exact_mod_cast hcpos

end Coordinates

section QuotientIntegrals

variable {F : Type} [Field F] [NumberField F] {M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The signed integral factors on the product fundamental domain `A × D¹`. -/
private theorem integral_rationalQuotient_haar (hc : IsCentral i)
    (f : AdelicGroupPoints F M → ℝ) (b : intrinsicSubgroup F T → ℝ)
    (w : normOneSubgroup F M → ℝ)
    (hf : ∀ a (n : normOneSubgroup F M), f (positivePointMap F M T i a * n) = b a * w n)
    (hfinv : ∀ g ∈ AdelicGroupPoints.rationalSubgroup F M, ∀ m, f (g * m) = f m)
    (hfmeas : Measurable (fun x : RationalQuotient F M => f x.out)) :
    ∫ x : RationalQuotient F M, f x.out
        ∂(LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) Measure.haar) =
      (∫ a, b a ∂normalizedPositiveHaarMeasure F M T i hi I e₀ hc) *
        ∫ n : normOneSubgroup F M in normOneDomain (M := M), w n ∂Measure.haar := by
  let := normalizedPositiveHaarMeasure_sigmaFinite F M T i hi I e₀ hc
  rw [LeftCosetSpace.discreteQuotientMeasure_eq _ _ _
      (isFundamentalDomain_productDomain T i hi I e₀ hc _),
    LeftCosetSpace.quotientMeasure,
    integral_map (LeftCosetSpace.measurable_mk _).aemeasurable hfmeas.aestronglyMeasurable]
  have hout := out_mk_apply (AdelicGroupPoints.rationalSubgroup F M) f hfinv
  simp_rw [hout]
  rw [← (measurePreserving_normOneDecomposition F M T i hi I e₀ hc).setIntegral_preimage_emb
    (normOneDecomposition F M T i hi I e₀).measurableEmbedding f]
  have hpre : (normOneDecomposition F M T i hi I e₀) ⁻¹' productDomain T i hi I e₀ =
      Set.univ ×ˢ normOneDomain (M := M) := by
    ext q
    simp only [Set.mem_preimage, productDomain, normOneDecomposition_apply,
      normOneFactor_positivePointMap_mul, Set.mem_prod, Set.mem_univ, true_and]
  rw [hpre]
  simp_rw [normOneDecomposition_apply, hf]
  rw [setIntegral_prod_mul, setIntegral_univ]

/-- The signed integral on the canonical quotient is the integral over `D¹`. -/
private theorem integral_canonical (W : AdelicGroupPoints F M → ℝ)
    (hWinv : ∀ g ∈ canonicalRationalSubgroup F M, ∀ m, W (g * m) = W m)
    (hWmeas : Measurable (fun x : CanonicalQuotient F M => W x.out)) :
    ∫ x : CanonicalQuotient F M, W x.out ∂canonicalMeasure F M =
      ∫ n : normOneSubgroup F M in normOneDomain (M := M), W n ∂Measure.haar := by
  unfold canonicalMeasure quotientHaarMeasure
  have hm := measurable_normOneToQuotient F M
    (canonicalRestrictionTorus F M) (canonicalRestrictionComponent F M)
  rw [integral_map hm.aemeasurable hWmeas.aestronglyMeasurable]
  unfold normOneRationalQuotientHaarMeasure LeftCosetSpace.haarQuotientMeasure
    LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
  have hcomp : Measurable (fun y : NormOneRationalQuotient F M =>
      W (normOneToQuotient F M (canonicalRestrictionTorus F M)
        (canonicalRestrictionComponent F M) y).out) := hWmeas.comp hm
  rw [integral_map (LeftCosetSpace.measurable_mk _).aemeasurable
    hcomp.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun n => by
    simp only [normOneToQuotient_mk]
    exact out_mk_apply _ W hWinv n

end QuotientIntegrals

section Diagonal

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  {β : (Fin n → ℝ) → ℝ}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
private theorem kernel_self_eq_ofReal (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) :
    kernel p l e β φ φ g m =
      ((β (parameterCoordinates F P e (characterLog F P (map F M P l m))) *
        normWeight p l φ g m : ℝ) : ℂ) := by
  rw [InducedInnerProductSesquilinear.kernel, weight, normWeight, Complex.ofReal_mul,
    Complex.ofReal_mul, ofReal_norm_parameterPower_neg_modulusParameter,
    mul_assoc, Complex.mul_conj', Complex.ofReal_pow, mul_assoc]

/-- A single positive constant compares the two Levi quotient integrals for every `g`. -/
private theorem exists_integral_rationalQuotient_kernel (hM : IsConnectedReductive M)
    (hl : IsRationalLeviSubgroup l) (hβ : Continuous β) (hβint : ∫ y, β y = 1)
    (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ)
    (hφeq : IsSplitComponentEquivariant p l φ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : AdelicGroupPoints F G,
      (∫ x : RationalQuotient F M, kernel p l e β φ φ g x.out
        ∂(LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) =
        ((c * ∫ x : CanonicalQuotient F M, normWeight p l φ g x.out
          ∂canonicalMeasure F M : ℝ) : ℂ) := by
  have hs := isSplitComponent_canonicalComponent F M
  have hi := canonical_characterRestrict_injective F M centralSplitTorusCharacter hM
  let := canonical_finiteIndex F M hM
  let := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  obtain ⟨I, hI, ⟨e₀⟩⟩ := hs.1.1.1
  let := Fintype.ofFinite I
  have hc : IsCentral (canonicalComponent F M) := hs.1.2
  let b := fun a : intrinsicSubgroup F (canonicalTorus F M) =>
    β (InducedInnerProductIntegrable.positiveCoordinates (canonicalComponent F M) e l a)
  let cA := ∫ a, b a ∂normalizedPositiveHaarMeasure F M (canonicalTorus F M)
    (canonicalComponent F M) hi I e₀ hc
  have hcA : 0 < cA :=
    integral_positive_weight_pos e (canonicalTorus F M) (canonicalComponent F M) hi I e₀ hl hc hβint
  let cM := Measure.haarScalarFactor μM (Measure.haar : Measure (AdelicGroupPoints F M))
  have hcM : 0 < (cM : ℝ) := by
    exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μM
      (Measure.haar : Measure (AdelicGroupPoints F M))
  have hμ : μM = cM • (Measure.haar : Measure (AdelicGroupPoints F M)) :=
    Measure.isMulLeftInvariant_eq_smul μM Measure.haar
  have hν : LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM =
      cM • LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) Measure.haar := by
    rw [hμ]
    unfold LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    rw [Measure.restrict_smul, Measure.map_smul _ (LeftCosetSpace.measurable_mk _).aemeasurable]
  refine ⟨(cM : ℝ) * cA, mul_pos hcM hcA, fun g => ?_⟩
  let W := normWeight p l φ g
  let f := fun m : AdelicGroupPoints F M =>
    β (parameterCoordinates F P e (characterLog F P (map F M P l m))) * W m
  have hker (m : AdelicGroupPoints F M) : kernel p l e β φ φ g m = (f m : ℂ) :=
    kernel_self_eq_ofReal e φ g m
  have hWc : Continuous W := continuous_normWeight p l continuous_const continuous_id hφc
  have hWinv : ∀ x ∈ canonicalRationalSubgroup F M, ∀ m, W (x * m) = W m :=
    fun _ hx m => canonicalRationalSubgroup_le_leftStabilizer hφinv hφeq g hx m
  have hWmeas : Measurable (fun x : CanonicalQuotient F M => W x.out) :=
    (continuous_out (canonicalRationalSubgroup F M) W hWc hWinv).measurable
  have hfc : Continuous f :=
    (hβ.comp ((continuous_parameterCoordinates F P e).comp
      ((continuous_characterLog F P).comp (map F M P l).continuous))).mul hWc
  have hfinv : ∀ x ∈ AdelicGroupPoints.rationalSubgroup F M, ∀ m, f (x * m) = f m := by
    intro x hx m
    apply Complex.ofReal_injective
    rw [← hker, ← hker, kernel_rational_mul e β hφinv hφinv hx]
  have hfmeas : Measurable (fun x : RationalQuotient F M => f x.out) :=
    (continuous_out (AdelicGroupPoints.rationalSubgroup F M) f hfc hfinv).measurable
  have hf (a : intrinsicSubgroup F (canonicalTorus F M)) (m : normOneSubgroup F M) :
      f (positivePointMap F M (canonicalTorus F M) (canonicalComponent F M) a * m) =
        b a * W m := by
    dsimp only [f, W]
    rw [characterLog_map_mul_normOne l m.property,
      normWeight_splitComponent_mul hφeq (mem_canonicalSubgroup_positivePointMap a)]
    rfl
  simp_rw [hker, integral_complex_ofReal]
  apply congrArg Complex.ofReal
  rw [hν, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    integral_rationalQuotient_haar _ _ hi I e₀ hc f b (fun m => W m) hf hfinv hfmeas,
    ← integral_canonical W hWinv hWmeas]
  exact (mul_assoc _ _ _).symm

variable {U : GroupScheme (Spec (CommRingCat.of F))} {iU : U ⟶ P}
  {K : Subgroup (AdelicGroupPoints F G)}
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}

/-- The diagonal is nonnegative, and equality forces the adelic function to vanish. -/
private theorem inducedInnerProduct_self_nonneg_and_eq_zero (hK : IsIwasawaCompact p K)
    (hl : IsRationalLeviSubgroup l) [IsIso (subgroupMultiplication l iU)]
    (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
    (hβ : Continuous β) (hβint : ∫ y, β y = 1)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ) :
    0 ≤ inducedInnerProduct K hK.isCompact p l μM e β φ φ ∧
      (inducedInnerProduct K hK.isCompact p l μM e β φ φ = 0 ↔ φ = 0) := by
  have hM := hl.isConnectedReductive
  have hφc : Continuous φ := hφ.1.2.1.1
  have hφinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) φ :=
    fun x hx g => hφ.1.1 x (Subgroup.mem_sup_right hx) g
  have hWinv (g : AdelicGroupPoints F G) :
      ∀ x ∈ canonicalRationalSubgroup F M, ∀ m, normWeight p l φ g (x * m) = normWeight p l φ g m :=
    fun _ hx m => canonicalRationalSubgroup_le_leftStabilizer hφinv hφ.2.1 g hx m
  obtain ⟨c, hc, hint⟩ :=
    exists_integral_rationalQuotient_kernel e hM hl hβ hβint μM hφc hφinv hφ.2.1
  let μK := compactHaarProbability F G K hK.isCompact
  let ν := μK.prod (canonicalMeasure F M)
  let W : K × CanonicalQuotient F M → ℝ := fun q => normWeight p l φ q.1 q.2.out
  have hWint : Integrable W ν := hφ.2.2
  have hWnonneg : 0 ≤ W := fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have : SFinite (canonicalMeasure F M) := by
    unfold canonicalMeasure quotientHaarMeasure normOneRationalQuotientHaarMeasure
      LeftCosetSpace.haarQuotientMeasure LeftCosetSpace.discreteQuotientMeasure
      LeftCosetSpace.quotientMeasure
    infer_instance
  have hformula : inducedInnerProduct K hK.isCompact p l μM e β φ φ =
      ((c * ∫ q, W q ∂ν : ℝ) : ℂ) := by
    rw [inducedInnerProduct_eq_kernel]
    simp_rw [hint, integral_complex_ofReal, integral_const_mul]
    rw [integral_prod W hWint]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rw [hformula]
    exact Complex.zero_le_real.mpr (mul_nonneg hc.le (integral_nonneg hWnonneg))
  · intro hz
    rw [hformula, Complex.ofReal_eq_zero] at hz
    have hWae : W =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg hWnonneg hWint).mp
        ((mul_eq_zero.mp hz).resolve_left hc.ne')
    have hWc : Continuous W :=
      continuous_prod_out (canonicalRationalSubgroup F M)
        (fun q : K × AdelicGroupPoints F M => normWeight p l φ q.1 q.2)
        (continuous_normWeight p l (ξ := fun q : K × AdelicGroupPoints F M => (q.1 : AdelicGroupPoints F G))
          (τ := Prod.snd) continuous_fst.subtype_val continuous_snd hφc)
        (fun k => hWinv k)
    let := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
    let := canonicalMeasure_isOpenPosMeasure F M centralSplitTorusCharacter hM
    have : ν.IsOpenPosMeasure := by dsimp only [ν, μK]; infer_instance
    have hWzero : W = 0 := Measure.eq_of_ae_eq hWae hWc continuous_const
    have hmk (k : K) (m : AdelicGroupPoints F M) :
        φ (map F P G p (map F M P l m) * k) = 0 := by
      have h := congrFun hWzero (k, LeftCosetSpace.mk (canonicalRationalSubgroup F M) m)
      change normWeight p l φ k (LeftCosetSpace.mk (canonicalRationalSubgroup F M) m).out = 0 at h
      rw [out_mk_apply (canonicalRationalSubgroup F M) (normWeight p l φ k) (hWinv k)] at h
      have hδ : ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
      exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h).resolve_left hδ))
    funext g
    obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
    let m : AdelicGroupPoints F M := leviComponent l iU q⁻¹
    let u : AdelicGroupPoints F U := radicalComponent l iU q⁻¹
    have hq : map F M P l m * map F U P iU u = q⁻¹ :=
      leviComponent_mul_radicalComponent l iU q⁻¹
    have hq' := congrArg Inv.inv hq
    simp only [mul_inv_rev, inv_inv] at hq'
    rw [← map_inv (map F U P iU) u, ← map_inv (map F M P l) m] at hq'
    have hu : map F U G (iU ≫ p) u⁻¹ ∈ parabolicUnipotentImage F p iU := ⟨u⁻¹, rfl⟩
    rw [← hq', map_mul, mul_assoc, ← map_comp_apply p iU,
      hφ.1.1 _ (Subgroup.mem_sup_left hu)]
    exact hmk ⟨k, hk⟩ m⁻¹
  · rintro rfl
    simp [inducedInnerProduct_eq_kernel, InducedInnerProductSesquilinear.kernel]

end Diagonal

/-- Positivity and the exact vanishing criterion for the finite Gram form on `A²_P`. -/
theorem inducedInnerProductGram : InducedInnerProductGramStatement := by
  intro F _ _ G P M U _ _ _ _ _ _ _ p _ iU l _
  let : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  intro _ _ _ hl hmul K hK N d rho hsmooth hcalc μM _ n e β hβ hβc hβint m φ hφ x
  let := hmul
  have hM := hl.isConnectedReductive
  obtain ⟨_, _, π, _, _, hlπ, _⟩ := hl.exists_unipotentRadical_retraction
  let A := squareIntegrableInducedForms p l hK.isCompact rho hsmooth hcalc iU
  let Φ := ∑ i, x i • φ i
  have hΦ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l Φ :=
    A.sum_mem (fun i _ => A.smul_mem (x i) (hφ i))
  have hgram : inducedInnerProduct K hK.isCompact p l μM e β Φ Φ =
      ∑ i, ∑ i', x i * (starRingEnd ℂ) (x i') *
        inducedInnerProduct K hK.isCompact p l μM e β (φ i) (φ i') := by
    let := InducedInnerProductSesquilinear.sFinite_discreteQuotientMeasure μM
    have hΦ_apply : Φ = fun g => ∑ i, x i * φ i g := by
      funext g
      simp only [Φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hΦ_apply, inducedInnerProduct_eq_kernel p l e β K hK.isCompact μM, kernel_sum]
    exact integral_integral_sum_sum
      (fun i i' (k : K) (z : RationalQuotient F M) => kernel p l e β (φ i) (φ i') k z.out)
      (fun i i' => integrable_kernel e K hK.isCompact hM hlπ hβ hβc μM (hφ i) (hφ i'))
      (fun i i' => x i * (starRingEnd ℂ) (x i'))
  rw [← hgram]
  exact inducedInnerProduct_self_nonneg_and_eq_zero e hK hl μM hβ hβint hΦ

end Langlands.Global
