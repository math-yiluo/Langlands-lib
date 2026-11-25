import Langlands.Global.AdelicInducedInnerProductGramStatement
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.AdelicInducedL2Inner
import Langlands.Automorphic.OperatorDeterminantSliceMeasure
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Proof of `InducedInnerProductGramStatement`

Positive definiteness of the inner product `(·,·)_P` of Lapid 2011, §2 (p.311), on finite
families in `A^2_P`, in the Iwasawa form `inducedInnerProduct`.

For `Φ = ∑ i, x i • φ i` the Gram sum is `∫_K ∫_{M(F) \ M(𝔸)} β(y(m)) δ_P(m)⁻¹ |Φ(m k)|²`
(sesquilinearity, from the integrability results of
`Langlands.Global.InducedInnerProductSesquilinearProof`). Write `M(𝔸) = A × M(𝔸)¹` with `A`
the positive points of the canonical split component and use the fundamental domain `A × D¹`
of `M(F)`. Since `δ_P(n)⁻¹ |Φ(n k)|²` is `A`-invariant, the inner integral is
`c · B · ∫_{D¹} δ_P(n)⁻¹ |Φ(n k)|² dn`, where `μ_M = c · haar` and
`B = ∫_A β(y(a)) da`. The Bochner product formula needs no integrability, so `β` may change
sign. For a rational Levi, `a ↦ y(a)` is a group isomorphism of `A` onto `ℝⁿ`: rational
characters of `P` restrict bijectively to `M`, and the coordinates of `e` are onto. The image
of Haar measure is then a positive multiple of Lebesgue measure, so `B > 0` from `∫ β = 1`.
This gives nonnegativity. If the Gram sum vanishes, then `δ_P(n)⁻¹ |Φ(n k)|²` vanishes almost
everywhere on `D¹` for almost every `k`, hence everywhere by continuity and full support of the
quotient measure on `M(F) \ M(𝔸)¹` and of Haar probability on `K`. The `A`-equivariance,
left `U(𝔸)`-invariance and `G(𝔸) = P(𝔸) K` then give `Φ = 0`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ComplexOrder ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.InducedInnerProductGram

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InducedInnerProductSesquilinear

section Haar

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [AddGroup A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]

/-- The image of a Haar measure under a homeomorphism `f` with `f (x * y) = f x + f y` is an
additive Haar measure. -/
theorem isAddHaarMeasure_map_of_map_mul (ν : Measure G) [ν.IsHaarMeasure] (f : G ≃ₜ A)
    (hf : ∀ x y, f (x * y) = f x + f y) : (Measure.map f ν).IsAddHaarMeasure where
  toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map ν f
  toIsOpenPosMeasure := f.continuous.isOpenPosMeasure_map f.surjective
  toIsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) f.continuous.measurable]
    have h : (fun x => g + x) ∘ f = f ∘ (fun x => f.symm g * x) := by
      funext x
      simp [hf]
    rw [h, ← Measure.map_map f.continuous.measurable
      (measurable_const_mul (f.symm g)), map_mul_left_eq_self]

/-- A function with integral `1` on `ℝⁿ`, composed with a homeomorphism `f` from a group with
`f (x * y) = f x + f y`, has positive integral for every Haar measure. -/
theorem integral_comp_pos (ν : Measure G) [ν.IsHaarMeasure] {n : ℕ} (f : G ≃ₜ (Fin n → ℝ))
    (hf : ∀ x y, f (x * y) = f x + f y) (β : (Fin n → ℝ) → ℝ) (hβ : ∫ y, β y = 1) :
    0 < ∫ x, β (f x) ∂ν := by
  have := isAddHaarMeasure_map_of_map_mul ν f hf
  have hint : ∫ x, β (f x) ∂ν = ∫ y, β y ∂(Measure.map f ν) :=
    (integral_map_equiv f.toMeasurableEquiv β).symm
  rw [hint, Measure.isAddLeftInvariant_eq_smul (Measure.map f ν) volume,
    integral_smul_nnreal_measure, hβ, NNReal.smul_def, smul_eq_mul, mul_one]
  exact NNReal.coe_pos.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _)

end Haar

section Levi

variable {F : Type} [Field F] {P M : GroupScheme (Spec (CommRingCat.of F))}

/-- Restriction of rational characters to a rational Levi subgroup is injective: a character
of `P = M U` is trivial on the unipotent radical `U`. (This reproduces a private lemma of
`Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction`.) -/
theorem characterRestrict_injective_of_levi {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) : Function.Injective (characterRestrict l) := by
  obtain ⟨U, i, hi, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l i) := hmul
  intro χ ψ h
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  have hfactor (θ : rationalCharacters P) :
      x ≫ θ.toMul.hom.hom = leviComponent l i x ≫ (characterRestrict l θ).toMul.hom.hom := by
    have htriv := hi.1.isUnipotent.comp_eq_one_of_isSplitTorus isSplitTorus_gm
      (i ≫ θ.toMul) T (radicalComponent l i x)
    simp only [Grp.comp_hom_hom] at htriv
    calc
      _ = ((leviComponent l i x ≫ l.hom.hom) *
          (radicalComponent l i x ≫ i.hom.hom)) ≫ θ.toMul.hom.hom :=
        congrArg (fun y : T ⟶ P.X => y ≫ θ.toMul.hom.hom)
          (leviComponent_mul_radicalComponent l i x).symm
      _ = _ := by
        simp only [MonObj.mul_comp, Category.assoc, htriv, mul_one,
          characterRestrict_apply, Grp.comp_hom_hom]
  rw [hfactor χ, hfactor ψ, h]

end Levi

section Coordinates

variable {F : Type} [Field F] [NumberField F]
  {P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)

omit [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- Every vector of `ℝⁿ` is the coordinate vector of some `H ∈ Hom(X^*(P), ℝ)`. -/
theorem coordinateMap_surjective : Function.Surjective (coordinateMap e) := by
  intro y
  let ψ : RealCharacterParameter F P →ₗ[ℝ] ℝ :=
    Fintype.linearCombination ℝ y ∘ₗ e.symm.toLinearMap
  let H : RealCharacterDual F P :=
    (AddMonoidHom.mk' (fun χ => ψ ((1 : ℝ) ⊗ₜ[ℤ] χ)) (fun a b => by
      rw [TensorProduct.tmul_add, map_add]) : rationalCharacters P →+ ℝ)
  have hpair : ∀ v, realParameterPairing F P v H = ψ v := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul t χ =>
      rw [realParameterPairing_tmul]
      change t * ψ ((1 : ℝ) ⊗ₜ[ℤ] χ) = ψ (t ⊗ₜ[ℤ] χ)
      rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, map_add]
  refine ⟨H, funext fun j => ?_⟩
  change realParameterPairing F P (e (Pi.single j 1)) H = y j
  rw [hpair]
  change Fintype.linearCombination ℝ y (e.symm (e (Pi.single j 1))) = y j
  rw [LinearEquiv.symm_apply_apply, Fintype.linearCombination_apply_single, one_smul]

omit [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- For a rational Levi `l`, the map `Hom(X^*(M), ℝ) → Hom(X^*(P), ℝ)` induced by `l` is onto. -/
theorem realCharacterDualMap_surjective_of_levi {l : M ⟶ P} (hl : IsRationalLeviSubgroup l) :
    Function.Surjective (realCharacterDualMap F M P l) := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  have hinj := characterRestrict_injective_of_levi hl
  have hleft : ∀ χ, characterRestrict π (characterRestrict l χ) = χ := by
    intro χ
    apply hinj
    change ((characterRestrict l).comp (characterRestrict π)) (characterRestrict l χ) =
      characterRestrict l χ
    rw [← characterRestrict_comp, hπ, characterRestrict_id]
    rfl
  intro H
  refine ⟨realCharacterDualMap F P M π H, ?_⟩
  apply AddMonoidHom.ext
  intro χ
  change H (characterRestrict π (characterRestrict l χ)) = H χ
  rw [hleft]

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

include hi in
theorem torusCoordinateMap_bijective (hl : IsRationalLeviSubgroup l) :
    Function.Bijective (torusCoordinateMap l e T i I e₀) := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  refine ⟨torusCoordinateMap_injective l e T i hi I e₀ hπ, ?_⟩
  exact (coordinateMap_surjective e).comp ((realCharacterDualMap_surjective_of_levi hl).comp
    ((realCharacterDualRestrictionEquiv F M T.toGrp i hi).surjective.comp
      (PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀).symm.surjective))

/-- The coordinates `y(a)` on the positive torus, as a homeomorphism onto `ℝⁿ`. -/
def torusCoordinateHomeomorph (hl : IsRationalLeviSubgroup l) :
    PositiveRealTorus.intrinsicSubgroup F T ≃ₜ (Fin n → ℝ) :=
  (positiveCoordinates T I e₀).trans
    (LinearEquiv.ofBijective (torusCoordinateMap l e T i I e₀)
      (torusCoordinateMap_bijective l e T i hi I e₀ hl)).toContinuousLinearEquiv.toHomeomorph

theorem torusCoordinateHomeomorph_apply (hl : IsRationalLeviSubgroup l)
    (a : PositiveRealTorus.intrinsicSubgroup F T) :
    torusCoordinateHomeomorph l e T i hi I e₀ hl a =
      parameterCoordinates F P e (characterLog F P
        (map F M P l (PositiveRealTorus.positivePointMap F M T i a))) :=
  (parameterCoordinates_positivePointMap l e T i I e₀ a).symm

theorem torusCoordinateHomeomorph_mul (hl : IsRationalLeviSubgroup l)
    (a b : PositiveRealTorus.intrinsicSubgroup F T) :
    torusCoordinateHomeomorph l e T i hi I e₀ hl (a * b) =
      torusCoordinateHomeomorph l e T i hi I e₀ hl a +
        torusCoordinateHomeomorph l e T i hi I e₀ hl b := by
  change torusCoordinateMap l e T i I e₀ (positiveCoordinates T I e₀ (a * b)) =
    torusCoordinateMap l e T i I e₀ (positiveCoordinates T I e₀ a) +
      torusCoordinateMap l e T i I e₀ (positiveCoordinates T I e₀ b)
  rw [← map_add]
  congr 1
  change PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀
      (characterLog F T.toGrp (a * b).val) =
    PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀ (characterLog F T.toGrp a.val) +
      PositiveRealTorus.dualCoordinatesContinuousEquiv F T I e₀ (characterLog F T.toGrp b.val)
  rw [← map_add, ← characterLog_mul]
  rfl

end Coordinates

section Weight

variable {F : Type} [Field F] [NumberField F]
  {P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- For a rational Levi and `∫ β = 1`, the integral of `a ↦ β(y(a))` over the positive torus for
the normalized positive Haar measure is positive. No sign condition on `β` is needed: `y` is a
group isomorphism onto `ℝⁿ`, so the image of the Haar measure is a positive multiple of
Lebesgue measure. -/
theorem integral_positive_weight_pos (hl : IsRationalLeviSubgroup l) (hc : IsCentral i)
    {β : (Fin n → ℝ) → ℝ} (hβ1 : ∫ y, β y = 1) :
    0 < ∫ a, β (parameterCoordinates F P e (characterLog F P
      (map F M P l (PositiveRealTorus.positivePointMap F M T i a))))
        ∂PositiveRealTorus.normalizedPositiveHaarMeasure F M T i hi I e₀ hc := by
  let := PositiveRealTorus.positiveIsTopologicalGroup F T I e₀
  have := PositiveRealTorus.normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e₀ hc
  simp_rw [← torusCoordinateHomeomorph_apply l e T i hi I e₀ hl]
  exact integral_comp_pos _ _ (torusCoordinateHomeomorph_mul l e T i hi I e₀ hl) β hβ1

end Weight

section KernelSelf

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  (β : (Fin n → ℝ) → ℝ)

/-- The diagonal integrand is `β(y(m)) δ_P(m)⁻¹ |φ(m g)|²`. -/
theorem kernel_self_eq (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) :
    kernel p l e β φ φ g m =
      (β (parameterCoordinates F P e (characterLog F P (map F M P l m))) : ℂ) *
        (normWeight p l φ g m : ℂ) := by
  have h := ofReal_norm_parameterPower_neg_modulusParameter (map F M P l m)
  simp only [InducedInnerProductSesquilinear.kernel, InducedInnerProductSesquilinear.weight,
    InducedInnerProductSesquilinear.normWeight]
  conv_lhs => rw [← h]
  rw [mul_assoc _ (φ _), Complex.mul_conj']
  push_cast
  ring

theorem normWeight_nonneg (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (m : AdelicGroupPoints F M) : 0 ≤ normWeight p l φ g m := by
  unfold normWeight
  positivity

end KernelSelf

section Decomposition

open PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type) [Fintype I] (e₀ : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

theorem preimage_productDomain :
    (normOneDecomposition F M T i hi I e₀) ⁻¹' productDomain T i hi I e₀ =
      Set.univ ×ˢ normOneDomain (M := M) := by
  ext q
  simp only [Set.mem_preimage, productDomain, normOneDecomposition_apply,
    normOneFactor_positivePointMap_mul, Set.mem_prod, Set.mem_univ, true_and]

/-- Bochner integrals over `M(F) \ M(𝔸)` for Haar measure of continuous left `M(F)`-invariant
functions that factor as `b(a) w(n)` on `A × M(𝔸)¹`. No integrability is needed. -/
theorem integral_rationalQuotient_haar (hc : IsCentral i) (f : AdelicGroupPoints F M → ℂ)
    (b : intrinsicSubgroup F T → ℂ) (w : normOneSubgroup F M → ℂ)
    (hf : ∀ a (n : normOneSubgroup F M), f (positivePointMap F M T i a * n) = b a * w n)
    (hfinv : ∀ g ∈ rationalSubgroup F M, ∀ m, f (g * m) = f m) (hfc : Continuous f) :
    ∫ x : RationalQuotient F M, f x.out
        ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) Measure.haar) =
      (∫ a, b a ∂normalizedPositiveHaarMeasure F M T i hi I e₀ hc) *
        ∫ n in normOneDomain (M := M), w n ∂Measure.haar := by
  have := normalizedPositiveHaarMeasure_sigmaFinite F M T i hi I e₀ hc
  have hfmeas := continuous_out (rationalSubgroup F M) f hfc hfinv
  rw [LeftCosetSpace.discreteQuotientMeasure_eq _ _ _
      (isFundamentalDomain_productDomain T i hi I e₀ hc _),
    LeftCosetSpace.quotientMeasure, integral_map (LeftCosetSpace.measurable_mk _).aemeasurable
      hfmeas.aestronglyMeasurable]
  have h1 : ∀ m, f (LeftCosetSpace.mk (rationalSubgroup F M) m).out = f m :=
    out_mk_apply (rationalSubgroup F M) f hfinv
  simp_rw [h1]
  rw [← (measurePreserving_normOneDecomposition F M T i hi I e₀ hc).setIntegral_preimage_emb
    (normOneDecomposition F M T i hi I e₀).measurableEmbedding, preimage_productDomain,
    ← Measure.prod_restrict, Measure.restrict_univ]
  simp_rw [normOneDecomposition_apply, hf]
  exact integral_prod_mul b w

/-- If `f(a n) = b(a) w(n)` is integrable on `M(F) \ M(𝔸)` and `∫ b ≠ 0`, then `w` is
integrable on the norm-one fundamental domain `D¹`. -/
theorem integrableOn_normOneDomain (hc : IsCentral i) (f : AdelicGroupPoints F M → ℂ)
    (b : intrinsicSubgroup F T → ℂ) (w : normOneSubgroup F M → ℂ)
    (hf : ∀ a (n : normOneSubgroup F M), f (positivePointMap F M T i a * n) = b a * w n)
    (hfinv : ∀ g ∈ rationalSubgroup F M, ∀ m, f (g * m) = f m) (hfc : Continuous f)
    (hbc : Continuous b) (hwc : Continuous w)
    (hb : ∫ a, b a ∂normalizedPositiveHaarMeasure F M T i hi I e₀ hc ≠ 0)
    (hint : Integrable (fun x : RationalQuotient F M => f x.out)
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) Measure.haar)) :
    IntegrableOn w (normOneDomain (M := M)) Measure.haar := by
  have := normalizedPositiveHaarMeasure_sigmaFinite F M T i hi I e₀ hc
  set νA := normalizedPositiveHaarMeasure F M T i hi I e₀ hc
  have hfmeas := continuous_out (rationalSubgroup F M) f hfc hfinv
  rw [LeftCosetSpace.discreteQuotientMeasure_eq _ _ _
      (isFundamentalDomain_productDomain T i hi I e₀ hc _), LeftCosetSpace.quotientMeasure,
    integrable_map_measure hfmeas.aestronglyMeasurable
      (LeftCosetSpace.measurable_mk _).aemeasurable] at hint
  have h1 : ((fun x : RationalQuotient F M => f x.out) ∘
      LeftCosetSpace.mk (rationalSubgroup F M)) = f :=
    funext (out_mk_apply (rationalSubgroup F M) f hfinv)
  rw [h1] at hint
  have h2 := ((measurePreserving_normOneDecomposition F M T i hi I e₀ hc).integrableOn_comp_preimage
    (normOneDecomposition F M T i hi I e₀).measurableEmbedding (f := f)
    (s := productDomain T i hi I e₀)).mpr hint
  rw [preimage_productDomain, IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h2
  have h3 : (f ∘ normOneDecomposition F M T i hi I e₀) = fun q => b q.1 * w q.2 := by
    funext q
    rw [Function.comp_apply, normOneDecomposition_apply, hf]
  rw [h3] at h2
  have hmeas : AEStronglyMeasurable (fun q : intrinsicSubgroup F T × normOneSubgroup F M =>
      b q.1 * w q.2) (νA.prod (Measure.haar.restrict (normOneDomain (M := M)))) :=
    ((hbc.comp continuous_fst).mul (hwc.comp continuous_snd)).aestronglyMeasurable
  obtain ⟨-, h4⟩ := (integrable_prod_iff' hmeas).mp h2
  simp only [norm_mul, integral_mul_const] at h4
  have hpos : (∫ x, ‖b x‖ ∂νA) ≠ 0 := by
    have h5 : ‖∫ a, b a ∂νA‖ ≤ ∫ a, ‖b a‖ ∂νA := norm_integral_le_integral_norm b
    have h6 : 0 < ‖∫ a, b a ∂νA‖ := norm_pos_iff.mpr hb
    exact (lt_of_lt_of_le h6 h5).ne'
  have h5 := h4.const_mul (∫ x, ‖b x‖ ∂νA)⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hpos, one_mul] at h5
  exact (integrable_norm_iff hwc.aestronglyMeasurable).mp h5

/-- A continuous nonnegative left `M(F)`-invariant function on `M(𝔸)¹` whose integral over the
norm-one fundamental domain vanishes is identically zero: the quotient measure on
`M(F) \ M(𝔸)¹` charges every nonempty open set. -/
theorem eq_zero_of_setIntegral_normOneDomain (w : normOneSubgroup F M → ℝ)
    (hwc : Continuous w) (hw0 : ∀ n, 0 ≤ w n)
    (hwinv : ∀ g₀ ∈ rationalNormOneSubgroup F M, ∀ n, w (g₀ * n) = w n)
    (hint : IntegrableOn w (normOneDomain (M := M)) Measure.haar)
    (hzero : ∫ n in normOneDomain (M := M), w n ∂Measure.haar = 0) (n : normOneSubgroup F M) :
    w n = 0 := by
  have hcont := continuous_out (rationalNormOneSubgroup F M) w hwc hwinv
  have hν : normOneRationalQuotientHaarMeasure F M = Measure.map
      (LeftCosetSpace.mk (rationalNormOneSubgroup F M))
      (Measure.haar.restrict (normOneDomain (M := M))) := rfl
  have : (normOneRationalQuotientHaarMeasure F M).IsOpenPosMeasure :=
    LeftCosetSpace.isOpenPosMeasure_discreteQuotientMeasure (rationalNormOneSubgroup F M)
      (isDiscrete_rationalNormOneSubgroup F M) Measure.haar
  have h1 : (fun q : NormOneRationalQuotient F M => w q.out) ∘
      LeftCosetSpace.mk (rationalNormOneSubgroup F M) = w :=
    funext (out_mk_apply (rationalNormOneSubgroup F M) w hwinv)
  have hint' : Integrable (fun q : NormOneRationalQuotient F M => w q.out)
      (normOneRationalQuotientHaarMeasure F M) := by
    rw [hν, integrable_map_measure hcont.aestronglyMeasurable
      (LeftCosetSpace.measurable_mk _).aemeasurable, h1]
    exact hint
  have hzero' : ∫ q, w q.out ∂(normOneRationalQuotientHaarMeasure F M) = 0 := by
    rw [hν, integral_map (LeftCosetSpace.measurable_mk _).aemeasurable
      hcont.aestronglyMeasurable]
    simp_rw [out_mk_apply (rationalNormOneSubgroup F M) w hwinv]
    exact hzero
  have hae := (integral_eq_zero_iff_of_nonneg (fun q => hw0 _) hint').mp hzero'
  have heq := (hcont.ae_eq_iff_eq (normOneRationalQuotientHaarMeasure F M)
    continuous_zero).mp hae
  have h2 := congrFun heq (LeftCosetSpace.mk (rationalNormOneSubgroup F M) n)
  simpa [out_mk_apply (rationalNormOneSubgroup F M) w hwinv] using h2

end Decomposition

section Main

open PositiveRealTorus RestrictionSplitCentre

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  {β : (Fin n → ℝ) → ℝ}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
/-- `δ_P(m)⁻¹ |φ(m g)|² = 0` forces `φ(m g) = 0`. -/
theorem form_eq_zero_of_normWeight_eq_zero {φ : AdelicGroupPoints F G → ℂ}
    {g : AdelicGroupPoints F G} {m : AdelicGroupPoints F M} (h : normWeight p l φ g m = 0) :
    φ (map F P G p (map F M P l m) * g) = 0 := by
  unfold InducedInnerProductSesquilinear.normWeight at h
  have hpp : ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖ ≠ 0 := by
    rw [parameterPower_neg_modulusParameter, Complex.norm_real]
    exact norm_ne_zero_iff.mpr (Real.exp_pos _).ne'
  have h2 := (mul_eq_zero.mp h).resolve_left hpp
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

/-- The diagonal inner integral over `M(F) \ M(𝔸)` of a continuous `Φ`, left `M(F)`-invariant
and `A_M`-equivariant, is a fixed positive constant times the integral of
`δ_P(n)⁻¹ |Φ(n g)|²` over the norm-one fundamental domain `D¹`; and if the inner integrand
is integrable and the latter integral vanishes, then `δ_P(m)⁻¹ |Φ(m g)|² = 0` for every
`m ∈ M(𝔸)`. -/
theorem kernel_self_data (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
    (hl : IsRationalLeviSubgroup l) (hβc : Continuous β) (hβ1 : ∫ y, β y = 1)
    {Φ : AdelicGroupPoints F G → ℂ} (hΦc : Continuous Φ)
    (hΦinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) Φ)
    (hΦeq : IsSplitComponentEquivariant p l Φ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ g : AdelicGroupPoints F G,
        ∫ q : RationalQuotient F M, kernel p l e β Φ Φ g q.out
            ∂(LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
              (isDiscrete_rationalSubgroup F M) μM) =
          ((C * ∫ n in normOneDomain (M := M), normWeight p l Φ g n ∂Measure.haar : ℝ) : ℂ)) ∧
      (∀ g : AdelicGroupPoints F G,
        Integrable (fun q : RationalQuotient F M => kernel p l e β Φ Φ g q.out)
            (LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
              (isDiscrete_rationalSubgroup F M) μM) →
        ∫ n in normOneDomain (M := M), normWeight p l Φ g n ∂Measure.haar = 0 →
        ∀ m : AdelicGroupPoints F M, normWeight p l Φ g m = 0) := by
  have hM : IsConnectedReductive M := hl.isConnectedReductive
  have hs₀ := isSplitComponent_canonicalComponent F M
  have hi := canonical_characterRestrict_injective F M centralSplitTorusCharacter hM
  have := canonical_finiteIndex F M hM
  obtain ⟨I, hIfin, ⟨e₀⟩⟩ := hs₀.1.1.1
  have hc : IsCentral (canonicalComponent F M) := hs₀.1.2
  let := Fintype.ofFinite I
  set T := canonicalTorus F M
  set A := canonicalComponent F M
  set νA := normalizedPositiveHaarMeasure F M T A hi I e₀ hc
  let yA : intrinsicSubgroup F T → ℝ := fun a => β (parameterCoordinates F P e
    (characterLog F P (map F M P l (positivePointMap F M T A a))))
  have hB : 0 < ∫ a, yA a ∂νA := integral_positive_weight_pos l e T A hi I e₀ hl hc hβ1
  have hyc : Continuous yA := hβc.comp ((continuous_parameterCoordinates F P e).comp
    ((continuous_characterLog F P).comp ((map F M P l).continuous.comp
      (positivePointMap F M T A).continuous)))
  set c := Measure.haarScalarFactor μM (Measure.haar : Measure (AdelicGroupPoints F M))
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hν : LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM =
      c • LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) Measure.haar := by
    have hμ : μM = c • (Measure.haar : Measure (AdelicGroupPoints F M)) :=
      Measure.isMulLeftInvariant_eq_smul μM Measure.haar
    rw [hμ]
    unfold LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    rw [Measure.restrict_smul, Measure.map_smul _ (LeftCosetSpace.measurable_mk _).aemeasurable]
  have hf : ∀ (g : AdelicGroupPoints F G) a (n : normOneSubgroup F M),
      kernel p l e β Φ Φ g (positivePointMap F M T A a * n) =
        (yA a : ℂ) * (normWeight p l Φ g n : ℂ) := by
    intro g a n
    rw [kernel_self_eq, characterLog_map_mul_normOne l n.property,
      normWeight_splitComponent_mul hΦeq (mem_canonicalSubgroup_positivePointMap a) g n]
  have hfinv : ∀ (g : AdelicGroupPoints F G), ∀ x ∈ AdelicGroupPoints.rationalSubgroup F M, ∀ m,
      kernel p l e β Φ Φ g (x * m) = kernel p l e β Φ Φ g m :=
    fun g x hx m => kernel_rational_mul e β hΦinv hΦinv hx g m
  have hfc : ∀ g : AdelicGroupPoints F G, Continuous (fun m => kernel p l e β Φ Φ g m) :=
    fun g => continuous_kernel p l e β (ξ := fun _ : AdelicGroupPoints F M => g) (τ := id)
      continuous_const continuous_id hβc hΦc hΦc
  have hwc : ∀ g : AdelicGroupPoints F G,
      Continuous (fun n : normOneSubgroup F M => normWeight p l Φ g n) :=
    fun g => continuous_normWeight p l (ξ := fun _ : normOneSubgroup F M => g)
      (τ := Subtype.val) continuous_const continuous_subtype_val hΦc
  refine ⟨c * ∫ a, yA a ∂νA, mul_pos (NNReal.coe_pos.mpr hcpos) hB, fun g => ?_,
    fun g hint hW m => ?_⟩
  · rw [hν, integral_smul_nnreal_measure,
      integral_rationalQuotient_haar T A hi I e₀ hc _ (fun a => (yA a : ℂ))
        (fun n => (normWeight p l Φ g n : ℂ)) (hf g) (hfinv g) (hfc g),
      integral_complex_ofReal, integral_complex_ofReal, NNReal.smul_def, Complex.real_smul]
    push_cast
    ring
  · rw [hν, ← Measure.coe_nnreal_smul, integrable_smul_measure
      (ENNReal.coe_ne_zero.mpr hcpos.ne') ENNReal.coe_ne_top] at hint
    have hb : ∫ a, (yA a : ℂ) ∂νA ≠ 0 := by
      rw [integral_complex_ofReal]
      exact_mod_cast hB.ne'
    have hwC := integrableOn_normOneDomain T A hi I e₀ hc _ (fun a => (yA a : ℂ))
      (fun n => (normWeight p l Φ g n : ℂ)) (hf g) (hfinv g) (hfc g)
      (Complex.continuous_ofReal.comp hyc) (Complex.continuous_ofReal.comp (hwc g)) hb hint
    have hwR : IntegrableOn (fun n : normOneSubgroup F M => normWeight p l Φ g n)
        (normOneDomain (M := M)) Measure.haar := by
      simpa using hwC.re
    have hvan1 : ∀ n : normOneSubgroup F M, normWeight p l Φ g n = 0 :=
      eq_zero_of_setIntegral_normOneDomain (fun n : normOneSubgroup F M => normWeight p l Φ g n)
        (hwc g) (fun n => normWeight_nonneg p l Φ g n)
        (fun g₀ hg₀ n => normWeight_rational_mul hΦinv
          (rationalNormOneSubgroupInclusion F M ⟨g₀, hg₀⟩).property g n) hwR hW
    obtain ⟨a, n₀, rfl⟩ : ∃ (a : intrinsicSubgroup F T) (n₀ : normOneSubgroup F M),
        positivePointMap F M T A a * (n₀ : AdelicGroupPoints F M) = m :=
      ⟨_, _, (normOneDecomposition F M T A hi I e₀).apply_symm_apply m⟩
    rw [normWeight_splitComponent_mul hΦeq (mem_canonicalSubgroup_positivePointMap a) g n₀]
    exact hvan1 n₀

end Main

end Langlands.Global.InducedInnerProductGram

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InducedInnerProductSesquilinear InducedInnerProductGram

/-- **Positive definiteness of `(·,·)_P` on `A^2_P`** (Lapid 2011, §2, p.311), in Gram form. -/
theorem inducedInnerProductGram_of_torusCoordinates : InducedInnerProductGramStatement := by
  intro F _ _ G P M U _ _ _ _ _ _ _ p _ iU l _ hG hp hU hl hmul K hK N d rho hsmooth hcalc μM _
    n e β hβc hβs hβ1 m φ hφ x
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hM : IsConnectedReductive M := hl.isConnectedReductive
  obtain ⟨_, _, π, _, _, hlπ, _⟩ := hl.exists_unipotentRadical_retraction
  have := InducedInnerProductSesquilinear.sFinite_discreteQuotientMeasure μM
  let Φ : AdelicGroupPoints F G → ℂ := fun g => ∑ j, x j * φ j g
  have hΦsum : ∑ j, x j • φ j = Φ := by
    funext g
    simp [Φ, Finset.sum_apply]
  have hΦc : Continuous Φ :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (hφ j).1.2.1.1
  have hΦinvU : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) Φ := by
    intro y hy g
    simp only [Φ, (hφ _).1.1 y hy g]
  have hΦinv : IsLeftInvariantUnder F G (parabolicLeviRationalImage F p l) Φ :=
    fun y hy g => hΦinvU y (Subgroup.mem_sup_right hy) g
  have hΦeq : IsSplitComponentEquivariant p l Φ := by
    intro a ha g
    simp only [Φ, (hφ _).2.1 a ha g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hgram : ∫ k : K, ∫ q : RationalQuotient F M, kernel p l e β Φ Φ k q.out
        ∂(LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM) ∂(compactHaarProbability F G K hK.isCompact) =
      ∑ i, ∑ i', x i * (starRingEnd ℂ) (x i') *
        inducedInnerProduct K hK.isCompact p l μM e β (φ i) (φ i') := by
    simp only [inducedInnerProduct_eq_kernel p l e β K hK.isCompact μM, Φ, kernel_sum]
    exact integral_integral_sum_sum
      (fun j j' (q : K) (y : RationalQuotient F M) => kernel p l e β (φ j) (φ j') q y.out)
      (fun j j' => integrable_kernel e K hK.isCompact hM hlπ hβc hβs μM (hφ j) (hφ j'))
      (fun j j' => x j * (starRingEnd ℂ) (x j'))
  have hkerint : Integrable (fun q : K × RationalQuotient F M => kernel p l e β Φ Φ q.1 q.2.out)
      ((compactHaarProbability F G K hK.isCompact).prod
        (LeftCosetSpace.discreteQuotientMeasure (AdelicGroupPoints.rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
    simp only [Φ, kernel_sum]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ =>
      (integrable_kernel e K hK.isCompact hM hlπ hβc hβs μM (hφ j) (hφ j')).const_mul _
  obtain ⟨C, hC, hint, hvan⟩ := kernel_self_data e μM hl hβc hβ1 hΦc hΦinv hΦeq
  let W : K → ℝ := fun k => ∫ n in normOneDomain (M := M), normWeight p l Φ k n ∂Measure.haar
  have hW0 : ∀ k, 0 ≤ W k := fun k => integral_nonneg fun n => normWeight_nonneg p l Φ _ _
  have hG' : ∑ i, ∑ i', x i * (starRingEnd ℂ) (x i') *
      inducedInnerProduct K hK.isCompact p l μM e β (φ i) (φ i') =
      ((C * ∫ k, W k ∂(compactHaarProbability F G K hK.isCompact) : ℝ) : ℂ) := by
    rw [← hgram]
    simp_rw [hint]
    rw [integral_complex_ofReal, integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hG']
    exact Complex.zero_le_real.mpr (mul_nonneg hC.le (integral_nonneg hW0))
  rw [hG', hΦsum]
  constructor
  · intro h0
    have hint0 : ∫ k, W k ∂(compactHaarProbability F G K hK.isCompact) = 0 := by
      have h1 : C * ∫ k, W k ∂(compactHaarProbability F G K hK.isCompact) = 0 := by
        exact_mod_cast h0
      exact (mul_eq_zero.mp h1).resolve_left hC.ne'
    have hJ := hkerint.integral_prod_left
    simp_rw [hint] at hJ
    have hWint : Integrable W (compactHaarProbability F G K hK.isCompact) := by
      refine (hJ.norm.const_mul C⁻¹).congr (Filter.Eventually.of_forall fun k => ?_)
      have hk : ‖((C * W k : ℝ) : ℂ)‖ = C * W k := by
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC.le (hW0 k))]
      change C⁻¹ * ‖((C * W k : ℝ) : ℂ)‖ = W k
      rw [hk, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
    have hWae := (integral_eq_zero_iff_of_nonneg hW0 hWint).mp hint0
    have hvanae : ∀ᵐ (k : K) ∂(compactHaarProbability F G K hK.isCompact),
        ∀ mm : AdelicGroupPoints F M, normWeight p l Φ k mm = 0 := by
      filter_upwards [hWae, hkerint.prod_right_ae] with k hk1 hk2
      exact hvan k hk2 hk1
    have hvanK : ∀ (k : K) (mm : AdelicGroupPoints F M), normWeight p l Φ k mm = 0 := by
      intro k mm
      have hc1 : Continuous fun k : K => normWeight p l Φ k mm :=
        continuous_normWeight p l (ξ := fun k : K => (k : AdelicGroupPoints F G))
          (τ := fun _ => mm) continuous_subtype_val continuous_const hΦc
      have hae3 : (fun k : K => normWeight p l Φ k mm) =ᵐ[compactHaarProbability F G K
          hK.isCompact] 0 := by
        filter_upwards [hvanae] with k hk using hk mm
      exact congrFun ((hc1.ae_eq_iff_eq _ continuous_zero).mp hae3) k
    funext g
    obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq g
    let : IsIso (subgroupMultiplication l iU) := hmul
    have hz := leviComponent_mul_radicalComponent l iU q⁻¹
    set mm := leviComponent l iU q⁻¹
    set u := radicalComponent l iU q⁻¹
    have hq : q = map F U P iU u⁻¹ * map F M P l mm⁻¹ := by
      have hz' : map F M P l mm * map F U P iU u = q⁻¹ := hz
      rw [map_inv, map_inv, ← mul_inv_rev, hz', inv_inv]
    have hmem : map F P G p (map F U P iU u⁻¹) ∈ parabolicQuotientSubgroup F p iU l :=
      Subgroup.mem_sup_left ⟨u⁻¹, map_comp_apply_of_hom iU u⁻¹⟩
    rw [hq, map_mul, mul_assoc, hΦinvU _ hmem]
    exact form_eq_zero_of_normWeight_eq_zero (hvanK ⟨k, hk⟩ mm⁻¹)
  · intro h0
    have hW : W = 0 := by
      funext k
      simp [W, InducedInnerProductSesquilinear.normWeight, h0]
    rw [hW]
    simp

end Langlands.Global
