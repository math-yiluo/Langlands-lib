import Langlands.Global.AdelicSpectralTransformSpaces

/-! # Inner products of restrictions in `H_P`

For `φ, ψ` on `G(𝔸)` whose restrictions `(k, m) ↦ φ(mk)` to Iwasawa coordinates
`K × M(F) \ M(𝔸)` represent elements `f, g` of `L²(β(y(m)) δ_P(m)⁻¹ dk dm)`, the `L²` inner
product `⟪f, g⟫` is the induced inner product `(ψ, φ)_P` of `inducedInnerProduct`; and
square-integrable restrictions of elements of `A^2_P` and their finite linear combinations give
elements of the Hilbert space `H_P` of `inducedHilbertSpace`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ENNReal InnerProductSpace

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

section Pairing

variable {F : Type} [Field F] [NumberField F] {P : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- The pairing `H ↦ ⟨μ, H⟩` with a fixed `μ ∈ X^*(P) ⊗ ℝ` is continuous on
`Hom(X^*(P), ℝ)`. -/
theorem continuous_realParameterPairing (mu : RealCharacterParameter F P) :
    Continuous (realParameterPairing F P mu) := by
  induction mu using TensorProduct.inductionOn with
  | tmul t χ =>
    exact (continuous_const.mul (continuous_dualEval F P χ)).congr fun H =>
      (realParameterPairing_tmul F P t χ H).symm
  | add x y hx hy =>
    exact (hx.add hy).congr fun H => by simp

variable [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]

/-- `m^{-2ρ_P} = exp(-H_P(m)(det Ad))` is a positive real number. -/
theorem parameterPower_neg_modulusParameter (y : AdelicGroupPoints F P) :
    parameterPower F P (-modulusParameter F P) y =
      (Real.exp (-(characterLog F P y (Lie.adjointDeterminantCharacter P))) : ℂ) := by
  unfold modulusParameter
  rw [parameterPower, map_neg, LinearMap.neg_apply,
    complexParameterPairing_tmul, one_mul, Complex.ofReal_exp, Complex.ofReal_neg]

/-- `m^{-2ρ_P}` equals its absolute value. -/
theorem ofReal_norm_parameterPower_neg_modulusParameter (y : AdelicGroupPoints F P) :
    ((‖parameterPower F P (-modulusParameter F P) y‖ : ℝ) : ℂ) =
      parameterPower F P (-modulusParameter F P) y := by
  rw [parameterPower_neg_modulusParameter, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

end Pairing

section Weight

variable {F : Type} [Field F] [NumberField F] {P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  (l : M ⟶ P) {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  (β : (Fin n → ℝ) → ℝ)

/-- The weight `β(y(m)) δ_P(m)⁻¹` on `M(𝔸)`, the density of `inducedL2Measure` at the coset
of `m` when `m` is the chosen representative. -/
def inducedWeight (m : AdelicGroupPoints F M) : ℝ :=
  β (parameterCoordinates F P e (characterLog F P (map F M P l m))) *
    ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖

omit [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] in
/-- `H_P(γ m) = H_P(m)` for `γ ∈ M(F)`. -/
theorem characterLog_map_rational_mul {g0 : AdelicGroupPoints F M}
    (hg0 : g0 ∈ rationalSubgroup F M) (m : AdelicGroupPoints F M) :
    characterLog F P (map F M P l (g0 * m)) = characterLog F P (map F M P l m) := by
  obtain ⟨x, rfl⟩ := hg0
  rw [map_mul, characterLog_mul, characterLog_map, characterLog_rational, map_zero, zero_add]

/-- The weight is left invariant under `M(F)`. -/
theorem inducedWeight_rational_mul {g0 : AdelicGroupPoints F M}
    (hg0 : g0 ∈ rationalSubgroup F M) (m : AdelicGroupPoints F M) :
    inducedWeight l e β (g0 * m) = inducedWeight l e β m := by
  simp only [inducedWeight, parameterPower, characterLog_map_rational_mul l hg0 m]

theorem inducedWeight_nonneg (hβ : ∀ y, 0 ≤ β y) (m : AdelicGroupPoints F M) :
    0 ≤ inducedWeight l e β m :=
  mul_nonneg (hβ _) (norm_nonneg _)

/-- The weight is continuous when `β` is. -/
theorem continuous_inducedWeight (hβ : Continuous β) : Continuous (inducedWeight l e β) := by
  have hH : Continuous fun m => characterLog F P (map F M P l m) :=
    (continuous_characterLog F P).comp (map F M P l).continuous
  refine (hβ.comp ?_).mul ?_
  · exact continuous_pi fun j => (continuous_realParameterPairing _).comp hH
  · simp only [parameterPower_neg_modulusParameter]
    exact continuous_norm.comp (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_characterLog_eval F P _).comp (map F M P l).continuous).neg))

/-- The weight read at the chosen representatives is measurable on `M(F) \ M(𝔸)`. -/
theorem measurable_inducedWeight_out (hβ : Continuous β) :
    Measurable fun q : RationalQuotient F M => inducedWeight l e β q.out := by
  have hinv : ∀ (g0 : rationalSubgroup F M) (x : AdelicGroupPoints F M),
      inducedWeight l e β ((g0 : AdelicGroupPoints F M) * x) = inducedWeight l e β x :=
    fun g0 x => inducedWeight_rational_mul l e β g0.2 x
  have hq : (fun q : RationalQuotient F M => inducedWeight l e β q.out) =
      LeftCosetSpace.lift _ (inducedWeight l e β) hinv := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq]
  exact measurable_from_quotient.mpr (continuous_inducedWeight l e β hβ).measurable

end Weight

section Inner

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

instance sFinite_discreteQuotientMeasure (μM : Measure (AdelicGroupPoints F M)) [SFinite μM] :
    SFinite (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM) := by
  unfold LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
  infer_instance

variable (K : Subgroup (AdelicGroupPoints F G))
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (p : P ⟶ G) (l : M ⟶ P)
  (μM : Measure (AdelicGroupPoints F M)) [SFinite μM] {n : ℕ}
  (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)

omit [LocallyOfFiniteType G.X.hom] in
/-- The `L²` inner product of the classes of the restrictions of `φ` and `ψ` is the induced
inner product `(ψ, φ)_P` (Mathlib's inner products are conjugate linear in the first
variable, `inducedInnerProduct` in the second). -/
theorem inner_eq_inducedInnerProduct (hβc : Continuous β) (hβ0 : ∀ y, 0 ≤ β y)
    (f g : Lp ℂ 2 (inducedL2Measure K hKc l μM e β)) (φ ψ : AdelicGroupPoints F G → ℂ)
    (hf : f =ᵐ[inducedL2Measure K hKc l μM e β] inducedRestriction K p l φ)
    (hg : g =ᵐ[inducedL2Measure K hKc l μM e β] inducedRestriction K p l ψ) :
    ⟪f, g⟫_ℂ = inducedInnerProduct K hKc p l μM e β ψ φ := by
  set D : K × RationalQuotient F M → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (inducedWeight l e β x.2.out) with hD
  have hμ : inducedL2Measure K hKc l μM e β =
      ((compactHaarProbability F G K hKc).prod (LeftCosetSpace.discreteQuotientMeasure
        (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M) μM)).withDensity D := by
    rw [hD]; rfl
  have hDm : Measurable D :=
    ENNReal.measurable_ofReal.comp ((measurable_inducedWeight_out l e β hβc).comp measurable_snd)
  have hDlt : ∀ᵐ x ∂((compactHaarProbability F G K hKc).prod
      (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) μM)), D x < ∞ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hDreal : ∀ x, (D x).toReal = inducedWeight l e β x.2.out := fun x =>
    ENNReal.toReal_ofReal (inducedWeight_nonneg l e β hβ0 _)
  set h : K × RationalQuotient F M → ℂ := fun x =>
    (starRingEnd ℂ) (inducedRestriction K p l φ x) * inducedRestriction K p l ψ x with hh
  have hfg : (fun x => ⟪f x, g x⟫_ℂ) =ᵐ[inducedL2Measure K hKc l μM e β] h := by
    filter_upwards [hf, hg] with x h1 h2
    rw [h1, h2, RCLike.inner_apply']
  have hint : Integrable h (inducedL2Measure K hKc l μM e β) :=
    (L2.integrable_inner f g).congr hfg
  rw [hμ, integrable_withDensity_iff_integrable_smul' hDm hDlt] at hint
  rw [L2.inner_def, integral_congr_ae hfg, hμ,
    integral_withDensity_eq_integral_toReal_smul hDm hDlt, integral_prod _ hint]
  unfold inducedInnerProduct
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [hDreal, hh, inducedRestriction, inducedWeight, Complex.real_smul, Complex.ofReal_mul,
    ofReal_norm_parameterPower_neg_modulusParameter]
  ring

end Inner

section Classes

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffineHom G.X.hom] [IsAffine U.X.left]
  (K : Subgroup (AdelicGroupPoints F G))
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth) (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)
  (μM : Measure (AdelicGroupPoints F M)) {n : ℕ}
  (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)

omit [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsAffine U.X.left] in
/-- The class of a square-integrable restriction of an element of `A^2_P` lies in `H_P`. -/
theorem toLp_mem_inducedHilbertSpace {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ)
    (hm : MemLp (inducedRestriction K p l φ) 2 (inducedL2Measure K hKc l μM e β)) :
    hm.toLp _ ∈ inducedHilbertSpace K hKc rho hsmooth hcalc p iU l μM e β :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, hm.coeFn_toLp⟩)

omit [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsAffine U.X.left] in
/-- A finite linear combination of classes of square-integrable restrictions of elements of
`A^2_P` lies in `H_P` and represents the restriction of the linear combination. -/
theorem sum_smul_toLp_mem_inducedHilbertSpace {m : ℕ} {ψ : Fin m → AdelicGroupPoints F G → ℂ}
    (hψ : ∀ q, IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l (ψ q))
    (hm : ∀ q, MemLp (inducedRestriction K p l (ψ q)) 2 (inducedL2Measure K hKc l μM e β))
    (c : Fin m → ℂ) :
    ∑ q, c q • (hm q).toLp _ ∈ inducedHilbertSpace K hKc rho hsmooth hcalc p iU l μM e β ∧
      ⇑(∑ q, c q • (hm q).toLp _ : Lp ℂ 2 (inducedL2Measure K hKc l μM e β))
        =ᵐ[inducedL2Measure K hKc l μM e β]
        inducedRestriction K p l (fun g => ∑ q, c q * ψ q g) := by
  refine ⟨Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _
    (toLp_mem_inducedHilbertSpace K hKc rho hsmooth hcalc p iU l μM e β (hψ q) (hm q)), ?_⟩
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hq : ∀ q ∈ (Finset.univ : Finset (Fin m)),
      ⇑(c q • (hm q).toLp _ : Lp ℂ 2 (inducedL2Measure K hKc l μM e β))
        =ᵐ[inducedL2Measure K hKc l μM e β] c q • inducedRestriction K p l (ψ q) :=
    fun q _ => (Lp.coeFn_smul _ _).trans ((hm q).coeFn_toLp.const_smul (c q))
  refine (eventuallyEq_sum hq).trans (Filter.Eventually.of_forall fun x => ?_)
  simp [inducedRestriction, Finset.sum_apply]

end Classes

end Langlands.Global.AdelicGroupPoints
