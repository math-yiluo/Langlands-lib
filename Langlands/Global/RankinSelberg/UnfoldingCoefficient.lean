import Langlands.Global.RankinSelberg.UnfoldingMeasure
import Langlands.Global.GeneralLinearGlobalWhittaker
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure

/-! # Character coefficients along subgroups with compact rational quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme AdelicSubgroupPoints

section RightTranslate

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H] (Γ : Subgroup H)

/-- Positive right translation on `Γ \ H` as a measurable equivalence. -/
def rightTranslateMeasurableEquiv (g : H) :
    LeftCosetSpace Γ ≃ᵐ LeftCosetSpace Γ where
  toFun := LeftCosetSpace.rightTranslate Γ g
  invFun := LeftCosetSpace.rightTranslate Γ g⁻¹
  left_inv q := by
    rw [LeftCosetSpace.rightTranslate_mul, mul_inv_cancel, LeftCosetSpace.rightTranslate_one]
  right_inv q := by
    rw [LeftCosetSpace.rightTranslate_mul, inv_mul_cancel, LeftCosetSpace.rightTranslate_one]
  measurable_toFun := LeftCosetSpace.measurable_rightTranslate Γ g
  measurable_invFun := LeftCosetSpace.measurable_rightTranslate Γ g⁻¹

end RightTranslate

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance coefficientSubgroupLocallyCompactSpace :
    LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

local instance coefficientSubgroupPolishSpace : PolishSpace (adelicPoints F G U) :=
  hclosed.polishSpace

local instance coefficientQuotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

/-- The integrand of a character coefficient, as a function on the rational quotient. -/
def coefficientIntegrand (χ : adelicPoints F G U → ℂ) (f : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (q : RationalQuotient F G U) : ℂ :=
  f (((Quotient.out q : adelicPoints F G U) : AdelicGroupPoints F G) * g) *
    starRingEnd ℂ (χ (Quotient.out q))

theorem subgroupCharacterCoefficient_eq_integral (χ : adelicPoints F G U → ℂ)
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    subgroupCharacterCoefficient F G U χ f g =
      ∫ q, coefficientIntegrand F G U χ f g q ∂normalizedRationalQuotientHaarMeasure F G U :=
  rfl

/-- Left `U(𝔸)`-equivariance of a character coefficient: if `f` is left invariant under
`U(F)` and `χ` is a unitary character of `U(𝔸)` trivial on `U(F)`, then the coefficient
transforms by `χ` under left translation by `U(𝔸)`. -/
theorem subgroupCharacterCoefficient_mul_left [CompactSpace (RationalQuotient F G U)]
    (χ : adelicPoints F G U → ℂ) (hχ_mul : ∀ a b, χ (a * b) = χ a * χ b)
    (hχ_rat : ∀ k : rationalSubgroup F G U, χ k = 1) (hχ_norm : ∀ a, ‖χ a‖ = 1)
    (f : AdelicGroupPoints F G → ℂ)
    (hf : ∀ (k : rationalSubgroup F G U) (x : AdelicGroupPoints F G),
      f (((k : adelicPoints F G U) : AdelicGroupPoints F G) * x) = f x)
    (u : adelicPoints F G U) (g : AdelicGroupPoints F G) :
    subgroupCharacterCoefficient F G U χ f ((u : AdelicGroupPoints F G) * g) =
      χ u * subgroupCharacterCoefficient F G U χ f g := by
  set Λ := rationalSubgroup F G U
  have hmp := measurePreserving_rightTranslate_of_compactRationalQuotient F G U u
  have key : ∀ q : RationalQuotient F G U,
      coefficientIntegrand F G U χ f g (LeftCosetSpace.rightTranslate Λ u q) =
        starRingEnd ℂ (χ u) * coefficientIntegrand F G U χ f ((u : AdelicGroupPoints F G) * g)
          q := by
    intro q
    have hq : LeftCosetSpace.rightTranslate Λ u q =
        LeftCosetSpace.mk Λ ((Quotient.out q : adelicPoints F G U) * u) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    obtain ⟨k, hk⟩ := exists_out_mk_eq Λ ((Quotient.out q : adelicPoints F G U) * u)
    simp only [coefficientIntegrand]
    rw [hq, hk]
    have h1 : (((k : adelicPoints F G U) * ((Quotient.out q : adelicPoints F G U) * u) :
        adelicPoints F G U) : AdelicGroupPoints F G) * g =
        ((k : adelicPoints F G U) : AdelicGroupPoints F G) *
          (((Quotient.out q : adelicPoints F G U) : AdelicGroupPoints F G) *
            ((u : AdelicGroupPoints F G) * g)) := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [h1, hf, hχ_mul, hχ_mul, hχ_rat, one_mul, map_mul]
    ring
  have hint := hmp.integral_comp (rightTranslateMeasurableEquiv Λ u).measurableEmbedding
    (coefficientIntegrand F G U χ f g)
  change ∫ q, coefficientIntegrand F G U χ f g (LeftCosetSpace.rightTranslate Λ u q)
      ∂normalizedRationalQuotientHaarMeasure F G U = _ at hint
  simp_rw [key] at hint
  rw [integral_const_mul] at hint
  rw [subgroupCharacterCoefficient_eq_integral, subgroupCharacterCoefficient_eq_integral,
    ← hint, ← mul_assoc]
  have hn : χ u * starRingEnd ℂ (χ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ_norm]
    simp
  rw [hn, one_mul]

/-- A character coefficient as a set integral over the chosen Borel fundamental domain of
`U(F)` in `U(𝔸)`, scaled by the mass normalizer. -/
theorem subgroupCharacterCoefficient_eq_setIntegral
    (χ : adelicPoints F G U → ℂ) (hχm : Measurable χ)
    (hχΛ : ∀ (k : rationalSubgroup F G U) (n : adelicPoints F G U), χ (k * n) = χ n)
    (f : AdelicGroupPoints F G → ℂ) (hfm : Measurable f)
    (hf : ∀ (k : rationalSubgroup F G U) (x : AdelicGroupPoints F G),
      f (((k : adelicPoints F G U) : AdelicGroupPoints F G) * x) = f x)
    (g : AdelicGroupPoints F G) :
    subgroupCharacterCoefficient F G U χ f g =
      (quotientMassNormalizer F G U).toReal •
        ∫ n in LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
            (isDiscrete_rationalSubgroup F G U),
          f ((n : AdelicGroupPoints F G) * g) * starRingEnd ℂ (χ n) ∂Measure.haar := by
  rw [subgroupCharacterCoefficient_eq_integral, normalizedRationalQuotientHaarMeasure,
    integral_smul_measure]
  congr 1
  have hm : Measurable (fun n : adelicPoints F G U =>
      f ((n : AdelicGroupPoints F G) * g) * starRingEnd ℂ (χ n)) :=
    (hfm.comp (measurable_subtype_coe.mul_const g)).mul
      (Complex.continuous_conj.measurable.comp hχm)
  have hinv : ∀ (k : rationalSubgroup F G U) (n : adelicPoints F G U),
      f (((k * n : adelicPoints F G U)) * g) * starRingEnd ℂ (χ (k * n)) =
        f ((n : AdelicGroupPoints F G) * g) * starRingEnd ℂ (χ n) := by
    intro k n
    rw [hχΛ, Subgroup.coe_mul, mul_assoc, hf]
  exact integral_out_eq (rationalSubgroup F G U) hm hinv Measure.haar _

/-- A character coefficient of measurable data is measurable. -/
theorem measurable_subgroupCharacterCoefficient
    (χ : adelicPoints F G U → ℂ) (hχm : Measurable χ)
    (hχΛ : ∀ (k : rationalSubgroup F G U) (n : adelicPoints F G U), χ (k * n) = χ n)
    (f : AdelicGroupPoints F G → ℂ) (hfm : Measurable f)
    (hf : ∀ (k : rationalSubgroup F G U) (x : AdelicGroupPoints F G),
      f (((k : adelicPoints F G U) : AdelicGroupPoints F G) * x) = f x) :
    Measurable (subgroupCharacterCoefficient F G U χ f) := by
  have heq : subgroupCharacterCoefficient F G U χ f = fun g =>
      (quotientMassNormalizer F G U).toReal •
        ∫ n in LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
            (isDiscrete_rationalSubgroup F G U),
          f ((n : AdelicGroupPoints F G) * g) * starRingEnd ℂ (χ n) ∂Measure.haar :=
    funext fun g => subgroupCharacterCoefficient_eq_setIntegral F G U χ hχm hχΛ f hfm hf g
  rw [heq]
  refine Measurable.const_smul (M := ℝ) ?_ _
  have hj : Measurable (fun p : AdelicGroupPoints F G × adelicPoints F G U =>
      f ((p.2 : AdelicGroupPoints F G) * p.1) * starRingEnd ℂ (χ p.2)) :=
    (hfm.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)).mul
      (Complex.continuous_conj.measurable.comp (hχm.comp measurable_snd))
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

end Langlands.Global.RankinSelbergGlobal.Unfolding
