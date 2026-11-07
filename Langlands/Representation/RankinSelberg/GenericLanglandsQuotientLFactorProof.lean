import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.Representation.Whittaker.FiniteProductCriterion
import Langlands.Representation.Classification.LanglandsDatumRealization

/-!
# Generic Langlands quotients have the L-factor of their standard modules

JPSS 1983, (9.4), display (4). A standard module with a surjection onto a
representation carrying a nonzero Whittaker functional is of Whittaker type, so
the standard module and its generic quotient have the same Whittaker functions
and hence the same L-polynomial.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial
open PadicField.TopologicalData

universe uF uV uW uV₂ uW₂

section CoefficientSets

variable {G : Type*} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {ρ : Representation ℂ G V} {ρ₂ : Representation ℂ G V₂}

/-- If every functional of the source is a multiple of the pullback of one functional
of a surjective image, every coefficient function of the source is a coefficient
function of the image. -/
theorem exists_coefficientModel_of_surjective
    (f : ρ.IntertwiningMap ρ₂) (hf : Function.Surjective f) (ℓ₂ : functionals N θ ρ₂)
    (hspan : ∀ ℓ : functionals N θ ρ, ∃ c : ℂ, ℓ = c • functionalsComap f ℓ₂)
    (ℓ : functionals N θ ρ) {w} (hw : w ∈ (coefficientModel ρ ℓ).toSubmodule) :
    ∃ ℓ' : functionals N θ ρ₂, w ∈ (coefficientModel ρ₂ ℓ').toSubmodule := by
  obtain ⟨c, rfl⟩ := hspan ℓ
  refine ⟨c • ℓ₂, ?_⟩
  rw [← map_smul, coefficientModel_functionalsComap f hf] at hw
  exact hw

end CoefficientSets

section WhittakerSets

variable {F : Type uF} [Field F] [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂}

/-- A surjection from a representation of Whittaker type onto one with a nonzero
functional identifies their Whittaker functions. -/
theorem whittakerSet_eq_of_surjective_of_whittakerType
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (hπ₂ : HasFunctional (N := upperUnipotent (n + 1) F) (θ := standardCharacter ψ n) π₂) :
    whittakerSet ψ n π = whittakerSet ψ n π₂ := by
  refine Set.Subset.antisymm ?_ (whittakerSet_subset_of_surjective ψ f hf)
  rintro w ⟨ℓ, hw⟩
  obtain ⟨ℓ₂, hℓ₂⟩ := hπ₂
  exact exists_coefficientModel_of_surjective f hf ℓ₂
    (hπ.eq_smul (functionalsComap_ne_zero f hf ℓ₂ hℓ₂)) ℓ hw

/-- The inverse-character analogue of
`whittakerSet_eq_of_surjective_of_whittakerType`. -/
theorem inverseWhittakerSet_eq_of_surjective_of_whittakerType
    (hπ : IsOfWhittakerType n (inverseStandardCharacter ψ n) π)
    (f : π.IntertwiningMap π₂) (hf : Function.Surjective f)
    (hπ₂ : HasFunctional (N := upperUnipotent (n + 1) F)
      (θ := inverseStandardCharacter ψ n) π₂) :
    inverseWhittakerSet ψ n π = inverseWhittakerSet ψ n π₂ := by
  refine Set.Subset.antisymm ?_ (inverseWhittakerSet_subset_of_surjective ψ f hf)
  rintro w ⟨ℓ, hw⟩
  obtain ⟨ℓ₂, hℓ₂⟩ := hπ₂
  exact exists_coefficientModel_of_surjective f hf ℓ₂
    (hπ.eq_smul (functionalsComap_ne_zero f hf ℓ₂ hℓ₂)) ℓ hw

end WhittakerSets

section PairCongruence

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂} {P : ℂ[X]}

/-- The pair L-polynomial depends only on the Whittaker functions of the first member
and the inverse-character Whittaker functions of the second. -/
theorem isPairLPolynomial_congr_whittakerSets
    (hπ : whittakerSet ψ r π = whittakerSet ψ r π₂)
    (hσ : inverseWhittakerSet ψ n σ = inverseWhittakerSet ψ n σ₂) :
    IsPairLPolynomial q ψ abv μ ν π σ P ↔ IsPairLPolynomial q ψ abv μ ν π₂ σ₂ P := by
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr, isPairLPolynomial_of_lt hnr]
    refine forall_congr' fun j => forall_congr' fun k => forall_congr' fun hr => ?_
    subst hr
    rw [unequalRankZetaValuesAt_rfl, unequalRankZetaValuesAt_rfl, unequalRankZetaValues,
      unequalRankZetaValues, hπ, hσ]
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairLPolynomial_self, isPairLPolynomial_self, IsEqualRankLPolynomial,
        IsEqualRankLPolynomial, equalRankZetaValues, equalRankZetaValues, hπ, hσ]
    · exact iff_of_false (not_isPairLPolynomial_of_lt (by omega))
        (not_isPairLPolynomial_of_lt (by omega))

end PairCongruence

section PadicCongruence

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}

/-- The p-adic pair L relation depends only on the two Whittaker-function sets
used by its zeta integrals. -/
theorem isPadicPairLPolynomial_congr_whittakerSets
    (hπ : letI := F.canonicalTopologicalData.topology
      whittakerSet ψ r π = whittakerSet ψ r π₂)
    (hσ : letI := F.canonicalTopologicalData.topology
      inverseWhittakerSet ψ n σ = inverseWhittakerSet ψ n σ₂) {P : ℂ[X]} :
    IsPadicPairLPolynomial F ψ ν π σ P ↔ IsPadicPairLPolynomial F ψ ν π₂ σ₂ P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => isPairLPolynomial_congr_whittakerSets hπ hσ

/-- The symmetric p-adic L relation in either rank order depends only on the
Whittaker functions of both members for both characters. -/
theorem isPadicSymmetricLPolynomial_congr_whittakerSets
    (hπ : letI := F.canonicalTopologicalData.topology
      whittakerSet ψ r π = whittakerSet ψ r π₂)
    (hπ' : letI := F.canonicalTopologicalData.topology
      inverseWhittakerSet ψ r π = inverseWhittakerSet ψ r π₂)
    (hσ : letI := F.canonicalTopologicalData.topology
      whittakerSet ψ n σ = whittakerSet ψ n σ₂)
    (hσ' : letI := F.canonicalTopologicalData.topology
      inverseWhittakerSet ψ n σ = inverseWhittakerSet ψ n σ₂) {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔ IsPadicSymmetricLPolynomial F ψ ν π₂ σ₂ P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact isPadicPairLPolynomial_congr_whittakerSets hπ hσ'
  · exact isPadicPairLPolynomial_congr_whittakerSets hσ hπ'

end PadicCongruence

section StandardModule

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)

/-- Normalized upper block induction of irreducible admissible blocks, each with a
nonzero Whittaker functional, is of Whittaker type. The block sizes are arbitrary
positive numbers, not syntactic successors. -/
theorem normalizedProduct_isOfWhittakerType_of_blocks (n : ℕ) (B : BlockShape (n + 1))
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (B.size i) F.Carrier) (W i))
    (hirr : ∀ i, Representation.IsIrreducible (σ i))
    (hadm : ∀ i, letI := F.canonicalTopologicalData.topology; IsAdmissible (σ i))
    (hfun : ∀ i, letI := F.canonicalTopologicalData.topology
      HasFunctional (N := upperUnipotent (B.size i) F.Carrier)
        (θ := entrywiseCharacter ψ.complex (B.size i)) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType n (standardCharacter ψ n) (F.canonicalNormalizedProductInduced B σ) := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨k, size, pos, total⟩ := B
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => by
      have := pos i
      show size i = size i - 1 + 1
      omega⟩
  refine normalizedProductWhittakerType.{uF, uW} p F ψ n k m total σ fun i => ?_
  have h : HasFunctional (N := upperUnipotent (m i + 1) F.Carrier)
      (θ := entrywiseCharacter ψ.complex (m i + 1)) (σ i) := hfun i
  rw [entrywiseCharacter_eq_standardCharacter] at h
  exact isOfWhittakerType_of_isGeneric F ⟨hirr i, hadm i, h⟩

/-- A standard module of a tempered Langlands datum with a surjective intertwining map
onto a representation carrying a nonzero Whittaker functional is of Whittaker type. -/
theorem standardModule_isOfWhittakerType_of_surjective {r : ℕ}
    (d : TemperedLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    (f : letI := F.canonicalTopologicalData.topology
      d.standardModule.representation.IntertwiningMap ρ) (hf : Function.Surjective f)
    (hρ : letI := F.canonicalTopologicalData.topology
      HasFunctional (N := upperUnipotent (r + 1) F.Carrier) (θ := standardCharacter ψ r) ρ) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType r (standardCharacter ψ r) d.standardModule.representation := by
  let T := F.canonicalTopologicalData
  let := T.topology
  obtain ⟨ℓ, hℓ⟩ := hρ
  let d' := d.universeLift.{uF, uV, uF}
  let E : d.standardModule.representation.Equiv d'.standardModule.representation :=
    d.universeLiftStandardModuleEquiv
  have hne : (functionalsComap E.symm.toIntertwiningMap (functionalsComap f ℓ)).val ≠ 0 :=
    functionalsComap_ne_zero _ (EquivLike.surjective E.symm) _
      (functionalsComap_ne_zero f hf ℓ hℓ)
  have hblocks := (hasStandardFunctional_finiteProduct_iff.{uF, uV} T ψ r d'.shape
    (T.twistedBlocks d'.shape d'.blocks d'.exponent)).mp ⟨_, hne⟩
  have hξ' : IsOfWhittakerType r (standardCharacter ψ r) d'.standardModule.representation :=
    normalizedProduct_isOfWhittakerType_of_blocks F ψ r d'.shape
      (fun i => (T.twistedBlocks d'.shape d'.blocks d'.exponent i).representation)
      (fun i => (isIrreducible_twist_iff _ _).mpr (d'.irreducible i))
      (fun i => (isAdmissible_twist_iff _ _ (T.isOpen_ker_determinantPowerCharacter _ _)).mpr
        (d'.tempered i).isAdmissible)
      hblocks
  exact hξ'.of_equiv E.symm

end StandardModule

/-- JPSS 1983, (9.4), display (4): a generic irreducible quotient of a standard
module has the L-polynomial of the standard module. -/
theorem genericLanglandsQuotientLFactor :
    GenericLanglandsQuotientLFactorStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t d e π σ hd he hπ hσ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨-, f, hf⟩ := hd
  obtain ⟨-, g, hg⟩ := he
  have hξ := standardModule_isOfWhittakerType_of_surjective F ψ d f hf hπ.2.2
  have hη := standardModule_isOfWhittakerType_of_surjective F ψ e g hg hσ.2.2
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists.{uF, max uF uV, max uF uW} p F ψ ν r t _ _
    π.representation σ.representation (isOfWhittakerType_of_isGeneric F hπ)
    (isOfWhittakerType_of_isGeneric F hσ)
  refine ⟨P, (isPadicSymmetricLPolynomial_congr_whittakerSets ?_ ?_ ?_ ?_).mpr hP, hP⟩
  · exact whittakerSet_eq_of_surjective_of_whittakerType ψ hξ f hf hπ.2.2
  · exact inverseWhittakerSet_eq_of_surjective_of_whittakerType ψ
      ((isOfWhittakerType_standard_iff_inverse ψ _).mp hξ) f hf
      (isOfInverseWhittakerType_of_isGeneric F hπ).exists_ne_zero
  · exact whittakerSet_eq_of_surjective_of_whittakerType ψ hη g hg hσ.2.2
  · exact inverseWhittakerSet_eq_of_surjective_of_whittakerType ψ
      ((isOfWhittakerType_standard_iff_inverse ψ _).mp hη) g hg
      (isOfInverseWhittakerType_of_isGeneric F hσ).exists_ne_zero

end Langlands.RankinSelberg
