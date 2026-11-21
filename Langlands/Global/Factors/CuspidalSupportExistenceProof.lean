import Langlands.Automorphic.CuspidalSupportSelectedPeriod
import Langlands.Automorphic.CuspidalLeviUnitaryCoefficients
import Langlands.Global.CuspidalLeviSectionExtraction
import Langlands.Global.CuspidalLeviCoefficientEvaluation

/-! # Cuspidal support for the original irreducible operator subquotient -/

noncomputable section

universe u
open NumberField
open scoped Classical
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Global

open Automorphic ArchimedeanGL FiniteVectors GeneralLinear

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup
attribute [local instance 100] LieRing.ofAssociativeRing

section SelectedPeriod

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)

local notation "n" => r + 1
local notation "B" => (⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ : BlockShape n)
local notation "U" => automorphicOperatorAlgebra F n
local notation "M" => AdelicBlockParabolic.FullLevi F B
local instance exactSupportOperatorRing : Ring U := Subalgebra.toRing U

variable (S : OperatorRealization F (r + 1))

local notation "T" => TranslatedBlockConstantTerms F B S
local notation "α" => translatedBlockTermOperatorAction F B S
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S
local notation "P" => translatedBlockLeviRestriction F B S

variable {C : Type*} [AddCommGroup C] [Module ℂ C]
  (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ C)
  (a : C →ₗ[ℂ] TranslatedBlockConstantTerms F ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ S)

local notation "ρc" => (AlgHom.toMonoidHom' A).comp (compactOperator F n)
local notation "ρf" => (AlgHom.toMonoidHom' A).comp (finiteOperator F n)
local notation "L" => operatorAlgebraComplexLieAction A

set_option maxHeartbeats 1000000 in
private theorem finiteInduction_of_unitaryCoefficients
    (ha : ∀ (b : U) (w : C), a (A b w) = α b (a w))
    (ha_inj : Function.Injective a)
    (Q : IrreducibleOperatorSubquotient F r)
    (q : Representation.IntertwiningMap (AlgHom.toMonoidHom' A) Q.representation)
    (hq : Function.Surjective q)
    (w₀ : C) (hw₀ : orbitSpan (AlgHom.toMonoidHom' A) w₀ = ⊤)
    (hκ : ∀ w : C, IsFiniteVector ρc w) (hρ : IsSmooth ρf) (hderiv : CompactDualDerivative ρc L)
    (χ : (Fin k → Ideles F) →ₜ* ℂˣ)
    (hη : ∀ (w : C) (z : Fin k → Ideles F),
      translatedFunctionAction β φ z (a w) = (χ z : ℂ) • a w)
    (hprincipal : ∀ a : Fin k → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1)
    (href : ∀ (w : S.Space) (t : Finset (Fin r)), (B).cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (@standardBlockWeight (r + 1) t) (S.ambient w) = 0) :
    ∃ T₀ : ∀ i, CuspidalOperatorRealization F (m i),
      FiniteParametrizedBlockInduction.HasSubquotient B
        (fun i => (T₀ i).realization.finiteRepresentation) Q.subquotient.finiteRepresentation := by
  let ω := blockTermHeckeCharacter F B χ hprincipal
  let W := cuspidalLeviUnitaryRealization F B ω
  let μ₀ := cuspidalLeviUnitarizingTwist F B ω
  let ν := fun i => (μ₀ i)⁻¹
  let : ∀ i : Fin k, AddCommGroup (W i).Space := fun _ => Submodule.addCommGroup _
  let V := PiTensorProduct ℂ (fun i : Fin k => (W i).Space)
  let tensorGroup : AddCommGroup V := PiTensorProduct.instAddCommGroup
  let : Zero V := ⟨tensorGroup.zero⟩
  let D : ∀ i, CuspidalOperatorDirectSum (W i) := fun i =>
    cuspidalOperatorDirectSumOfUnitaryCentralCharacter (W i)
      (cuspidalLeviUnitaryRealization_isCuspidal F B ω i)
      (cuspidalLeviUnitaryCharacter F B ω i) (cuspidalLeviUnitaryCharacter_isUnitary F B ω i)
      (cuspidalLeviUnitaryRealization_hasCentralCharacter F B ω i)
  obtain ⟨g, hg, hblock⟩ := exists_unitaryCuspidalLeviCoefficients F B ω S a A ha hκ
    χ.toMonoidHom hη (blockTermHeckeCharacter_onIdeles F B χ hprincipal) href
  let e : ∀ i, (W i).Space →ₗ[ℂ] (AdelicGL F (m i + 1) → ℂ) :=
    fun i => operatorRealizationFunctionEvaluation (W i)
  have he (w : C) (b : M) : functionTensorEvaluation e (g w) b =
      cuspidalLeviDeterminantWeight μ₀ b * P (a w) b := hg w b
  have hz (w : C) : g w = 0 ↔ P (a w) = 0 :=
    cuspidalLeviCoefficient_eq_zero_iff hm W μ₀ (g w) (P (a w)) (he w)
  have hkill (w : C) (hw : ∀ l d, g (ρc l (ρf d w)) = 0) : q w = 0 := by
    have hw₀ : a w = 0 := by
      apply translatedBlockTerm_zero_of_compact_finite_restrictions F B S (a w)
      intro l d
      have hc : a (ρc l (ρf d w)) = α (compactOperator F n l) (α (finiteOperator F n d) (a w)) :=
        (ha (compactOperator F n l) _).trans
          (congrArg (α (compactOperator F n l)) (ha (finiteOperator F n d) w))
      exact (congrArg P hc).symm.trans ((hz _).mp (hw l d))
    have hw' : w = 0 := ha_inj (hw₀.trans a.map_zero.symm)
    exact (congrArg q hw').trans q.toLinearMap.map_zero
  have hcov (p : AdelicBlockParabolic.Finite F B) (w : C) :
      g (ρf p.val w) = cuspidalLeviRestoringScalar hm ν p •
        (B).blockTensor (fun i => (W i).finiteRepresentation)
          ((B).leviProjection (FiniteAdeles F) p) (g w) := by
    let d := (B).leviProjection (FiniteAdeles F) p
    let b : M := fun i => AdelicGL.ofFinite F (m i + 1) (d i)
    have hc : cuspidalLeviRestoringScalar hm ν p * cuspidalLeviDeterminantWeight μ₀ b = 1 :=
      cuspidalLeviDeterminantWeight_inv_mul hm μ₀ b
    refine cuspidalLeviCoefficient_finiteCovariance hm W μ₀ d
      (cuspidalLeviRestoringScalar hm ν p) (g w) (g (ρf p.val w)) (P (a w)) hc (he w) ?_
    intro x
    calc
      _ = cuspidalLeviDeterminantWeight μ₀ x * P (a (ρf p.val w)) x := he _ x
      _ = cuspidalLeviDeterminantWeight μ₀ x *
          P (α (finiteOperator F n p.val) (a w)) x :=
        congrArg (fun y : T => cuspidalLeviDeterminantWeight μ₀ x * P y x) (ha (finiteOperator F n p.val) w)
      _ = _ := congrArg (cuspidalLeviDeterminantWeight μ₀ x * ·)
        (translatedBlockLeviRestriction_finiteParabolic F B S p (a w) x)
  have hupper (X : RealLieAlgebra F n) (w : C) (hX : IsStrictUpperBlockLie F B X) :
      g (L (complexify F n X) w) = 0 := by
    let b := differentialOperator F n (envelopingGenerator F n (complexify F n X))
    change g (A b w) = 0
    exact (hz (A b w)).mpr
      ((congrArg P (ha b w)).trans (translatedBlockLeviRestriction_strictUpper F B S X hX (a w)))
  exact exists_finiteParametrizedSubquotient_of_cuspidalLeviCoefficients hm ν A W D q hq w₀
    hw₀ (hκ w₀) hρ hderiv g hkill hcov hupper hblock

end SelectedPeriod

section Transfer

local instance finalProofTransferOperatorRing (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    Ring (automorphicOperatorAlgebra F n) :=
  Subalgebra.toRing _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n) {C : Type*} [AddCommGroup C] [Module ℂ C]
  (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ C)

local notation "T" => TranslatedBlockConstantTerms F B S
local notation "α" => translatedBlockTermOperatorAction F B S
local notation "ρc" => (AlgHom.toMonoidHom' A).comp (compactOperator F n)
local notation "ρf" => (AlgHom.toMonoidHom' A).comp (finiteOperator F n)
local notation "L" => operatorAlgebraComplexLieAction A

variable (j : Representation.IntertwiningMap (AlgHom.toMonoidHom' A)
  (AlgHom.toMonoidHom' (translatedBlockTermOperatorAction F B S)))

private def finiteInclusionOfTranslatedPeriod :
    Representation.IntertwiningMap ρf (translatedBlockTermFiniteAction F B S) where
  toLinearMap := j.toLinearMap
  isIntertwining' d := j.isIntertwining' (finiteOperator F n d)

private def compactInclusionOfTranslatedPeriod :
    Representation.IntertwiningMap ρc (translatedBlockTermCompactAction F B S) where
  toLinearMap := j.toLinearMap
  isIntertwining' k := j.isIntertwining' (compactOperator F n k)

set_option maxHeartbeats 700000 in
private theorem regularity_of_translatedPeriodInclusion (hj : Function.Injective j) :
    (∀ w : C, IsFiniteVector ρc w) ∧ IsSmooth ρf ∧ CompactDualDerivative ρc L := by
  let j₁ := finiteInclusionOfTranslatedPeriod B S A j
  let j₂ := compactInclusionOfTranslatedPeriod B S A j
  refine ⟨fun w => (isFiniteVector_map_iff j₂ hj w).mp (translatedBlockTerm_compactFinite F B S (j w)),
    isSmooth_of_injective j₁ hj (translatedBlockTerm_finiteSmooth F B S), ?_⟩
  refine CompactDualDerivative.of_injective_intertwiner (translatedBlockTermCompactAction F B S)
    (translatedBlockTermComplexLieAction F B S) (translatedBlockTerm_compactDualDerivative F B S) j₂ hj ?_
  intro X w
  exact Representation.IntertwiningMap.isIntertwining _ _ j
    (differentialOperator F n (envelopingGenerator F n X)) w

end Transfer

private theorem cyclicInclusion_eigen {I R V : Type*} [Monoid I] [Ring R] [Algebra ℂ R]
    [AddCommGroup V] [Module ℂ V] (D : R →ₐ[ℂ] Module.End ℂ V) (σ : Representation ℂ I V)
    (hD : ∀ i a, Commute (σ i) (D a)) (χ : I →* ℂˣ)
    (v : Representation.asModule (AlgHom.toMonoidHom' D)) (hv : ∀ i, σ i v = (χ i : ℂ) • v)
    (w : (cyclicAlgebraSubrepresentation D v).toSubmodule) (i : I) :
    σ i (cyclicAlgebraInclusion D v w) = (χ i : ℂ) • cyclicAlgebraInclusion D v w := by
  obtain ⟨a, ha⟩ := exists_cyclicAlgebraAction_generator D v w
  have h : D a v = cyclicAlgebraInclusion D v w := congrArg Subtype.val ha
  calc
    _ = σ i (D a v) := congrArg (σ i) h.symm
    _ = D a (σ i v) := LinearMap.congr_fun (hD i a).eq v
    _ = D a ((χ i : ℂ) • v) := congrArg (D a) (hv i)
    _ = (χ i : ℂ) • D a v := (D a).map_smul _ _
    _ = _ := congrArg ((χ i : ℂ) • ·) h

set_option maxHeartbeats 700000 in
/-- The existence direction of Langlands's cuspidal support theorem at the finite places. -/
theorem cuspidalSupportExistence : CuspidalSupportExistenceStatement.{u} := by
  intro F _ _ _ r Q
  obtain ⟨k, m, hm, S, v, χ, q, hq, hχ, hprincipal, href⟩ := exists_cuspidalSupportSelectedPeriod F Q
  let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  let U := automorphicOperatorAlgebra F (r + 1)
  let : Ring U := Subalgebra.toRing U
  let T := TranslatedBlockConstantTerms F B S
  let α : U →ₐ[ℂ] Module.End ℂ T := translatedBlockTermOperatorAction F B S
  let C := (cyclicAlgebraSubrepresentation (R := U) (V := T) α v).toSubmodule
  let A : U →ₐ[ℂ] Module.End ℂ C := cyclicAlgebraAction (R := U) (V := T) α v
  let j := cyclicAlgebraInclusion (R := U) (V := T) α v
  have hj : Function.Injective j := Subtype.val_injective
  have ha (b : U) (w : C) : j.toLinearMap (A b w) = α b (j.toLinearMap w) := by
    exact Representation.IntertwiningMap.isIntertwining _ _ j b w
  obtain ⟨hκ, hρ, hderiv⟩ := regularity_of_translatedPeriodInclusion B S A j hj
  let σ := translatedFunctionAction (blockConstantTermScalarAction F B) (realizedBlockConstantTerm F B S)
  have hη (w : C) (z : Fin k → Ideles F) : σ z (j w) = (χ z : ℂ) • j w :=
    cyclicInclusion_eigen (R := U) (V := T) α σ
      (translatedBlockTermCenterAction_commute F B S) χ.toMonoidHom v hχ w z
  let w₀ := cyclicAlgebraGenerator (R := U) (V := T) α v
  have hw₀ : orbitSpan (AlgHom.toMonoidHom' A) w₀ = ⊤ :=
    cyclicAlgebraGenerator_orbitSpan (R := U) (V := T) α v
  obtain ⟨T₀, hT⟩ := finiteInduction_of_unitaryCoefficients hm S A j.toLinearMap ha hj Q q hq
    w₀ hw₀ hκ hρ hderiv χ hη hprincipal href
  obtain ⟨P, hP, hQ⟩ := exists_finiteInducedConstituent_of_parametrizedInduction hm Q hT
  exact ⟨k, m, hm, T₀, P, hP, hQ⟩

end Langlands.Global
