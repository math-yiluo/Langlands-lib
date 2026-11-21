import Langlands.Global.RankinSelberg.EqualFiniteWhittakerTests
import Langlands.Global.RankinSelberg.EqualIntegrandProducts
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction
import Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockIntegrationProof
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Representation.Whittaker.RectangularSupport

/-! # Finite unequal-rank Whittaker tests

Over a p-adic field, nonzero Whittaker functionals on representations of Whittaker type of
`GL_(r+1)` and `GL_(t+1)`, `t < r`, extend to `PadicUnequalTestData` whose two local integrals
`Ψ(s; W, W')` and `Ψ(s; ρ(w_(n,m)) W̃, W̃')` are nonzero arbitrarily far right; the two local
integrals are the integrals of the integrands of the Library's `ArchimedeanLocal` definitions;
and on the finite factors of the cuspidal presentations the test data are realized by factor
vectors. See the paired Markdown.
-/

noncomputable section
universe u uQ uK uV uW
open MeasureTheory Langlands.RankinSelberg Langlands.HarmonicAnalysis
open Langlands.Whittaker Langlands.GeneralLinear Langlands.QuotientIntegration
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.UnequalFiniteWhittakerTests

section Matrices

variable {K : Type uK} [Field K]

/-- The block-zero matrix of JPSS is `diag(g, 1)`. -/
theorem blockMatrixAt_zero_eq_padGL {r t : ℕ} (h : t < r) (k : ℕ) (hr : r = t + (0 + k + 1))
    (g : Langlands.GeneralLinear (t + 1) K) (X : Matrix (Fin 0) (Fin (t + 1)) K) :
    AdjacentBlockReduction.blockMatrixAt 0 k hr g X =
      padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g := by
  apply Units.ext
  ext a b
  rw [AdjacentBlockReduction.blockMatrixAt_entry, UnequalAnalytic.padGL_apply,
    dite_eq_right (show ¬(t + 1 ≤ (a : ℕ) ∧ (a : ℕ) < t + 1 + 0) by omega), add_zero]
  by_cases ha : (a : ℕ) < t + 1
  · by_cases hb : (b : ℕ) < t + 1
    · rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left ⟨ha, hb⟩]
    · have hab : a ≠ b := fun e => hb (by subst e; exact ha)
      rw [dite_eq_left ha, dite_eq_right hb, dite_eq_right (fun x => hb x.2),
        Matrix.one_apply_ne hab]
  · rw [dite_eq_right ha, dite_eq_right (fun x => ha x.1), Matrix.one_apply]

/-- The block-`(r-t-1)` matrix of JPSS is the rectangular point. -/
theorem blockMatrixAt_rows_eq_rectangularPoint {r t : ℕ} (h : t < r)
    (hr : r = t + ((r - t - 1) + 0 + 1))
    (g : Langlands.GeneralLinear (t + 1) K) (X : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) K) :
    AdjacentBlockReduction.blockMatrixAt (r - t - 1) 0 hr g X =
      ArchimedeanLocal.rectangularPoint h g X := by
  apply Units.ext
  ext a b
  rw [AdjacentBlockReduction.blockMatrixAt_entry]
  change _ = RectangularSupport.rectGL h g X a b
  rw [RectangularSupport.rectGL_apply]
  by_cases hb : (b : ℕ) < t + 1
  · by_cases ha : (a : ℕ) < t + 1
    · rw [dite_eq_right (show ¬(t + 1 ≤ (a : ℕ) ∧ (a : ℕ) < t + 1 + (r - t - 1)) by omega)]
      simp [ha, hb]
    · by_cases ha' : (a : ℕ) < r
      · simp only [ha, hb, ha', dite_true, dite_false,
          show t + 1 ≤ (a : ℕ) ∧ (a : ℕ) < t + 1 + (r - t - 1) by omega]
        have hab : a ≠ b := fun e => ha (e ▸ hb)
        simp [hab]
      · have hab : a ≠ b := fun e => ha (e ▸ hb)
        simp only [ha, hb, ha', dite_true, dite_false, hab, ite_false,
          show ¬(t + 1 ≤ (a : ℕ) ∧ (a : ℕ) < t + 1 + (r - t - 1)) by omega, add_zero]
  · by_cases ha : (a : ℕ) < t + 1
    · have hab : a ≠ b := fun e => hb (e ▸ ha)
      simp [ha, hb, hab]
    · simp only [ha, hb, dite_false]
      by_cases ha' : t + 1 ≤ (a : ℕ) ∧ (a : ℕ) < t + 1 + (r - t - 1)
      · simp [ha']
      · simp

/-- `diag(1, w)` written with two equal sizes of the antidiagonal block. -/
theorem reindex_blockSum_weylLong_congr {m a b N : ℕ} (hab : a = b) (h₁ : m + a = N)
    (h₂ : m + b = N) :
    GeneralLinear.reindex (finCongr h₁)
        (GeneralLinear.blockSum ((1 : Langlands.GeneralLinear m K), weylLong a K)) =
      GeneralLinear.reindex (finCongr h₂)
        (GeneralLinear.blockSum ((1 : Langlands.GeneralLinear m K), weylLong b K)) := by
  subst hab
  rfl

/-- The block Weyl element of the local functional equation is `unfoldingWeyl`. -/
theorem blockWeylAt_eq_unfoldingWeyl {r t : ℕ} (h : t < r) :
    (blockWeylAt t r h : Langlands.GeneralLinear (r + 1) K) = ArchimedeanLocal.unfoldingWeyl h :=
  reindex_blockSum_weylLong_congr (by omega) _ _

end Matrices

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance : MeasurableSpace K.Carrier := borel K.Carrier
local instance : BorelSpace K.Carrier := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := borel _
local instance (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r K.Carrier) := ⟨rfl⟩

/-- **Nonvanishing p-adic unequal-rank test data.** For nonzero Whittaker functionals there are
test data with these functionals whose ordinary and dual integrals are nonzero arbitrarily far
right. -/
theorem padicUnequalNonvanishingTest (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (ν : Correspondence.LocalAdditiveHaarMeasure K) (hν : Correspondence.IsSelfDualMeasure K ψ ν)
    {r t : ℕ} (h : t < r) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) K.Carrier) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType t (inverseStandardCharacter ψ t) σ)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ t σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    ∃ D : PadicUnequalTestData K ψ π σ, D.functional = ℓ ∧ D.inverseFunctional = ℓ' ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.integral h ν s ≠ 0) ∧
      ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.dualIntegral h ν s ≠ 0 := by
  have hμ := unipotentQuotientHaar_isCompatible K.Carrier t
  obtain ⟨ζ, c, m, P, Pd, -, hall⟩ :=
    unequalRankFunctionalEquation K K.canonicalTopologicalData t r h ψ
      (unipotentQuotientHaar K.Carrier t) hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨hP, -, hFE⟩ := hall 0 (r - t - 1) (by omega)
  obtain ⟨R, hRmem, hR0⟩ := hP.exists_ne_zero
  rw [unequalRankValuesAt_eq] at hRmem
  obtain ⟨f, f', hfR⟩ := hRmem
  obtain ⟨R₂, Rd, hR₂, hRd, hN⟩ := hFE f f'
  have hq := K.canonicalTopologicalData.residueCardinality_gt_one
  have hRR : R₂ = R := hR₂.unique hq hfR
  subst hRR
  have hRd0 : Rd ≠ 0 :=
    EqualNonvanishing.dual_ne_zero_of_normalized hq hP.polynomial_ne_zero hR0 hN
  let D : PadicUnequalTestData K ψ π σ :=
    ⟨inferInstance, unipotentQuotientHaar K.Carrier t, hμ, ℓ, hℓ, ℓ', hℓ', f, f'⟩
  refine ⟨D, rfl, rfl, ?_, ?_⟩
  · exact EqualNonvanishing.nonvanishing_on_right_of_rational hq hR0 hR₂
  · exact EqualNonvanishing.nonvanishing_on_right_of_rational hq hRd0 hRd

variable {K}
variable {ψ : Correspondence.NontrivialAdditiveCharacter K} {r t : ℕ}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) K.Carrier) W}

/-- The ordinary local integrand of p-adic test data, in the `ArchimedeanLocal` form. -/
def testIntegrand (h : t < r) (D : PadicUnequalTestData K ψ π σ) (s : ℂ) :
    LeftUnipotentQuotient t K.Carrier → ℂ :=
  ArchimedeanLocal.unequalIntegrand (normalizedAbsoluteValue K.canonicalTopologicalData) h
    D.vector.val.val D.inverseVector.val.val s

/-- The dual local block kernel of p-adic test data, in the `ArchimedeanLocal` form. -/
def testDualKernel (h : t < r) (D : PadicUnequalTestData K ψ π σ) (s : ℂ) :
    LeftUnipotentQuotient t K.Carrier × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) K.Carrier → ℂ :=
  fun p => ArchimedeanLocal.blockKernel (normalizedAbsoluteValue K.canonicalTopologicalData) h
    (ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h)
      (ArchimedeanLocal.dualFunction (r + 1) D.vector.val.val))
    (ArchimedeanLocal.dualFunction (t + 1) D.inverseVector.val.val) s p.1 p.2

/-- The ordinary local integrand integrates to the ordinary integral of the data. -/
theorem testIntegrand_integral (h : t < r) (ν : Correspondence.LocalAdditiveHaarMeasure K)
    (D : PadicUnequalTestData K ψ π σ) (s : ℂ) :
    padicQuotientIntegral K D.quotientMeasure (testIntegrand h D s) = D.integral h ν s := by
  change (∫ q, testIntegrand h D s q ∂D.measure) =
    unequalRankIntegralAt 0 (r - t - 1) (by omega) ψ
      (normalizedAbsoluteValue K.canonicalTopologicalData) D.measure
      (rectangularMeasure ν 0 (t + 1)) D.vector.val D.inverseVector.val s
  rw [AdjacentBlockReduction.unequalRankIntegralAt_eq_outer]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have hk : ((0 + (r - t - 1) + 1 : ℕ) : ℂ) = ((r - t : ℕ) : ℂ) := by
    congr 1
    omega
  simp only [rectangularMeasure_zero_rows, integral_dirac, blockMatrixAt_zero_eq_padGL h,
    EqualIntegrandProducts.determinantWeight_eq_detPower, hk]
  rfl

/-- The dual local block kernel integrates to the dual integral of the data. -/
theorem testDualKernel_integral (h : t < r) (ν : Correspondence.LocalAdditiveHaarMeasure K)
    (D : PadicUnequalTestData K ψ π σ) (s : ℂ) :
    padicBlockIntegral K (r - (t + 1)) D.quotientMeasure ν (testDualKernel h D s) =
      D.dualIntegral h ν s := by
  change (∫ q, (∫ x, testDualKernel h D s (q, x) ∂rectangularMeasure ν (r - (t + 1)) (t + 1))
      ∂D.measure) =
    unequalRankIntegralAt (r - t - 1) 0 (by omega) (ψ.scale (-1))
      (normalizedAbsoluteValue K.canonicalTopologicalData) D.measure
      (rectangularMeasure ν (r - t - 1) (t + 1))
      (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r D.vector.val)
        (blockWeylAt t r h))
      (secondDualFunction ψ t D.inverseVector.val) s
  rw [AdjacentBlockReduction.unequalRankIntegralAt_eq_outer]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have hk : ((r - t - 1 + 0 + 1 : ℕ) : ℂ) = ((r - t : ℕ) : ℂ) := by
    congr 1
    omega
  simp only [testDualKernel, ArchimedeanLocal.blockKernel]
  rw [integral_mul_const, integral_mul_const,
    EqualIntegrandProducts.determinantWeight_eq_detPower, hk]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [translateWhittaker_apply, firstDualFunction_apply,
    blockMatrixAt_rows_eq_rectangularPoint h, blockWeylAt_eq_unfoldingWeyl h]
  rfl

end Padic

section Presentations

open NumberField Langlands.Automorphic Langlands.Global.CompletionPadic
open Langlands.Global.FiniteAdelicGL Langlands.Global.CuspidalPairFunctionalEquation
open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerModel
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r t : ℕ}

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F (n + 1)) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F (n + 1)) :=
  Submodule.addCommGroup _
local instance {n : ℕ} {v : FinitePlace F} (L : LocalRealization F (n + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

variable {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
variable (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') (v : FinitePlace F)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))

local instance : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology
local instance (n : ℕ) : TopologicalSpace (FiniteLocalGL F (n + 1) v) :=
  (padicField v).canonicalGeneralLinearTopology (n + 1)
local instance : ValuativeRel (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance : MeasurableSpace (padicField v).Carrier := borel (padicField v).Carrier
local instance : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (FiniteLocalGL F (n + 1) v) := borel _
local instance (n : ℕ) : BorelSpace (FiniteLocalGL F (n + 1) v) := ⟨rfl⟩
local instance (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := borel _
local instance (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) :=
  borel _

/-- The test data on the two exact embedded finite components. -/
abbrev TestData : Type u :=
  PadicUnequalTestData (padicField v) ψ (V := (P.localComponent v).Space)
    (W := (P'.localComponent v).Space) (P.localComponent v).representation
    (P'.localComponent v).representation

private theorem component_generic (hP : HasIrreducibleAdmissibleComponents P) :
    Whittaker.IsGeneric ψ r (V := (P.localComponent v).Space)
      (P.localComponent v).representation := by
  have hχ : CuspidalWhittaker.localCharacter F v ≠ 1 := by
    intro he
    obtain ⟨z, hz⟩ := CuspidalWhittaker.exists_localCharacter_ne_one F v
    exact hz (by rw [he, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional (P.localComponent v)
    (P.localComponent_isCuspidal v) (P.localComponent_ne_bot v)
  exact (P.localComponent v).isGeneric_of_integerTrivial_character (hP v).1 (hP v).2
    (CuspidalWhittaker.localCharacter F v) hχ
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one F hx) ℓ hℓ heq ψ

/-- Both right-half-plane nonvanishing clauses on the actual finite components. -/
theorem exists_tests (h : t < r) (hP : HasIrreducibleAdmissibleComponents P)
    (hP' : HasIrreducibleAdmissibleComponents P')
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (hν : Correspondence.IsSelfDualMeasure (padicField v) ψ ν) :
    ∃ D : TestData P P' v ψ,
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.integral h ν s ≠ 0) ∧
      ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ D.dualIntegral h ν s ≠ 0 := by
  have hgen := component_generic P v ψ hP
  have hgen' := component_generic P' v (ψ.scale (-1)) hP'
  have hW := isOfWhittakerType_of_isGeneric (padicField v) hgen
  have hW' := isOfWhittakerType_of_isGeneric (padicField v) hgen'
  rw [standardCharacter_scale_neg_one] at hW'
  obtain ⟨ℓ, hℓ⟩ := hgen.2.2
  obtain ⟨ℓ', hℓ'⟩ := hgen'.2.2
  obtain ⟨D, _, _, hn, hn'⟩ := padicUnequalNonvanishingTest (padicField v) ψ ν hν h
    (P.localComponent v).Space (P'.localComponent v).Space
    (P.localComponent v).representation (P'.localComponent v).representation
    hW hW' ℓ (functionalsCongr (standardCharacter_scale_neg_one ψ t) ℓ') hℓ hℓ'
  exact ⟨D, hn, hn'⟩

/-- Transport the smaller-rank test functional to the character of the inverse component. -/
def inverseComponentFunctional (D : TestData P P' v ψ) :
    ComponentFunctionals P' v (inverseFinite v ψ) :=
  RankinSelberg.functionalsCongr (EqualFiniteWhittakerTests.inverse_factorCharacter (r := t) v ψ).symm
    D.inverseFunctional

private theorem exists_inverseModelVector (D : TestData P P' v ψ) :
    ∃ f : (Whittaker.coefficientModel (P'.localComponent v).representation
        (inverseComponentFunctional P P' v ψ D)).toSubmodule,
      ∀ g : FiniteLocalGL F (t + 1) v, f.val.val g = D.inverseVector.val.val g := by
  obtain ⟨a, ha⟩ := Whittaker.modelMap_surjective (P'.localComponent v).representation
    D.inverseFunctional D.inverseVector
  refine ⟨Whittaker.modelMap (P'.localComponent v).representation
    (inverseComponentFunctional P P' v ψ D) a, fun g => ?_⟩
  exact congrArg (fun f : (Whittaker.coefficientModel (P'.localComponent v).representation
    D.inverseFunctional).toSubmodule => f.val.val g) ha

/-- Realize the smaller-rank test function on the supplied finite factor exactly. -/
def inverseFactorCoefficient (D : TestData P P' v ψ) :
    EqualFiniteWhittakerTests.FactorCoefficient P' v (inverseFinite v ψ) D.inverseVector.val.val := by
  let h := exists_inverseModelVector P P' v ψ D
  let a := EqualFiniteWhittakerTests.factorCoefficient P' v (inverseFinite v ψ)
    (inverseComponentFunctional P P' v ψ D) D.inverseFunctional_ne_zero (Classical.choose h)
  exact ⟨a.functional, a.reference, a.reference_value, a.vector,
    fun g => (a.coefficient_eq g).trans (Classical.choose_spec h g)⟩

end Presentations

end Langlands.Global.RankinSelbergGlobal.UnequalFiniteWhittakerTests
