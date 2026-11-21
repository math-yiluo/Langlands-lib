import Langlands.Global.Factors.CuspidalPairPoleUnequalAssembly
import Langlands.Global.Factors.CuspidalPairPoleUnequalFiniteProduct
import Langlands.Global.RankinSelberg.UnequalIntegrandProducts

/-! # Covering normalized unequal-rank tests from prescribed archimedean products -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ

open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open NumberField Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal
open RankinSelbergGlobal.FiniteWhittakerPartialDomain
open RankinSelbergGlobal.FiniteWhittakerSemilocal
open RankinSelbergGlobal.UnequalIntegrandProducts
open LocalPointFactorization
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassField.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)
open MeasureTheory

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}
  {LR : {v : InfinitePlace F // v.IsReal} → ℂ → ℂ}
  {LC : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ}

local instance poleUnequalNormalizedSchemeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleUnequalNormalizedSchemeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleUnequalNormalizedRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance poleUnequalNormalizedContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance poleUnequalNormalizedFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance poleUnequalNormalizedAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance poleUnequalNormalizedStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "L∞" => (fun s : ℂ => (∏ v, LR v s) * ∏ w, LC w s)

/-- The local paired products are invariant and their normalized integrals are nonzero at `s₀`. -/
structure PoleUnequalArchimedeanTest (hrt : t < r)
    (LR : RP → ℂ → ℂ) (LC : CP → ℂ → ℂ) (s₀ : ℂ) where
  realLeft : RP → Langlands.GeneralLinear (r + 1) ℝ → ℂ
  realRight : RP → Langlands.GeneralLinear (t + 1) ℝ → ℂ
  complexLeft : CP → Langlands.GeneralLinear (r + 1) ℂ → ℂ
  complexRight : CP → Langlands.GeneralLinear (t + 1) ℂ → ℂ
  realMeasure : RP → ArchimedeanLocal.RealQuotientMeasureData t
  complexMeasure : CP → ArchimedeanLocal.ComplexQuotientMeasureData t
  realNormalization : ∀ v, OrdinaryIntegralNormalization
    (ArchimedeanLocal.realUnequalIntegral hrt (realMeasure v) (realLeft v) (realRight v)) (LR v)
  complexNormalization : ∀ w, OrdinaryIntegralNormalization
    (ArchimedeanLocal.complexUnequalIntegral hrt (complexMeasure w) (complexLeft w) (complexRight w)) (LC w)
  realNonzero : ∀ v, (realNormalization v).value s₀ ≠ 0
  complexNonzero : ∀ w, (complexNormalization w).value s₀ ≠ 0
  realInvariant : let hp := Nat.succ_le_succ hrt.le
    ∀ v (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) g,
      realLeft v (padGL hp (u.val * g)) * realRight v (u.val * g) =
        realLeft v (padGL hp g) * realRight v g
  complexInvariant : let hp := Nat.succ_le_succ hrt.le
    ∀ w (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ) g,
      complexLeft w (padGL hp (u.val * g)) * complexRight w (u.val * g) =
        complexLeft w (padGL hp g) * complexRight w g

section Padic

variable (v : FinitePlace F)
local instance poleUnequalNormalizedPadicTopology : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
local instance poleUnequalNormalizedPadicValuation : ValuativeRel (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.valuativeRel
local instance poleUnequalNormalizedPadicLocalField : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance poleUnequalNormalizedPadicMeasurable : MeasurableSpace (padicField v).Carrier := borel (padicField v).Carrier
local instance poleUnequalNormalizedPadicBorel : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance poleUnequalNormalizedPadicQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) := borel _

private theorem padicIntegral_eq_blockZero {k : ℕ} (hr : r = t + (0 + k + 1)) (hrt : t < r)
    (χ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : LocalFactor.PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData χ)
    (D : PoleFiniteTestVectors v χ P P') (s : ℂ) :
    padicQuotientIntegral (padicField v) (equalPadicQuotientMeasure (padicField v) t)
      (ArchimedeanLocal.unequalIntegrand
        (normalizedAbsoluteValue (padicField v).canonicalTopologicalData) hrt D.left.val D.right.val s) =
      unequalRankIntegralAt 0 k hr χ (normalizedAbsoluteValue (padicField v).canonicalTopologicalData)
        (equalPadicQuotientMeasure (padicField v) t) (rectangularMeasure ν.val 0 (t + 1)) D.left D.right s :=
  unequalIntegral_eq_blockZero hr hrt χ _ _ ν.val D.left D.right s

end Padic

variable {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {hPS : P.exceptional ⊆ S} {hPS' : P'.exceptional ⊆ S}
  {c : FinitePairLChoice P P' hP hP'} {hrt : t < r}

/-- If the archimedean inputs cover every spectral point for each tuple of finite references,
the ordinary global tests can be chosen from actual cuspidal tensors. -/
def HasCoveringUnequalArchimedeanTests (hP : HasIrreducibleAdmissibleComponents P)
    (hP' : HasIrreducibleAdmissibleComponents P') (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (hrt : t < r)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (LR : RP → ℂ → ℂ) (LC : CP → ℂ → ℂ) : Prop :=
  ∀ (D : ∀ v : S, PoleFiniteTestVectors v.1 (ψv v) P P') (s₀ : ℂ),
    ∃ (b : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
      (b' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
      (A : PoleUnequalArchimedeanTest hrt LR LC s₀) (κ : ℂ), κ ≠ 0 ∧
      let hp := Nat.succ_le_succ hrt.le
      let U := cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hP
        (P.finitePure S hPS (fun v => (D v).leftFactor.reference) ⊗ₜ[ℂ] b))
      let U' := cuspWhittaker F T' ψ.complex⁻¹ (P'.allPlaceTensorEquiv hP'
        (P'.finitePure S hPS' (fun v => (D v).rightFactor.reference) ⊗ₜ[ℂ] b'))
      ∀ g ∈ unipotentIntegralOutside F (t + 1) S,
        U (pad F hp (infinitePoint S g)) * U' (infinitePoint S g) = κ *
          ((∏ v, A.realLeft v (padGL hp (realComponent F (t + 1) v g)) *
            A.realRight v (realComponent F (t + 1) v g)) *
          ∏ w, A.complexLeft w (padGL hp (complexComponent F (t + 1) w g)) *
            A.complexRight w (complexComponent F (t + 1) w g))

/-- The prescribed finite tests and the covering archimedean tests give actual global
vectors with a normalized partial integral nonzero at every requested point. -/
theorem nonempty_unequalNormalizedTests_of_archimedean_product
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ν : ∀ v : S, LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v))
    (hA : HasCoveringUnequalArchimedeanTests hP hP' hPS hPS' ψ hrt ψv LR LC) :
    Nonempty (UnequalNormalizedTests.{u, uQ, 0} c hrt S ψ L∞) := by
  have hOne (s₀ : ℂ) : ∃ (x : T.Space) (x' : T'.Space),
      IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
      ∃ N : OrdinaryIntegralNormalization
        (partialUnequalWhittakerIntegral F hrt S (cuspWhittaker F T ψ.complex x)
          (cuspWhittaker F T' ψ.complex⁻¹ x'))
        (fun s => L∞ s * ∏ v ∈ S, c.finiteL v s), N.value s₀ ≠ 0 := by
    let k := r - (t + 1)
    have hr : r = t + (0 + k + 1) := by dsimp [k]; omega
    choose D NS hNS _ using fun v : S => exists_poleFiniteUnequalTest v.1 (ψv v) c (ν v) hr hT hT' s₀
    obtain ⟨bInf, bInf', A, κ, hκ, hArch⟩ := hA D s₀
    let a (v : S) := (D v).leftFactor.vector
    let a' (v : S) := (D v).rightFactor.vector
    let x := P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] bInf)
    let x' := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] bInf')
    let W := cuspWhittaker F T ψ.complex x
    let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
    let hp := Nat.succ_le_succ hrt.le
    have hf := hasOrdinaryUnequalFiniteProduct hrt hP hP' hPS hPS' ψ hψF hψv D bInf bInf'
    dsimp only [HasOrdinaryUnequalFiniteProduct] at hf
    have hW (g : Points F (t + 1)) (hg : g ∈ unipotentIntegralOutside F (t + 1) S) :
        W (pad F hp g) * W' g = κ *
          ((∏ v, A.realLeft v (padGL hp (realComponent F (t + 1) v g)) * A.realRight v (realComponent F (t + 1) v g)) *
          (∏ w, A.complexLeft w (padGL hp (complexComponent F (t + 1) w g)) * A.complexRight w (complexComponent F (t + 1) w g)) *
          ∏ v : S, (D v).left.val (padGL hp (finiteComponent F (t + 1) v.1 g)) *
            (D v).right.val (finiteComponent F (t + 1) v.1 g)) :=
      (hf g hg).trans ((congrArg (fun z : ℂ => z * _) (hArch g hg)).trans (mul_assoc _ _ _))
    have hpoint := pairedWhittakerIntegrandProduct F hrt S κ W W'
      A.realLeft A.realRight A.complexLeft A.complexRight
      (fun v => (D v).left.val) (fun v => (D v).right.val)
      A.realInvariant A.complexInvariant
      (fun v => by
        let _ : TopologicalSpace (padicField v.1).Carrier := (padicField v.1).canonicalTopologicalData.topology
        exact unequalPair_invariant hr (ψv v) (D v).left (D v).right hrt) hW
    let fS (v : S) := ArchimedeanLocal.unequalIntegrand
      (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData) hrt (D v).left.val (D v).right.val
    let NS' (v : S) : OrdinaryIntegralNormalization
        (fun s => padicQuotientIntegral (padicField v.1) (equalPadicQuotientMeasure (padicField v.1) t) (fS v s))
        (c.finiteL v.1) :=
      ⟨(NS v).value, (NS v).analytic, by
        obtain ⟨b, hb⟩ := (NS v).eq_on_right
        exact ⟨b, fun s hs => (padicIntegral_eq_blockZero v.1 hr hrt (ψv v) (ν v) (D v) s).trans (hb s hs)⟩⟩
    obtain ⟨C, hC, N, hN⟩ := exists_normalization_of_semilocal_pointwise_product
      A.realMeasure A.complexMeasure (fun v => equalPadicQuotientMeasure (padicField v.1) t)
      (fun v => equalPadicQuotientMeasure_isCompatible (padicField v.1) t)
      (unequalWhittakerIntegrand F hrt W W') hκ
      (fun v => ArchimedeanLocal.realUnequalIntegrand hrt (A.realLeft v) (A.realRight v))
      (fun w => ArchimedeanLocal.complexUnequalIntegrand hrt (A.complexLeft w) (A.complexRight w))
      fS ⟨0, fun s _ q hq => hpoint s q hq⟩ A.realNormalization A.complexNormalization NS'
    refine ⟨x, x', P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS a bInf,
      P'.allPlaceTensorEquiv_finitePure_sphericalOutside hP' S hPS' a' bInf',
      ⟨N.value, N.analytic, ?_⟩, ?_⟩
    · obtain ⟨b, hb⟩ := N.eq_on_right
      refine ⟨b, fun s hs => ?_⟩
      rw [partialUnequalWhittakerIntegral_eq_setIntegral, hb s hs]
      exact congrArg (fun a : ℂ => N.value s * (L∞ s * a))
        (Finset.prod_coe_sort S (fun v => c.finiteL v s))
    · change N.value s₀ ≠ 0
      rw [hN]
      exact mul_ne_zero hC (mul_ne_zero
        (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => A.realNonzero v)
          (Finset.prod_ne_zero_iff.mpr fun w _ => A.complexNonzero w))
        (Finset.prod_ne_zero_iff.mpr fun v _ => hNS v))
  choose x x' hx hx' N hN using hOne
  refine ⟨⟨ℂ, x, x', hx, hx', fun i => (N i).value, fun i => (N i).analytic,
    fun s => ⟨s, hN s⟩, fun i => ?_⟩⟩
  obtain ⟨b, hb⟩ := (N i).eq_on_right
  exact ⟨b, fun s hs => (hb s hs).trans (mul_assoc _ _ _).symm⟩

end Langlands.Global.CuspidalPairPoles
