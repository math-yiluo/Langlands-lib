import Langlands.Global.Factors.CuspidalPairPoleFiniteTestVectors
import Langlands.Global.RankinSelberg.InfiniteWhittakerPrescribedProduct
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Global.RankinSelberg.EqualIntegrandProducts
import Langlands.Global.RankinSelberg.ArchimedeanEqualTestAssembly

/-! # Ordinary normalization for prescribed pure equal-rank tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

open NumberField MeasureTheory
open scoped Classical TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelberg RankinSelbergGlobal ArchimedeanLocal
open HarmonicAnalysis (UnitaryAdditiveCharacter)
open FiniteWhittakerSemilocal FiniteWhittakerDual InfiniteWhittakerSlice EqualIntegrandProducts EqualSchwartzTensor
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel archimedeanRealGLMeasurable
  archimedeanRealGLBorel archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanComplexNMeasurable archimedeanComplexNBorel

variable {F : Type u} [Field F] [NumberField F] {r : ℕ} {S : Finset (FinitePlace F)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance poleEqualProductSchemeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleEqualProductSchemeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleEqualProductRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualProductContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualProductFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualProductAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleEqualProductStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- The pure global Schwartz test with the specified retained factors. -/
def poleEqualSchwartzTensor
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1) : RowVector F (r + 1) → ℂ :=
  restrictedTensor F (r + 1) S ΦR ΦC (extendFiniteRowTests F (r + 1) S ΦS)

/-- The pure test is Schwartz–Bruhat and standard outside the chosen finite set. -/
theorem poleEqualSchwartzTensor_spec
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1) :
    poleEqualSchwartzTensor (F := F) (r := r) (S := S) ΦR ΦC ΦS ∈ schwartzBruhat F (r + 1) ∧
      IsStandardOutside F (r + 1) S (poleEqualSchwartzTensor ΦR ΦC ΦS) :=
  ⟨restrictedTensor_mem_schwartzBruhat F (r + 1) S ΦR ΦC _ (extendFiniteRowTests_test F (r + 1) S ΦS),
    restrictedTensor_isStandardOutside F (r + 1) S ΦR ΦC _⟩

private theorem poleEqualSchwartzTensor_eq
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1) :
    poleEqualSchwartzTensor (F := F) (r := r) (S := S) ΦR ΦC ΦS =
      (integralOutside F (r + 1) S).indicator fun y : RowVector F (r + 1) =>
      (∏ v : RP, ΦR v (realRowCoordinates F (r + 1) v y)) *
      (∏ w : CP, ΦC w (complexRowCoordinates F (r + 1) w y)) *
      ∏ v : S, ΦS v (localCoordinates F (r + 1) v.1 y) := by
  simpa only [poleEqualSchwartzTensor, extendFiniteRowTests_apply] using
    restrictedTensor_eq F (r + 1) S ΦR ΦC (extendFiniteRowTests F (r + 1) S ΦS)

variable [CompactSpace (AdeleQuotient F)] {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' hP hP'} {hPS : P.exceptional ⊆ S} {hPS' : P'.exceptional ⊆ S}
  {ψ : UnitaryAdditiveCharacter (Adeles F)}
  {ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)}

section Padic

variable (v : FinitePlace F)
local instance poleEqualPadicTopology : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
local instance poleEqualPadicMeasurable : MeasurableSpace (padicField v).Carrier := borel _
local instance poleEqualPadicQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient r (padicField v).Carrier) := borel _

/-- The ordinary equal local integral on the prescribed finite pair and row test. -/
def poleEqualFiniteIntegral (χ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (D : PoleFiniteTestVectors v χ P P') (Φ : finiteRowTest F (r + 1) v) : ℂ → ℂ :=
  equalRankIntegral χ (normalizedAbsoluteValue (padicField v).canonicalTopologicalData)
    (equalPadicQuotientMeasure (padicField v) r) D.left D.right Φ

end Padic

/-- Normalize the partial equal-rank integral of specified pure tests. The value of the
normalization is the product of the supplied local values times a fixed nonzero scalar. -/
theorem exists_ordinaryEqualNormalization_of_pure_product
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (D : ∀ v : S, PoleFiniteTestVectors v.1 (ψv v) P P')
    (b : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (b' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
    (WR WR' : RP → GeneralLinear (r + 1) ℝ → ℂ)
    (WC WC' : CP → GeneralLinear (r + 1) ℂ → ℂ)
    (ΦR : RP → SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ΦC : CP → SchwartzMap (Fin (r + 1) → ℂ) ℂ) (ΦS : ∀ v : S, finiteRowTest F (r + 1) v.1)
    (DR : RP → RealQuotientMeasureData r) (DC : CP → ComplexQuotientMeasureData r)
    (LR : RP → ℂ → ℂ) (LC : CP → ℂ → ℂ)
    {κ κ' : ℂ} (hκ : κ ≠ 0) (hκ' : κ' ≠ 0)
    (hR : ∀ v (u : GeneralLinear.upperUnipotent (r + 1) ℝ) g,
      WR v (u.val * g) * WR' v (u.val * g) = WR v g * WR' v g)
    (hC : ∀ w (u : GeneralLinear.upperUnipotent (r + 1) ℂ) g,
      WC w (u.val * g) * WC' w (u.val * g) = WC w g * WC' w g)
    (hInf : HasPrescribedInfiniteWhittakerProduct
      (infiniteResidual S P hP hPS ψ.complex (fun v => (D v).leftFactor.reference) b) κ WR WC)
    (hInf' : HasPrescribedInfiniteWhittakerProduct
      (infiniteResidual S P' hP' hPS' ψ.complex⁻¹ (fun v => (D v).rightFactor.reference) b') κ' WR' WC')
    (NR : ∀ v, OrdinaryIntegralNormalization (realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v)) (LR v))
    (NC : ∀ w, OrdinaryIntegralNormalization (complexEqualIntegral (DC w) (WC w) (WC' w) (ΦC w)) (LC w))
    (NS : ∀ v : S, OrdinaryIntegralNormalization (poleEqualFiniteIntegral v.1 (ψv v) (D v) (ΦS v)) (c.finiteL v.1)) :
    let x := P.allPlaceTensorEquiv hP (P.finitePure S hPS (fun v => (D v).leftFactor.vector) ⊗ₜ[ℂ] b)
    let x' := P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' (fun v => (D v).rightFactor.vector) ⊗ₜ[ℂ] b')
    let Φ := poleEqualSchwartzTensor ΦR ΦC ΦS
    ∃ C : ℂ, C ≠ 0 ∧ ∃ N : OrdinaryIntegralNormalization
      (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex x)
        (cuspWhittaker F T' ψ.complex⁻¹ x') Φ)
      (fun s => ((∏ v, LR v s) * ∏ w, LC w s) * ∏ v ∈ S, c.finiteL v s),
      ∀ s, N.value s = C * (((∏ v, (NR v).value s) * ∏ w, (NC w).value s) * ∏ v : S, (NS v).value s) := by
  intro x x' Φ
  let W := cuspWhittaker F T ψ.complex x
  let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
  let ℓ (v : S) := (D v).leftFactor.functional
  let ℓ' (v : S) := (D v).rightFactor.functional
  let a₀ (v : S) := (D v).leftFactor.reference
  let a₀' (v : S) := (D v).rightFactor.reference
  let a (v : S) := (D v).leftFactor.vector
  let a' (v : S) := (D v).rightFactor.vector
  let WS (v : S) := (D v).left.val
  let WS' (v : S) := (D v).right.val
  have hpair (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
      W g * W' g = (κ * κ') *
        (((∏ v, WR v (realComponent F (r + 1) v g) * WR' v (realComponent F (r + 1) v g)) *
          ∏ w, WC w (complexComponent F (r + 1) w g) * WC' w (complexComponent F (r + 1) w g)) *
          ∏ v : S, WS v (finiteComponent F (r + 1) v.1 g) * WS' v (finiteComponent F (r + 1) v.1 g)) := by
    have hf := pair_eq_product S P hP hPS T' P' hP' hPS' ψ hψF ψv hψv ℓ ℓ' a₀
      (fun v => (D v).leftFactor.reference_value) a₀' (fun v => (D v).rightFactor.reference_value) a a' b b' g hg
    refine hf.trans ?_
    have hfinite : (∏ v : S, (ℓ v).val ((P.localFactor v).representation (finiteComponent F (r + 1) v.1 g) (a v)) *
        (ℓ' v).val ((P'.localFactor v).representation (finiteComponent F (r + 1) v.1 g) (a' v))) =
        ∏ v : S, WS v (finiteComponent F (r + 1) v.1 g) * WS' v (finiteComponent F (r + 1) v.1 g) :=
      Finset.prod_congr rfl fun v _ => congrArg₂ (· * ·)
        ((D v).leftFactor.coefficient_eq _) ((D v).rightFactor.coefficient_eq _)
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (hInf g) (hInf' g)) hfinite).trans ?_
    simp only [Finset.prod_mul_distrib]
    ac_rfl
  let fS (v : S) := equalIntegrand (normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData)
    (WS v) (WS' v) (ΦS v)
  have hkernel := pairedWhittakerIntegrandProduct F r S (κ * κ') W W' Φ WR WR' WC WC' WS WS'
    (fun v => ΦR v) (fun w => ΦC w) (fun v => ΦS v) hR hC
    (fun v => by
      let _ : TopologicalSpace (padicField v.1).Carrier := (padicField v.1).canonicalTopologicalData.topology
      exact whittaker_product_invariant (ψv v) (D v).left (D v).right)
    hpair (poleEqualSchwartzTensor_eq ΦR ΦC ΦS)
  let NS' (v : S) : OrdinaryIntegralNormalization
      (fun s => padicQuotientIntegral (padicField v.1) (equalPadicQuotientMeasure (padicField v.1) r) (fS v s))
      (c.finiteL v.1) := ⟨(NS v).value, (NS v).analytic, by
    let _ : TopologicalSpace (padicField v.1).Carrier := (padicField v.1).canonicalTopologicalData.topology
    let _ : MeasurableSpace (LeftUnipotentQuotient r (padicField v.1).Carrier) := borel _
    obtain ⟨b₀, hb₀⟩ := (NS v).eq_on_right
    refine ⟨b₀, fun s hs => ?_⟩
    exact (equalIntegral_eq_rankinSelberg (ψv v) _ r _ (D v).left (D v).right (ΦS v) s).trans (hb₀ s hs)⟩
  obtain ⟨C, hC₀, N, hN⟩ := exists_normalization_of_semilocal_pointwise_product DR DC
    (fun v => equalPadicQuotientMeasure (padicField v.1) r)
    (fun v => equalPadicQuotientMeasure_isCompatible (padicField v.1) r)
    (equalWhittakerIntegrand F W W' Φ) (mul_ne_zero hκ hκ')
    (fun v => realEqualIntegrand (WR v) (WR' v) (ΦR v))
    (fun w => complexEqualIntegrand (WC w) (WC' w) (ΦC w)) fS
    ⟨0, fun s _ q hq => hkernel s q hq⟩ NR NC NS'
  refine ⟨C, hC₀, ⟨N.value, N.analytic, ?_⟩, hN⟩
  obtain ⟨a₀, ha₀⟩ := N.eq_on_right
  refine ⟨a₀, fun s hs => ?_⟩
  rw [partialEqualWhittakerIntegral_eq_setIntegral, ha₀ s hs]
  exact congrArg (fun z : ℂ => N.value s * (((∏ v, LR v s) * ∏ w, LC w s) * z))
    (Finset.prod_coe_sort S (fun v => c.finiteL v s))

end Langlands.Global.CuspidalPairPoles
