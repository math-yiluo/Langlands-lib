import Langlands.Global.FiniteAdelicGL.WhittakerMultiplicityOne
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerFunctionalStatement
import Langlands.Global.RankinSelberg.RealPlaceWhittakerEquivariance
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerEquivariance

/-! # The local covariance and fixed-level continuity of a mixed Whittaker functional -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Archimedean
  Langlands.Archimedean.MixedSmooth Langlands.Archimedean.SmoothInvariantSubspace
  Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
  Langlands.HarishChandraSchwartz Langlands.Global.HeckeFunctionalEquation NumberField

universe u v w

attribute [local instance] regSchemeAffine regSchemeSmooth

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm
local notation "Πf" => MixedSmooth.finiteRepresentation σ π hcomm
local notation "Πa" => MixedSmooth.archimedeanRepresentation σ π hcomm

/-- A fixed-level inclusion continuous in the derivative topology makes a
continuous pullback of the mixed functional. -/
theorem continuous_mixedWhittaker_on_level
    {X : Type w} [TopologicalSpace X] (j : X → W)
    (J : CompactOpenSubgroup (FiniteAdelicGL F (r + 1)))
    (hJ : ∀ x, (j x).val.val ∈ fixedSubspace σ J.toSubgroup)
    (hcont : Continuous (fun x => (DerivativeSmoothVectors.toSmooth I π).symm (j x).val))
    (ℓ : W →ₗ[ℂ] ℂ)
    (hℓ : IsContinuousAtEachLevel (A := ArchimedeanMatrix F (r + 1)) σ π hcomm ℓ) :
    Continuous (fun x => ℓ (j x)) := by
  obtain ⟨f, hf, he⟩ := hℓ J
  have hc := (continuous_of_isContinuousOnSmoothVectors I π f hf).comp hcont
  refine hc.congr fun x => ?_
  simpa only [Function.comp_apply, LinearEquiv.apply_symm_apply] using (he (j x) (hJ x)).symm

variable (ψ : UnitaryAdditiveCharacter (Adeles F))

/-- Finite local insertion has the standard character of the corresponding
canonical additive component. -/
theorem mixedWhittaker_finitePlace (ℓ : W →ₗ[ℂ] ℂ)
    (hℓ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ) (p : FinitePlace F)
    (ψp : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField p))
    (hψp : ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ p ψp)
    (a : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F p)) (x : W) :
    ℓ (Πf (localInclusion F (r + 1) p a.val) x) =
      (FiniteWhittakerTensor.factorCharacter p ψp a : ℂ) * ℓ x := by
  let z : unipotentAdelic F (r + 1) :=
    ⟨UnramifiedWhittaker.localPoint F p a.val,
      UnramifiedWhittaker.localPoint_mem_unipotentAdelic F p a.val a.property⟩
  let d := localInclusion F (r + 1) p a.val
  have hpoint : GeneralLinearGroupPoints.adelicEquiv F (r + 1) z.val =
      AdelicGL.ofFinite F (r + 1) d := MulEquiv.apply_symm_apply _ _
  have ha : archPart F (r + 1) z.val = 1 := by
    change archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) z.val)) = 1
    rw [hpoint, AdelicGL.infinite_ofFinite, map_one]
  have hd : finPart F (r + 1) z.val = d := by
    change AdelicGL.finite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) z.val) = d
    rw [hpoint, AdelicGL.finite_ofFinite]
  have hc := UnramifiedWhittaker.genericCharacter_localPoint F ψ p ψp hψp a
  change (genericCharacter F r ψ.complex (fun _ => 1) z : ℂ) =
    (FiniteWhittakerTensor.factorCharacter p ψp a : ℂ) at hc
  simpa only [ha, hd, hc, map_one, Module.End.one_apply] using hℓ.2 z x

/-- The restriction along a finite-factor intertwiner satisfies the local
covariance predicate used for finite adelic uniqueness. -/
theorem mixedWhittaker_hasComponents {V : Type w} [AddCommGroup V] [Module ℂ V]
    (ℓ : W →ₗ[ℂ] ℂ)
    (hℓ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ)
    (ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) V)
    (j : V →ₗ[ℂ] W) (hj : ∀ g x, j (ρ g x) = Πf g (j x))
    (ψp : ∀ p, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField p))
    (hψp : ∀ p, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ p (ψp p)) :
    HasWhittakerComponents ψp ρ (ℓ.comp j) := by
  intro p a x
  exact (congrArg ℓ (hj (localInclusion F (r + 1) p a.val) x)).trans
    (mixedWhittaker_finitePlace σ π hcomm ψ ℓ hℓ p (ψp p) (hψp p) a (j x))

/-- Under insertion at a real place the mixed functional transforms by
the standard character of the real additive component. -/
theorem mixedWhittaker_realPlace (ℓ : W →ₗ[ℂ] ℂ)
    (hℓ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ)
    (p : {p : InfinitePlace F // p.IsReal})
    (c : ℝˣ) (hc : IsRealAdditiveComponent ψ p.val p.property c)
    (a : GeneralLinear.upperUnipotent (r + 1) ℝ) (x : W) :
    ℓ (Πa (realPlaceGL F (r + 1) p a.val) x) =
      (Whittaker.standardCharacter (realScaledCharacter c) r a : ℂ) * ℓ x := by
  let z : unipotentAdelic F (r + 1) :=
    ⟨realPlacePoint F (r + 1) p a.val, realPlacePoint_mem_unipotent F (r + 1) p a⟩
  have ha : archPart F (r + 1) z.val = realPlaceGL F (r + 1) p a.val :=
    archPart_adelicPoint F (r + 1) _ 1
  have hd : finPart F (r + 1) z.val = 1 := finPart_adelicPoint F (r + 1) _ 1
  have hcz := genericCharacter_realPlacePoint F ψ.complex p c (realComponent_complex ψ p c hc) a.property
  have hc' : (genericCharacter F r ψ.complex (fun _ => 1) z : ℂ) =
      (Whittaker.standardCharacter (realScaledCharacter c) r a : ℂ) := hcz
  simpa only [ha, hd, hc', map_one, Module.End.one_apply] using hℓ.2 z x

/-- Under insertion at a complex place the mixed functional transforms by
the standard character of the complex additive component. -/
theorem mixedWhittaker_complexPlace (ℓ : W →ₗ[ℂ] ℂ)
    (hℓ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ)
    (p : {p : InfinitePlace F // p.IsComplex})
    (c : ℂˣ) (hc : IsComplexAdditiveComponent ψ p.val p.property c)
    (a : GeneralLinear.upperUnipotent (r + 1) ℂ) (x : W) :
    ℓ (Πa (complexPlaceGL F (r + 1) p a.val) x) =
      (Whittaker.standardCharacter (complexScaledCharacter c) r a : ℂ) * ℓ x := by
  let z : unipotentAdelic F (r + 1) :=
    ⟨complexPlacePoint F (r + 1) p a.val,
      complexPlacePoint_mem_unipotentAdelic F (r + 1) p a.property⟩
  have ha : archPart F (r + 1) z.val = complexPlaceGL F (r + 1) p a.val :=
    archPart_adelicPoint F (r + 1) _ 1
  have hd : finPart F (r + 1) z.val = 1 := finPart_adelicPoint F (r + 1) _ 1
  have hcz := genericCharacter_complexPlacePoint F ψ.complex p c
    (complexComponent_complex ψ p c hc) a.property
  have hc' : (genericCharacter F r ψ.complex (fun _ => 1) z : ℂ) =
      (Whittaker.standardCharacter (complexScaledCharacter c) r a : ℂ) := hcz
  simpa only [ha, hd, hc', map_one, Module.End.one_apply] using hℓ.2 z x

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
