import Langlands.Global.RankinSelberg.FiniteWhittakerDualProduct
import Langlands.Global.RankinSelberg.SelfPairPositiveData

/-! # Nonzero normalized infinite Whittaker residuals -/

noncomputable section
open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerResidual

open Langlands.Automorphic Langlands.Global.FiniteAdelicGL
open Langlands.Global.CompletionPadic
open Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.ClassField.Global.RelativeWeilGroup
open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open FiniteWhittakerPartialDomain UnipotentClass LocalPointFactorization

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

local instance (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance [CompactSpace (AdeleQuotient F)] (T : CuspidalOperatorRealization F r) :
    AddCommGroup T.Space := Submodule.addCommGroup _
local instance : DecidableEq (FinitePlace F) := Classical.decEq _

private def eraseCoordinate (v : FinitePlace F) (g : Points F (r + 1)) : Points F (r + 1) :=
  g * (localPoint F (r + 1) v (finiteComponent F (r + 1) v g))⁻¹

private theorem finiteComponent_eraseCoordinate (v : FinitePlace F) (g : Points F (r + 1)) :
    finiteComponent F (r + 1) v (eraseCoordinate v g) = 1 :=
  finiteComponent_mul_inv_localPoint F (r + 1) v g

private theorem finiteComponent_eraseCoordinate_of_ne {v w : FinitePlace F} (hw : w ≠ v)
    (g : Points F (r + 1)) :
    finiteComponent F (r + 1) w (eraseCoordinate v g) = finiteComponent F (r + 1) w g := by
  rw [eraseCoordinate, UnipotentClass.finiteComponent_mul, LocalPointFactorization.finiteComponent_inv,
    finiteComponent_localPoint_of_ne F (r + 1) hw, inv_one, mul_one]

variable [CompactSpace (AdeleQuotient F)] {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u, uQ} T)
  (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S)
  (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
  (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
  (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)

include P hPS hψ hS in
/-- Removing any unramified coordinate from a nonzero Whittaker value leaves a
nonzero value of the same spherical vector. -/
private theorem nonzero_eraseCoordinate (x : T.Space) (hxS : IsSphericalOutside F T S x)
    (v : FinitePlace F) (hv : v ∉ S) (g : Points F (r + 1))
    (hg : cuspWhittaker F T ψ.complex x g ≠ 0) :
    cuspWhittaker F T ψ.complex x (eraseCoordinate v g) ≠ 0 := by
  obtain ⟨ψv, hψv, _⟩ := hS v hv
  obtain ⟨a, ha⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1) (P.spectralSystem.eigenvalues v
    (fun hvP => hv (hPS hvP)))
  have hfactor := (UnramifiedWhittaker.unramifiedWhittakerFactorization
    F ψ hψ r T P S hPS hS x hxS v hv ψv hψv (placeUniformizer v)
    (isUniformizingElement_canonical v) a ha (eraseCoordinate v g)
    (finiteComponent_eraseCoordinate v g) (finiteComponent F (r + 1) v g)).1
  change cuspWhittaker F T ψ.complex x
    (eraseCoordinate v g * localPoint F (r + 1) v (finiteComponent F (r + 1) v g)) =
      cuspWhittaker F T ψ.complex x (eraseCoordinate v g) * _ at hfactor
  have hrestore : eraseCoordinate v g * localPoint F (r + 1) v (finiteComponent F (r + 1) v g) = g := by
    rw [eraseCoordinate, inv_mul_cancel_right]
  rw [hrestore] at hfactor
  intro hzero
  exact hg (hfactor.trans (by rw [hzero, zero_mul]))

include P hPS hψ hS in
/-- A nonzero vector spherical outside `S` has a nonzero Whittaker value
at a point that is integral at every finite place outside `S`. -/
private theorem exists_nonzero_integralAway (x : T.Space) (hx : x ≠ 0)
    (hxS : IsSphericalOutside F T S x) :
    ∃ g : Points F (r + 1), (∀ v ∉ S, finiteComponent F (r + 1) v g ∈
      localIntegral F (r + 1) v) ∧ cuspWhittaker F T ψ.complex x g ≠ 0 := by
  obtain ⟨g, hg⟩ := SelfPair.exists_cuspWhittaker_ne_zero T ψ.complex
    (UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ) hx
  have hfinite : {v | finiteComponent F (r + 1) v g ∉ localIntegral F (r + 1) v}.Finite :=
    Filter.eventually_cofinite.mp (eventually_localIntegral F (r + 1)
      (AdelicGL.finite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)))
  have trim (E : Finset (FinitePlace F)) (g : Points F (r + 1))
      (hint : ∀ v ∉ S, v ∉ E → finiteComponent F (r + 1) v g ∈ localIntegral F (r + 1) v)
      (hval : cuspWhittaker F T ψ.complex x g ≠ 0) :
      ∃ g' : Points F (r + 1), (∀ v ∉ S, finiteComponent F (r + 1) v g' ∈
        localIntegral F (r + 1) v) ∧ cuspWhittaker F T ψ.complex x g' ≠ 0 := by
    induction E using Finset.induction_on generalizing g with
    | empty => exact ⟨g, fun v hv => hint v hv (Finset.notMem_empty v), hval⟩
    | @insert v E hvE ih =>
      by_cases hvS : v ∈ S
      · exact ih g (fun w hwS hwE => hint w hwS fun he =>
          (Finset.mem_insert.mp he).elim (fun e => hwS (e ▸ hvS)) hwE) hval
      · refine ih (eraseCoordinate v g) (fun w hwS hwE => ?_) ?_
        · by_cases h : w = v
          · subst w
            rw [finiteComponent_eraseCoordinate]
            exact (localIntegral F (r + 1) v).one_mem
          · rw [finiteComponent_eraseCoordinate_of_ne h]
            exact hint w hwS (fun he => (Finset.mem_insert.mp he).elim h hwE)
        · exact nonzero_eraseCoordinate P S hPS ψ hψ hS x hxS v hvS g hval
  refine trim hfinite.toFinset g (fun v _ hv => ?_) hg
  by_contra hi
  exact hv (hfinite.mem_toFinset.mpr hi)

omit [CompactSpace (AdeleQuotient F)] in
private theorem integralPoint_decomposition (g : Points F (r + 1))
    (hg : ∀ v ∉ S, finiteComponent F (r + 1) v g ∈ localIntegral F (r + 1) v) :
    ∃ k : awayIntegralSubgroup F (r + 1) S,
      g = retainedPoint S g * adelicSplit F (r + 1) S (1, (1, k.val)) := by
  let z := (adelicSplit F (r + 1) S).symm g
  have hz (v : {v : FinitePlace F // v ∉ S}) :
      z.2.2 v = finiteComponent F (r + 1) v.1 g := by
    have h := finiteComponent_adelicSplit_of_not_mem F (r + 1) S z v.property
    simpa only [z, ContinuousMulEquiv.apply_symm_apply] using h.symm
  let k : awayIntegralSubgroup F (r + 1) S :=
    ⟨z.2.2, fun v => (hz v).symm ▸ hg v.1 v.property⟩
  refine ⟨k, ?_⟩
  change g = adelicSplit F (r + 1) S (z.1, (z.2.1, 1)) *
    adelicSplit F (r + 1) S (1, (1, z.2.2))
  rw [← map_mul]
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.eta, z] using
    ((adelicSplit F (r + 1) S).apply_symm_apply g).symm

variable (hP : HasIrreducibleAdmissibleComponents P)

include hψ hS in
/-- If the global vector is nonzero, its normalized infinite residual is nonzero
somewhere on the partial domain. -/
theorem exists_infiniteResidual_ne_zero_of_global
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (hx : P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t) ≠ 0) :
    ∃ g ∈ unipotentIntegralOutside F (r + 1) S,
      infiniteResidual S P hP hPS ψ.complex a₀ t g ≠ 0 := by
  let x : T.Space := P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)
  obtain ⟨g, hint, hg⟩ := exists_nonzero_integralAway P S hPS ψ hψ hS x hx
    (P.allPlaceTensorEquiv_finitePure_sphericalOutside hP S hPS a₀ t)
  obtain ⟨k, hk⟩ := integralPoint_decomposition S g hint
  have hw : cuspWhittaker F T ψ.complex x (retainedPoint S g) ≠ 0 := by
    intro hzero
    apply hg
    rw [hk]
    exact (whittaker_mul_away P hP S hPS ψ.complex a₀ t (retainedPoint S g) k).trans hzero
  have hfinite := coefficient_eq_product_at_retained S P hP hPS ψ hψ ψv hψv ℓ a₀ ha₀ a₀ t g
  refine ⟨g, fun v hv => ?_, fun hzero => hw ?_⟩
  · refine ⟨(finiteComponent F (r + 1) v g)⁻¹, (localIntegral F (r + 1) v).inv_mem (hint v hv), ?_⟩
    rw [mul_inv_cancel]
    exact ⟨Matrix.one_apply_eq, fun i j h => Matrix.one_apply_ne h.ne'⟩
  · exact hfinite.trans (by rw [show cuspWhittaker F T ψ.complex x (infinitePoint S g) = 0 from
      hzero, mul_zero])

include hψ hS in
/-- The normalized infinite residual of every nonzero infinite tensor is
nonzero somewhere on the partial domain. -/
theorem exists_infiniteResidual_ne_zero
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) (ht : t ≠ 0) :
    ∃ g ∈ unipotentIntegralOutside F (r + 1) S,
      infiniteResidual S P hP hPS ψ.complex a₀ t g ≠ 0 := by
  apply exists_infiniteResidual_ne_zero_of_global P S hPS ψ hψ hS hP ψv hψv ℓ a₀ ha₀ t
  have ha (v : S) : a₀ v ≠ 0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz, map_zero] using ha₀ v)
  intro hz
  apply Langlands.TensorMultiplicity.tmul_ne_zero (K := ℂ) (P.finitePure_ne_zero S hPS a₀ ha) ht
  exact (P.allPlaceTensorEquiv hP).injective (hz.trans (map_zero _).symm)

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerResidual
