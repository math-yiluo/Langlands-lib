import Langlands.Automorphic.CuspidalArithmeticSpectralTransportStatement
import Langlands.Automorphic.CuspidalArithmeticSphericalTransport
import Langlands.Automorphic.CuspidalArithmeticTensorTransport

/-! # Arithmetic pullback of an attached cuspidal spectral system -/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global AdelicFunctoriality AdelicGLTransport FiniteAdelicGL Unramified

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

local instance arithmeticSpectralRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSpectralContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSpectralSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSpectralFormsGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance arithmeticSpectralSpaceGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} (S : LocalRealization F n v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

omit [NumberField K] [NumberField L] in
private theorem not_mem_source_exceptional (a : L ≃+* K) (E : Finset (FinitePlace L))
    (v : FinitePlace K) (hv : v ∉ transportExceptional a E) : finitePlaceEquiv a v ∉ E := by
  simpa only [transportExceptional, Finset.mem_map_equiv, Equiv.symm_symm] using hv

omit [NumberField K] [NumberField L] in
/-- Pullback of finite places along the inverse field isomorphism. -/
theorem arithmeticPlace_inverse (e : K ≃+* L) (v : FinitePlace K) :
    finitePlaceEquiv e.symm v = (finitePlaceEquiv e).symm v := by
  apply (finitePlaceEquiv e).injective
  rw [Equiv.apply_symm_apply, ← Equiv.trans_apply, ← finitePlaceEquiv_trans,
    RingEquiv.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]

private theorem eulerPolynomial_of_place_eq {I : Type*} {n : ℕ} (s : SpectralSystem I n)
    {v w : I} (h : v = w) (hv : v ∉ s.exceptional) (hw : w ∉ s.exceptional) :
    s.eulerPolynomial v hv = s.eulerPolynomial w hw := by
  subst w
  rfl

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
variable {r : ℕ} {S : CuspidalOperatorRealization L r}

/-- An actual cuspidal presentation pulls back with the same local carrier universes. -/
def arithmeticComap (P : CuspidalSpectralPresentation.{uL, uV} S) (e : K ≃+* L) :
    CuspidalSpectralPresentation.{uK, uV} (S.arithmeticComap e) := by
  let A := P.finiteSlice.arithmeticComap e
  let Q := P.presentation.arithmeticComap e
  refine
    { finiteSlice := A
      localFactor := fun v => SmoothRep.pullback (localEquiv (r + 1) e.symm v).symm
        (P.localFactor (finitePlaceEquiv e.symm v))
      tensorExceptional := transportExceptional e.symm P.tensorExceptional
      reference := fun v => P.reference (finitePlaceEquiv e.symm v)
      reference_fixed := transportReference_fixed e.symm _ _ _ P.reference_fixed
      presentation := Q
      exceptional := transportExceptional e.symm P.exceptional
      unramified := ?_ }
  refine
    { exceptional_subset := by
        intro v hv
        simp only [transportExceptional, Finset.mem_map_equiv, Equiv.symm_symm] at hv ⊢
        exact P.unramified.exceptional_subset hv
      irreducible := ?_
      admissible := ?_
      eigenvalues := fun v hv => P.unramified.eigenvalues _ (not_mem_source_exceptional _ _ v hv)
      hasSpectrum := ?_ }
  · intro v hv
    exact (isIrreducible_comp_continuousMulEquiv_iff _ (localEquiv (r + 1) e.symm v).symm).mpr
      (P.unramified.irreducible _ (not_mem_source_exceptional _ _ v hv))
  · intro v hv
    exact isAdmissible_comp_continuousMulEquiv _ (localEquiv (r + 1) e.symm v).symm
      (P.unramified.admissible _ (not_mem_source_exceptional _ _ v hv))
  · intro v hv
    let w := finitePlaceEquiv e.symm v
    let f := localEquiv (r + 1) e.symm v
    let source := P.presentation.localComponentEquiv P.finiteSlice.nonzero w
    let target := Q.localComponentEquiv A.nonzero v
    let B := source.symm.toLinearEquiv.trans target.toLinearEquiv
    refine LocalRealization.hasSphericalHeckeSpectrum_arithmetic e.symm B ?_ _
      (P.unramified.hasSpectrum w (not_mem_source_exceptional _ _ v hv))
    intro g x
    have hsource := LinearMap.congr_fun (source.symm.isIntertwining' g) x
    have htarget := LinearMap.congr_fun (target.isIntertwining' (f g)) (source.symm x)
    have hfactor : transportFactors e.symm (fun w => (P.localFactor w).representation) v
          (f g) (source.symm x) = (P.localFactor w).representation g (source.symm x) :=
      congrArg (fun k : FiniteLocalGL L (r + 1) w => (P.localFactor w).representation k (source.symm x))
        (f.symm_apply_apply g)
    exact (congrArg target hsource).trans ((congrArg target hfactor.symm).trans htarget)

end CuspidalSpectralPresentation

/-- Pullback carries an attached spectral system and preserves the Euler polynomials
at corresponding places where they are defined. -/
theorem cuspidalArithmeticSpectralTransport :
    CuspidalArithmeticSpectralTransportStatement.{uK, uL, uV} := by
  intro K L _ _ _ _ _ _ e r c s hs
  obtain ⟨S, P, rfl, rfl⟩ := hs
  let Q := P.arithmeticComap e
  refine ⟨Q.spectralSystem, ⟨S.arithmeticComap e, Q, rfl, rfl⟩,
    Filter.Eventually.of_forall ?_⟩
  intro v hv hw
  have hv' : finitePlaceEquiv e.symm v ∉ P.spectralSystem.exceptional :=
    not_mem_source_exceptional e.symm P.exceptional v hv
  change P.spectralSystem.eulerPolynomial (finitePlaceEquiv e.symm v) hv' =
    P.spectralSystem.eulerPolynomial ((finitePlaceEquiv e).symm v) hw
  exact eulerPolynomial_of_place_eq _ (arithmeticPlace_inverse e v) hv' hw

end Langlands.Automorphic
