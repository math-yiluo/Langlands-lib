import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Representation.Unramified.TwistedHeckeScalars

/-! # Spherical spectra of determinant multiples

Let the realization of `T'` be the determinant multiple of the realization of `T` by a
Hecke character `χ`, of arbitrary order. At a finite place `v` where `χ` is unramified and
both presentations are unramified, the spectrum of `T'` at `v` is the spectrum of `T`
with every eigenvalue multiplied by `χ_v(ϖ_v)`. Hence the scaled spectral system of a
presentation of `T` and the spectral system of a presentation of `T'` have the same Euler
polynomials at almost every place.
-/

noncomputable section
universe uF uV uW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

open Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F]

/-- At a place where `χ` is unramified, `χ_v ∘ det` is trivial on `GL_n(𝒪_v)`. -/
theorem finiteLocalDeterminant_eq_one_of_isUnramifiedAt (χ : HeckeCharacter F) (n : ℕ)
    (v : FinitePlace F) (hχ : χ.IsUnramifiedAt v) (g : FiniteLocalGL F n v)
    (hg : g ∈ localIntegral F n v) : χ.finiteLocalDeterminant n v g = 1 := by
  have hdet : ∀ A : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (∀ i j, A i j ∈ v.adicCompletionIntegers F) → A.det ∈ v.adicCompletionIntegers F := by
    intro A hA
    let O := (v.adicCompletionIntegers F).toSubring
    let A' : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hA i j⟩
    have hA' : O.subtype.mapMatrix A' = A := rfl
    have h : A.det ∈ O := by
      rw [← hA', ← RingHom.map_det]
      exact A'.det.property
    exact h
  rw [finiteLocalDeterminant_eq_finiteComponent_det]
  apply hχ
  refine ⟨?_, ?_⟩
  · change ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ hg.1
  · change (((Matrix.GeneralLinearGroup.det g)⁻¹ : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ hg.2

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified
open Langlands.Unramified.MinusculeCosets ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F]

local instance detMultipleRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance detMultipleContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance detMultipleSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance detMultipleFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance detMultipleStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance detMultipleRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {n : ℕ}

/-- The continuous function of a finite translate is the right translate of the continuous
function. -/
theorem toContinuous_finiteRepresentation (S : OperatorRealization F n)
    (d : FiniteAdelicGL F n) (f : S.Space) :
    S.toContinuous (S.finiteRepresentation d f) =
      continuousRightAction F n (AdelicGL.ofFinite F n d) (S.toContinuous f) :=
  toContinuousMap_injective F n (ContinuousMap.ext fun _ => rfl)

/-- A determinant multiple intertwines the finite translations up to the determinant
character. -/
theorem finiteRepresentation_of_toContinuous_eq {S T : OperatorRealization F n}
    {χ : HeckeCharacter F} (e : S.Space ≃ₗ[ℂ] T.Space)
    (he : ∀ f, T.toContinuous (e f) = determinantMultiplier n χ (S.toContinuous f))
    (d : FiniteAdelicGL F n) (f : S.Space) :
    T.finiteRepresentation d (e f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        e (S.finiteRepresentation d f) := by
  -- Explicit steps: rewriting with `map_smul` here exhausts `isDefEq`.
  apply T.toContinuous_injective
  calc T.toContinuous (T.finiteRepresentation d (e f))
      = continuousRightAction F n (AdelicGL.ofFinite F n d) (T.toContinuous (e f)) :=
        toContinuous_finiteRepresentation T d (e f)
    _ = continuousRightAction F n (AdelicGL.ofFinite F n d)
          (determinantMultiplier n χ (S.toContinuous f)) := by rw [he]
    _ = (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) • determinantMultiplier n χ
          (continuousRightAction F n (AdelicGL.ofFinite F n d) (S.toContinuous f)) :=
        determinantMultiplier_rightAction n χ _ _
    _ = (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
          determinantMultiplier n χ (S.toContinuous (S.finiteRepresentation d f)) := by
        rw [toContinuous_finiteRepresentation S d f]
    _ = (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
          T.toContinuous (e (S.finiteRepresentation d f)) := by
        rw [he (S.finiteRepresentation d f)]
    _ = T.toContinuous ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
          e (S.finiteRepresentation d f)) := (T.toContinuous.map_smul _ _).symm

/-- The local translations of a determinant multiple are those of the source, multiplied
by `χ_v ∘ det`. -/
theorem localRepresentation_of_toContinuous_eq {S T : OperatorRealization F n}
    {χ : HeckeCharacter F} (e : S.Space ≃ₗ[ℂ] T.Space)
    (he : ∀ f, T.toContinuous (e f) = determinantMultiplier n χ (S.toContinuous f))
    (v : FinitePlace F) (g : FiniteLocalGL F n v) (f : S.Space) :
    T.localRepresentation v g (e f) =
      (χ.finiteLocalDeterminant n v g : ℂ) • e (S.localRepresentation v g f) :=
  finiteRepresentation_of_toContinuous_eq e he (localInclusion F n v g) f

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- If the realization of `T'` is the determinant multiple of that of `T` by `χ`, then at a
place where `χ` is unramified, outside the exceptional sets of two presentations, the
spectrum of `T'` is the spectrum of `T` multiplied by `χ_v(ϖ_v)`. -/
theorem eigenvalues_eq_scale_of_isDeterminantMultiple (T T' : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uV} T) (P' : CuspidalSpectralPresentation.{uF, uW} T')
    {χ : HeckeCharacter F}
    (h : OperatorRealization.IsDeterminantMultiple χ T.realization T'.realization)
    (v : FinitePlace F) (hχ : χ.IsUnramifiedAt v) (hv : v ∉ P.exceptional)
    (hv' : v ∉ P'.exceptional) :
    P'.spectralSystem.eigenvalues v hv' =
      Eigenvalues.scale (χ.finiteUniformizerValue v) (P.spectralSystem.eigenvalues v hv) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨a, ha⟩ := P.exists_spherical_ne_zero v hv
  have hK : ∀ k ∈ Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r,
      (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom k = 1 := fun k hk =>
    χ.finiteLocalDeterminant_eq_one_of_isUnramifiedAt (r + 1) v hχ k
      ((SetLike.ext_iff.mp (localIntegral_eq_sphericalSubgroup F v r) k).mpr hk)
  exact PairedHecke.eq_scale_of_twist (CompletionPadic.padicField v)
    (T.realization.localRepresentation v) (T.realization.localRepresentation_isSmooth_canonical v)
    (T'.realization.localRepresentation v)
    (T'.realization.localRepresentation_isSmooth_canonical v) e
    (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
    (OperatorRealization.localRepresentation_of_toContinuous_eq e he v) hK
    (χ.finiteUniformizerValue v) (χ.finiteLocalDeterminant_standardDiagonal v r) _ _
    (P.corner_eq_smul v hv) (P'.corner_eq_smul v hv') a ha

/-- The scaled spectral system of a presentation of `T` and the spectral system of a
presentation of the determinant multiple `T'` have the same Euler polynomials. -/
theorem sameEulerPolynomials_scale_of_isDeterminantMultiple
    (T T' : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uV} T) (P' : CuspidalSpectralPresentation.{uF, uW} T')
    {χ : HeckeCharacter F}
    (h : OperatorRealization.IsDeterminantMultiple χ T.realization T'.realization) :
    (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SameEulerPolynomials
      P'.spectralSystem := by
  obtain ⟨U, hU⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt (K := F) χ
  filter_upwards [U.eventually_cofinite_notMem] with v hvU hs ht
  change Eigenvalues.eulerPolynomial
      (Eigenvalues.scale (χ.finiteUniformizerValue v) (P.spectralSystem.eigenvalues v hs)) =
    Eigenvalues.eulerPolynomial (P'.spectralSystem.eigenvalues v ht)
  rw [eigenvalues_eq_scale_of_isDeterminantMultiple T T' P P' h v (hU v hvU) hs ht]

end CuspidalOperatorRealization

end Langlands.Automorphic
