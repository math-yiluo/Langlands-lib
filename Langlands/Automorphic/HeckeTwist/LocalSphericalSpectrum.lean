import Langlands.Automorphic.LocalSphericalDeterminantSpectrum
import Langlands.Automorphic.HeckeTwist.LocalSphericalTwist
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Automorphic.HeckeTwist.FiniteTail
import Langlands.Representation.Unramified.EigenvalueScaling

/-! # Spherical spectra under multiplication by any Hecke determinant character

Multiplication by `χ ∘ det`, for an arbitrary Hecke character `χ`, scales a spherical Hecke
spectrum by the local uniformizer value of `χ` at every finite place where the local
determinant character is trivial on the integral subgroup, in particular outside the full
integral tail of `Langlands.Automorphic.HeckeTwist.FiniteTail`. This is the finite-order-free
version of `Langlands.Automorphic.LocalSphericalDeterminantSpectrum`.
-/

noncomputable section
universe uF uV uW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

private theorem submodule_ne_bot_of_linearEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {A : Submodule ℂ V} {B : Submodule ℂ W} (e : A ≃ₗ[ℂ] B) (hA : A ≠ ⊥) :
    B ≠ ⊥ := by
  obtain ⟨x, hx, hne⟩ := A.ne_bot_iff.mp hA
  refine B.ne_bot_iff.mpr ⟨(e ⟨x, hx⟩ : W), (e ⟨x, hx⟩).property, ?_⟩
  intro h
  have he : e ⟨x, hx⟩ = e 0 := by
    apply Subtype.ext
    simpa only [map_zero, ZeroMemClass.coe_zero] using h
  exact hne (congrArg Subtype.val (e.injective he))

private theorem scalar_equation_of_linearEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (T : Module.End ℂ W) (c : ℂ)
    (h : ∀ x, T (e x) = c • e x) :
    ∀ y, T y = c • y := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  exact h x

variable {F : Type uF} [Field F] [NumberField F]

local instance heckeSpectrumTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeSpectrumTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeSpectrumTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeSpectrumTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeSpectrumTwistSpaceGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ} (S : LocalRealization F (r + 1) v)
variable (χ : HeckeCharacter F)
variable (hlocal : ∀ g ∈ localIntegral F (r + 1) v,
  χ.finiteLocalDeterminant (r + 1) v g = 1)

/-- Actual mass-one Hecke covariance with the canonical local uniformizer value. -/
theorem standardHeckeOperator_heckeDeterminantTwist_uniformizer
    (i : Fin (r + 2)) (f : S.SphericalVectors) :
    (S.heckeDeterminantTwist χ).standardHeckeOperator i
        (S.heckeDeterminantTwistSphericalEquiv χ hlocal f) =
      (χ.finiteUniformizerValue v : ℂ) ^ i.val •
        S.heckeDeterminantTwistSphericalEquiv χ hlocal (S.standardHeckeOperator i f) := by
  simpa only [χ.finiteLocalDeterminant_standardDiagonal, Units.val_pow_eq_pow_val]
    using S.standardHeckeOperator_heckeDeterminantTwist χ hlocal i f

/-- The actual multiplier transports a supplied normalized scalar eigen-equation. -/
theorem standardHeckeOperator_heckeDeterminantTwist_scaled
    (s : Eigenvalues (r + 1)) (i : Fin (r + 2)) (f : S.SphericalVectors)
    (hf : S.standardHeckeOperator i f =
      standardHeckeScalar (CompletionPadic.padicField v) s i • f) :
    (S.heckeDeterminantTwist χ).standardHeckeOperator i
        (S.heckeDeterminantTwistSphericalEquiv χ hlocal f) =
      standardHeckeScalar (CompletionPadic.padicField v)
          (Eigenvalues.scale (χ.finiteUniformizerValue v) s) i •
        S.heckeDeterminantTwistSphericalEquiv χ hlocal f := by
  simpa only [χ.finiteLocalDeterminant_standardDiagonal, Units.val_pow_eq_pow_val,
    standardHeckeScalar_scale] using
      S.standardHeckeOperator_heckeDeterminantTwist_eigen χ hlocal i f
        (standardHeckeScalar (CompletionPadic.padicField v) s i) hf

/-- Nonzero simultaneous eigenvectors transport in the actual local form space. -/
theorem isSphericalHeckeEigenvector_heckeDeterminantTwist
    (s : Eigenvalues (r + 1)) (f : S.SphericalVectors)
    (hf : S.IsSphericalHeckeEigenvector s f) :
    (S.heckeDeterminantTwist χ).IsSphericalHeckeEigenvector
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s)
      (S.heckeDeterminantTwistSphericalEquiv χ hlocal f) := by
  refine ⟨?_, fun i => S.standardHeckeOperator_heckeDeterminantTwist_scaled
    χ hlocal s i f (hf.2 i)⟩
  intro h
  exact hf.1 ((S.heckeDeterminantTwistSphericalEquiv χ hlocal).injective
    (h.trans (S.heckeDeterminantTwistSphericalEquiv χ hlocal).map_zero.symm))

include hlocal in
/-- A supplied whole-space spectrum transports through the actual spherical equivalence. -/
theorem hasSphericalHeckeSpectrum_heckeDeterminantTwist
    (s : Eigenvalues (r + 1)) (hs : S.HasSphericalHeckeSpectrum s) :
    (S.heckeDeterminantTwist χ).HasSphericalHeckeSpectrum
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s) := by
  refine ⟨submodule_ne_bot_of_linearEquiv
    (S.heckeDeterminantTwistSphericalEquiv χ hlocal) hs.1, ?_⟩
  intro i
  exact scalar_equation_of_linearEquiv
    (S.heckeDeterminantTwistSphericalEquiv χ hlocal)
    ((S.heckeDeterminantTwist χ).standardHeckeOperator i)
    (standardHeckeScalar (CompletionPadic.padicField v)
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s) i)
    (fun f => S.standardHeckeOperator_heckeDeterminantTwist_scaled χ hlocal s i f (hs.2 i f))

/-- The proved finite character tail supplies the local-triviality premise. -/
theorem hasSphericalHeckeSpectrum_heckeDeterminantTwist_outside_tail
    (hv : v ∉ χ.finiteHeckeDeterminantTail (r + 1))
    (s : Eigenvalues (r + 1)) (hs : S.HasSphericalHeckeSpectrum s) :
    (S.heckeDeterminantTwist χ).HasSphericalHeckeSpectrum
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s) :=
  S.hasSphericalHeckeSpectrum_heckeDeterminantTwist χ
    (fun g hg => χ.finiteLocalHeckeDeterminant_eq_one_outside_tail (r + 1) v hv g hg)
    s hs

/-- Transport supplied numerical spectrum data together with its actual scalar-action proof. -/
def heckeDeterminantTwistSphericalSpectrum
    (s : {s : Eigenvalues (r + 1) // S.HasSphericalHeckeSpectrum s}) :
    {s : Eigenvalues (r + 1) //
      (S.heckeDeterminantTwist χ).HasSphericalHeckeSpectrum s} :=
  ⟨Eigenvalues.scale (χ.finiteUniformizerValue v) s.val,
    S.hasSphericalHeckeSpectrum_heckeDeterminantTwist χ hlocal s.val s.property⟩

@[simp] theorem heckeDeterminantTwistSphericalSpectrum_val
    (s : {s : Eigenvalues (r + 1) // S.HasSphericalHeckeSpectrum s}) :
    (S.heckeDeterminantTwistSphericalSpectrum χ hlocal s).val =
      Eigenvalues.scale (χ.finiteUniformizerValue v) s.val := rfl

/-- Transport a supplied nonzero actual eigenvector with its eigen-equations. -/
def heckeDeterminantTwistSphericalEigenvector (s : Eigenvalues (r + 1))
    (f : {f : S.SphericalVectors // S.IsSphericalHeckeEigenvector s f}) :
    {f : (S.heckeDeterminantTwist χ).SphericalVectors //
      (S.heckeDeterminantTwist χ).IsSphericalHeckeEigenvector
        (Eigenvalues.scale (χ.finiteUniformizerValue v) s) f} :=
  ⟨S.heckeDeterminantTwistSphericalEquiv χ hlocal f.val,
    S.isSphericalHeckeEigenvector_heckeDeterminantTwist χ hlocal s f.val f.property⟩

@[simp] theorem heckeDeterminantTwistSphericalEigenvector_val (s : Eigenvalues (r + 1))
    (f : {f : S.SphericalVectors // S.IsSphericalHeckeEigenvector s f}) :
    (S.heckeDeterminantTwistSphericalEigenvector χ hlocal s f).val =
      S.heckeDeterminantTwistSphericalEquiv χ hlocal f.val := rfl

end LocalRealization
end Langlands.Automorphic
