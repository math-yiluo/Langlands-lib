import Langlands.Automorphic.LocalSphericalDeterminantTwist
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Automorphic.FiniteDeterminantTail
import Langlands.Representation.Unramified.EigenvalueScaling

/-! # Supplied spherical spectra under actual determinant multiplication -/

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

local instance spectrumTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance spectrumTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance spectrumTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance spectrumTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance spectrumTwistSpaceGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ} (S : LocalRealization F (r + 1) v)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
variable (hlocal : ∀ g ∈ localIntegral F (r + 1) v,
  χ.finiteLocalDeterminant (r + 1) v g = 1)

/-- Actual mass-one Hecke covariance with the canonical local uniformizer value. -/
theorem standardHeckeOperator_determinantTwist_uniformizer
    (i : Fin (r + 2)) (f : S.SphericalVectors) :
    (S.determinantTwist χ hχ).standardHeckeOperator i
        (S.determinantTwistSphericalEquiv χ hχ hlocal f) =
      (χ.finiteUniformizerValue v : ℂ) ^ i.val •
        S.determinantTwistSphericalEquiv χ hχ hlocal (S.standardHeckeOperator i f) := by
  simpa only [χ.finiteLocalDeterminant_standardDiagonal, Units.val_pow_eq_pow_val]
    using S.standardHeckeOperator_determinantTwist χ hχ hlocal i f

/-- The actual multiplier transports a supplied normalized scalar eigen-equation. -/
theorem standardHeckeOperator_determinantTwist_scaled
    (s : Eigenvalues (r + 1)) (i : Fin (r + 2)) (f : S.SphericalVectors)
    (hf : S.standardHeckeOperator i f =
      standardHeckeScalar (CompletionPadic.padicField v) s i • f) :
    (S.determinantTwist χ hχ).standardHeckeOperator i
        (S.determinantTwistSphericalEquiv χ hχ hlocal f) =
      standardHeckeScalar (CompletionPadic.padicField v)
          (Eigenvalues.scale (χ.finiteUniformizerValue v) s) i •
        S.determinantTwistSphericalEquiv χ hχ hlocal f := by
  simpa only [χ.finiteLocalDeterminant_standardDiagonal, Units.val_pow_eq_pow_val,
    standardHeckeScalar_scale] using
      S.standardHeckeOperator_determinantTwist_eigen χ hχ hlocal i f
        (standardHeckeScalar (CompletionPadic.padicField v) s i) hf

/-- Nonzero simultaneous eigenvectors transport in the actual local form space. -/
theorem isSphericalHeckeEigenvector_determinantTwist
    (s : Eigenvalues (r + 1)) (f : S.SphericalVectors)
    (hf : S.IsSphericalHeckeEigenvector s f) :
    (S.determinantTwist χ hχ).IsSphericalHeckeEigenvector
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s)
      (S.determinantTwistSphericalEquiv χ hχ hlocal f) := by
  refine ⟨?_, fun i => S.standardHeckeOperator_determinantTwist_scaled
    χ hχ hlocal s i f (hf.2 i)⟩
  intro h
  exact hf.1 ((S.determinantTwistSphericalEquiv χ hχ hlocal).injective
    (h.trans (S.determinantTwistSphericalEquiv χ hχ hlocal).map_zero.symm))

include hlocal in
/-- A supplied whole-space spectrum transports through the actual spherical equivalence. -/
theorem hasSphericalHeckeSpectrum_determinantTwist
    (s : Eigenvalues (r + 1)) (hs : S.HasSphericalHeckeSpectrum s) :
    (S.determinantTwist χ hχ).HasSphericalHeckeSpectrum
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s) := by
  refine ⟨submodule_ne_bot_of_linearEquiv
    (S.determinantTwistSphericalEquiv χ hχ hlocal) hs.1, ?_⟩
  intro i
  exact scalar_equation_of_linearEquiv
    (S.determinantTwistSphericalEquiv χ hχ hlocal)
    ((S.determinantTwist χ hχ).standardHeckeOperator i)
    (standardHeckeScalar (CompletionPadic.padicField v)
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s) i)
    (fun f => S.standardHeckeOperator_determinantTwist_scaled χ hχ hlocal s i f (hs.2 i f))

/-- The proved finite character tail supplies the local-triviality premise. -/
theorem hasSphericalHeckeSpectrum_determinantTwist_outside_tail
    (hv : v ∉ χ.finiteDeterminantTail (r + 1) hχ)
    (s : Eigenvalues (r + 1)) (hs : S.HasSphericalHeckeSpectrum s) :
    (S.determinantTwist χ hχ).HasSphericalHeckeSpectrum
      (Eigenvalues.scale (χ.finiteUniformizerValue v) s) :=
  S.hasSphericalHeckeSpectrum_determinantTwist χ hχ
    (fun g hg => χ.finiteLocalDeterminant_eq_one_outside_tail (r + 1) hχ v hv g hg)
    s hs

/-- Transport supplied numerical spectrum data together with its actual scalar-action proof. -/
def determinantTwistSphericalSpectrum
    (s : {s : Eigenvalues (r + 1) // S.HasSphericalHeckeSpectrum s}) :
    {s : Eigenvalues (r + 1) //
      (S.determinantTwist χ hχ).HasSphericalHeckeSpectrum s} :=
  ⟨Eigenvalues.scale (χ.finiteUniformizerValue v) s.val,
    S.hasSphericalHeckeSpectrum_determinantTwist χ hχ hlocal s.val s.property⟩

@[simp] theorem determinantTwistSphericalSpectrum_val
    (s : {s : Eigenvalues (r + 1) // S.HasSphericalHeckeSpectrum s}) :
    (S.determinantTwistSphericalSpectrum χ hχ hlocal s).val =
      Eigenvalues.scale (χ.finiteUniformizerValue v) s.val := rfl

/-- Transport a supplied nonzero actual eigenvector with its eigen-equations. -/
def determinantTwistSphericalEigenvector (s : Eigenvalues (r + 1))
    (f : {f : S.SphericalVectors // S.IsSphericalHeckeEigenvector s f}) :
    {f : (S.determinantTwist χ hχ).SphericalVectors //
      (S.determinantTwist χ hχ).IsSphericalHeckeEigenvector
        (Eigenvalues.scale (χ.finiteUniformizerValue v) s) f} :=
  ⟨S.determinantTwistSphericalEquiv χ hχ hlocal f.val,
    S.isSphericalHeckeEigenvector_determinantTwist χ hχ hlocal s f.val f.property⟩

@[simp] theorem determinantTwistSphericalEigenvector_val (s : Eigenvalues (r + 1))
    (f : {f : S.SphericalVectors // S.IsSphericalHeckeEigenvector s f}) :
    (S.determinantTwistSphericalEigenvector χ hχ hlocal s f).val =
      S.determinantTwistSphericalEquiv χ hχ hlocal f.val := rfl

end LocalRealization
end Langlands.Automorphic
