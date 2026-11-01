import Langlands.Automorphic.PresentedSpectralSystem
import Langlands.Automorphic.FiniteTensorDeterminantComponents
import Langlands.Automorphic.DeterminantTwistAdmissibility
import Langlands.Automorphic.LocalSphericalDeterminantSpectrum
import Langlands.Representation.Unramified.SpectralSystemScaling
import Langlands.Representation.Twist.SubquotientProof

/-! # Actual unramified data after determinant multiplication -/

noncomputable section
open scoped Classical
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F]

local instance unramifiedTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance unramifiedTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance unramifiedTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance unramifiedTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance unramifiedTwistSpaceGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

private theorem actualSpectrum_of_equiv
    {v : FinitePlace F} {r : ℕ} (L M : LocalRealization F (r + 1) v)
    (e : L.representation.Equiv M.representation)
    (hI : L.IsIrreducible) (hA : L.IsAdmissible)
    (s : Eigenvalues (r + 1)) (hs : L.HasSphericalHeckeSpectrum s) :
    M.HasSphericalHeckeSpectrum s := by
  let A := L.padicObject hI hA
  let B := M.padicObject
    ((Langlands.isIrreducible_iff_of_equiv e).mp hI)
    ((Langlands.isAdmissible_iff_of_equiv e).mp hA)
  exact (Langlands.Unramified.hasSphericalHeckeSpectrum_iff_of_equiv
    (CompletionPadic.padicField v) (A := A) (B := B) e s).mp hs

namespace FiniteTensorPresentation.UnramifiedData

variable {r : ℕ} {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable {P : FiniteTensorPresentation F (r + 1) ρ E e he S}
variable {hS : S.IsNonzero F (r + 1)} {T : Finset (FinitePlace F)}
variable (D : P.UnramifiedData hS T) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

/-- Supplied actual unramified data transport to the genuine multiplied
presentation, after adding the proved character-tail bound to the exceptions. -/
def determinantTwist :
    (P.determinantTwist χ hχ).UnramifiedData
      ((S.determinantTwist_ne_bot_iff χ hχ).mpr hS)
      (T ∪ χ.finiteDeterminantTail (r + 1) hχ) where
  exceptional_subset := Finset.union_subset_union D.exceptional_subset (fun _ h => h)
  irreducible v hv := (Langlands.isIrreducible_twist_iff
    (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom (ρ v)).mpr
      (D.irreducible v (fun h => hv (Finset.mem_union_left _ h)))
  admissible v hv := (Langlands.isAdmissible_twist_iff
    (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom (ρ v)
    (χ.finiteLocalDeterminant_isOpen_ker (r + 1) hχ v)).mpr
      (D.admissible v (fun h => hv (Finset.mem_union_left _ h)))
  eigenvalues v hv := Eigenvalues.scale (χ.finiteUniformizerValue v)
    (D.eigenvalues v (fun h => hv (Finset.mem_union_left _ h)))
  hasSpectrum v hv := by
    let hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    have hI : (P.localComponent hS v).IsIrreducible :=
      (P.localComponent_isIrreducible_iff hS v).mpr (D.irreducible v hvT)
    have hA : (P.localComponent hS v).IsAdmissible :=
      (P.localComponent_isAdmissible_iff hS v).mpr (D.admissible v hvT)
    exact actualSpectrum_of_equiv
      (P.determinantTwistLocalComponent hS χ hχ v)
      ((P.determinantTwist χ hχ).localComponent
        ((S.determinantTwist_ne_bot_iff χ hχ).mpr hS) v)
      (P.determinantTwistPresentationLocalComponentEquiv hS χ hχ v).symm
      (((P.localComponent hS v).determinantTwist_isIrreducible_iff χ hχ).mpr hI)
      (((P.localComponent hS v).determinantTwist_isAdmissible_iff χ hχ).mpr hA)
      _ ((P.localComponent hS v).hasSphericalHeckeSpectrum_determinantTwist_outside_tail
        χ hχ (fun h => hv (Finset.mem_union_right _ h)) _ (D.hasSpectrum v hvT))

@[simp]
theorem determinantTwist_eigenvalues (v : FinitePlace F)
    (hv : v ∉ T ∪ χ.finiteDeterminantTail (r + 1) hχ) :
    (D.determinantTwist χ hχ).eigenvalues v hv =
      Eigenvalues.scale (χ.finiteUniformizerValue v)
        (D.eigenvalues v (fun h => hv (Finset.mem_union_left _ h))) := rfl

/-- The actual-data power traces have the expected positive character powers. -/
theorem determinantTwist_powerTrace (v : FinitePlace F)
    (hv : v ∉ T ∪ χ.finiteDeterminantTail (r + 1) hχ) (k : ℕ) :
    (D.determinantTwist χ hχ).powerTrace v hv k =
      (χ.finiteUniformizerValue v : ℂ) ^ k *
        D.powerTrace v (fun h => hv (Finset.mem_union_left _ h)) k :=
  Eigenvalues.powerTrace_scale _ _ _

/-- The actual-data Euler denominator scales by substitution in its variable. -/
theorem determinantTwist_eulerPolynomial (v : FinitePlace F)
    (hv : v ∉ T ∪ χ.finiteDeterminantTail (r + 1) hχ) :
    (D.determinantTwist χ hχ).eulerPolynomial v hv =
      (D.eulerPolynomial v (fun h => hv (Finset.mem_union_left _ h))).comp
        (Polynomial.C (χ.finiteUniformizerValue v : ℂ) * Polynomial.X) :=
  Eigenvalues.eulerPolynomial_scale _ _

@[simp]
theorem determinantTwist_spectralSystem :
    (D.determinantTwist χ hχ).spectralSystem =
      (SpectralSystem.scale χ.finiteUniformizerValue D.spectralSystem).restrict
        (T ∪ χ.finiteDeterminantTail (r + 1) hχ) Finset.subset_union_left := rfl

/-- The enlarged finite set does not change almost-everywhere trace comparison
with the pointwise scaled supplied system. -/
theorem samePowerTraces_determinantTwist :
    (SpectralSystem.scale χ.finiteUniformizerValue D.spectralSystem).SamePowerTraces
      (D.determinantTwist χ hχ).spectralSystem := by
  rw [determinantTwist_spectralSystem]
  exact SpectralSystem.samePowerTraces_restrict _ _ _

theorem sameEulerPolynomials_determinantTwist :
    (SpectralSystem.scale χ.finiteUniformizerValue D.spectralSystem).SameEulerPolynomials
      (D.determinantTwist χ hχ).spectralSystem := by
  rw [determinantTwist_spectralSystem]
  exact SpectralSystem.sameEulerPolynomials_restrict _ _ _

/-- Comparison with any commonly scaled supplied numerical system reflects to
the original data; no arithmetic realization of the comparison system is assumed. -/
theorem determinantTwist_samePowerTraces_scale_iff {m : ℕ}
    (t : SpectralSystem (FinitePlace F) m) :
    (D.determinantTwist χ hχ).spectralSystem.SamePowerTraces
        (SpectralSystem.scale χ.finiteUniformizerValue t) ↔
      D.spectralSystem.SamePowerTraces t := by
  have hD := D.samePowerTraces_determinantTwist χ hχ
  constructor
  · intro h
    exact (SpectralSystem.samePowerTraces_scale_iff _ _ _).mp (hD.trans h)
  · intro h
    exact hD.symm.trans ((SpectralSystem.samePowerTraces_scale_iff _ _ _).mpr h)

theorem determinantTwist_sameEulerPolynomials_scale_iff {m : ℕ}
    (t : SpectralSystem (FinitePlace F) m) :
    (D.determinantTwist χ hχ).spectralSystem.SameEulerPolynomials
        (SpectralSystem.scale χ.finiteUniformizerValue t) ↔
      D.spectralSystem.SameEulerPolynomials t := by
  have hD := D.sameEulerPolynomials_determinantTwist χ hχ
  constructor
  · intro h
    exact (SpectralSystem.sameEulerPolynomials_scale_iff _ _ _).mp (hD.trans h)
  · intro h
    exact hD.symm.trans ((SpectralSystem.sameEulerPolynomials_scale_iff _ _ _).mpr h)

end FiniteTensorPresentation.UnramifiedData
end Langlands.Automorphic
