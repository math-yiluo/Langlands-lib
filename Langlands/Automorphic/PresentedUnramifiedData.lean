import Langlands.Automorphic.LocalSphericalHecke

/-! # Supplied unramified spectral data for actual tensor presentations -/

noncomputable section
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F]

local instance presentedUnramifiedRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance presentedUnramifiedContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance presentedUnramifiedSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance presentedUnramifiedFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance presentedUnramifiedSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {r : ℕ} {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)

/-- Explicit spectra outside a finite exceptional set for this actual presentation.
The scalar-action field is evidence, not an assertion of spectral existence. -/
structure UnramifiedData (hS : S.IsNonzero F (r + 1)) (T : Finset (FinitePlace F)) where
  exceptional_subset : E ⊆ T
  irreducible : ∀ v ∉ T, (ρ v).IsIrreducible
  admissible : ∀ v ∉ T, Langlands.IsAdmissible (ρ v)
  eigenvalues : ∀ v ∉ T, Langlands.Unramified.Eigenvalues (r + 1)
  hasSpectrum : ∀ v (hv : v ∉ T),
    (P.localComponent hS v).HasSphericalHeckeSpectrum (eigenvalues v hv)

namespace UnramifiedData

variable {P} {hS : S.IsNonzero F (r + 1)} {T : Finset (FinitePlace F)}
variable (D : P.UnramifiedData hS T)

/-- The same spectrum belongs to the genuine class of the actual local component. -/
theorem hasSpectrumClass (v : FinitePlace F) (hv : v ∉ T) :
    Langlands.Unramified.HasSphericalHeckeSpectrumClass (CompletionPadic.padicField v)
      (P.localPadicClass hS v (D.irreducible v hv) (D.admissible v hv))
      (D.eigenvalues v hv) :=
  ((P.localComponent hS v).hasSphericalHeckeSpectrumClass_iff _ _ _).mpr
    (D.hasSpectrum v hv)

/-- Its genuine local class is spherical at each place where the data are supplied. -/
theorem isSphericalClass (v : FinitePlace F) (hv : v ∉ T) :
    Correspondence.IsSphericalClass (CompletionPadic.padicField v)
      (P.localPadicClass hS v (D.irreducible v hv) (D.admissible v hv)) :=
  P.localPadicClass_isSpherical hS v (fun hvE => hv (D.exceptional_subset hvE))
    (D.irreducible v hv) (D.admissible v hv)

/-- Each supplied spectrum yields a nonzero ambient eigenform lying in the component. -/
theorem exists_eigenform (v : FinitePlace F) (hv : v ∉ T) :
    ∃ f : (P.localComponent hS v).SphericalVectors,
      IsSphericalHeckeEigenform F v r (D.eigenvalues v hv)
        ((P.localComponent hS v).sphericalInclusion f) :=
  (P.localComponent hS v).exists_sphericalHeckeEigenform_of_spectrum _
    (D.hasSpectrum v hv)

/-- Power traces retain all eigenvalue multiplicities; positive powers are the
ones used in unramified trace comparisons. -/
def powerTrace (v : FinitePlace F) (hv : v ∉ T) (k : ℕ) : ℂ :=
  (D.eigenvalues v hv).powerTrace k

/-- The normalized Euler denominator of the supplied actual Hecke spectrum. -/
def eulerPolynomial (v : FinitePlace F) (hv : v ∉ T) : Polynomial ℂ :=
  (D.eigenvalues v hv).eulerPolynomial

@[simp] theorem powerTrace_zero (v : FinitePlace F) (hv : v ∉ T) :
    D.powerTrace v hv 0 = (r + 1 : ℕ) :=
  Langlands.Unramified.Eigenvalues.powerTrace_zero _

@[simp] theorem eulerPolynomial_eval_zero (v : FinitePlace F) (hv : v ∉ T) :
    (D.eulerPolynomial v hv).eval 0 = 1 :=
  Langlands.Unramified.Eigenvalues.eulerPolynomial_eval_zero _

theorem eulerPolynomial_ne_zero (v : FinitePlace F) (hv : v ∉ T) :
    D.eulerPolynomial v hv ≠ 0 :=
  Langlands.Unramified.Eigenvalues.eulerPolynomial_ne_zero _

@[simp] theorem eulerPolynomial_natDegree (v : FinitePlace F) (hv : v ∉ T) :
    (D.eulerPolynomial v hv).natDegree = r + 1 :=
  Langlands.Unramified.Eigenvalues.eulerPolynomial_natDegree _

/-- A matrix realizing these numerical invariants; no canonical matrix is chosen. -/
theorem exists_matrix (v : FinitePlace F) (hv : v ∉ T) :
    ∃ A : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ,
      (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).charpolyRev =
        D.eulerPolynomial v hv ∧
      ∀ k : ℕ, Matrix.trace ((A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) ^ k) =
        D.powerTrace v hv k :=
  Langlands.Unramified.Eigenvalues.exists_matrix _

/-- Enlarge the exceptional set by forgetting data at additional places. -/
def restrict {U : Finset (FinitePlace F)} (hTU : T ⊆ U) : P.UnramifiedData hS U where
  exceptional_subset := D.exceptional_subset.trans hTU
  irreducible v hv := D.irreducible v (fun h => hv (hTU h))
  admissible v hv := D.admissible v (fun h => hv (hTU h))
  eigenvalues v hv := D.eigenvalues v (fun h => hv (hTU h))
  hasSpectrum v hv := D.hasSpectrum v (fun h => hv (hTU h))

@[simp] theorem restrict_powerTrace {U : Finset (FinitePlace F)} (hTU : T ⊆ U)
    (v : FinitePlace F) (hv : v ∉ U) (k : ℕ) :
    (D.restrict hTU).powerTrace v hv k =
      D.powerTrace v (fun h => hv (hTU h)) k := rfl

@[simp] theorem restrict_eulerPolynomial {U : Finset (FinitePlace F)} (hTU : T ⊆ U)
    (v : FinitePlace F) (hv : v ∉ U) :
    (D.restrict hTU).eulerPolynomial v hv =
      D.eulerPolynomial v (fun h => hv (hTU h)) := rfl

/-- Transport supplied data between genuine presentations of the same tensor
family, possibly with different actual target subspaces. -/
def transport {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS' : S'.IsNonzero F (r + 1)) : Q.UnramifiedData hS' T where
  exceptional_subset := D.exceptional_subset
  irreducible := D.irreducible
  admissible := D.admissible
  eigenvalues := D.eigenvalues
  hasSpectrum v hv := by
    apply ((Q.localComponent hS' v).hasSphericalHeckeSpectrumClass_iff _ _ _).mp
    change Langlands.Unramified.HasSphericalHeckeSpectrumClass _
      (Q.localPadicClass hS' v (D.irreducible v hv) (D.admissible v hv)) _
    rw [← P.localPadicClass_eq Q hS hS' v (D.irreducible v hv) (D.admissible v hv)]
    exact D.hasSpectrumClass v hv

@[simp] theorem transport_powerTrace {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS' : S'.IsNonzero F (r + 1)) (v : FinitePlace F) (hv : v ∉ T) (k : ℕ) :
    (D.transport Q hS').powerTrace v hv k = D.powerTrace v hv k := rfl

@[simp] theorem transport_eulerPolynomial {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS' : S'.IsNonzero F (r + 1)) (v : FinitePlace F) (hv : v ∉ T) :
    (D.transport Q hS').eulerPolynomial v hv = D.eulerPolynomial v hv := rfl

end UnramifiedData
end FiniteTensorPresentation
end Langlands.Automorphic
