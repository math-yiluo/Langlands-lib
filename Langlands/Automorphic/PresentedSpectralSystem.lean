import Langlands.Automorphic.PresentedUnramifiedData
import Langlands.Representation.Unramified.SpectralSystem

/-! # Numerical spectral systems from actual presented unramified data -/

noncomputable section
open scoped BigOperators
universe uF uV uJ

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F]

local instance presentedSpectralRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance presentedSpectralContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance presentedSpectralSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance presentedSpectralFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

namespace FiniteTensorPresentation
namespace UnramifiedData

variable {r : ℕ} {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable {P : FiniteTensorPresentation F (r + 1) ρ E e he S}
variable {hS : S.IsNonzero F (r + 1)} {T : Finset (FinitePlace F)}
variable (D : P.UnramifiedData hS T)

/-- Forget the actual presentation evidence, retaining its supplied spectra. -/
def spectralSystem : SpectralSystem (FinitePlace F) (r + 1) where
  exceptional := T
  eigenvalues := D.eigenvalues

@[simp] theorem spectralSystem_exceptional : D.spectralSystem.exceptional = T := rfl

@[simp] theorem spectralSystem_eigenvalues (v : FinitePlace F) (hv : v ∉ T) :
    D.spectralSystem.eigenvalues v hv = D.eigenvalues v hv := rfl

@[simp] theorem spectralSystem_powerTrace (v : FinitePlace F) (hv : v ∉ T) (k : ℕ) :
    D.spectralSystem.powerTrace v hv k = D.powerTrace v hv k := rfl

@[simp] theorem spectralSystem_eulerPolynomial (v : FinitePlace F) (hv : v ∉ T) :
    D.spectralSystem.eulerPolynomial v hv = D.eulerPolynomial v hv := rfl

/-- The retained spectra still satisfy the actual component's scalar equations. -/
theorem spectralSystem_hasSpectrum (v : FinitePlace F) (hv : v ∉ T) :
    (P.localComponent hS v).HasSphericalHeckeSpectrum
      (D.spectralSystem.eigenvalues v hv) :=
  D.hasSpectrum v hv

@[simp] theorem restrict_spectralSystem {U : Finset (FinitePlace F)} (hTU : T ⊆ U) :
    (D.restrict hTU).spectralSystem = D.spectralSystem.restrict U hTU := rfl

@[simp] theorem transport_spectralSystem {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS' : S'.IsNonzero F (r + 1)) :
    (D.transport Q hS').spectralSystem = D.spectralSystem := rfl

theorem samePowerTraces_restrict {U : Finset (FinitePlace F)} (hTU : T ⊆ U) :
    D.spectralSystem.SamePowerTraces (D.restrict hTU).spectralSystem :=
  D.spectralSystem.samePowerTraces_restrict U hTU

theorem sameEulerPolynomials_restrict {U : Finset (FinitePlace F)} (hTU : T ⊆ U) :
    D.spectralSystem.SameEulerPolynomials (D.restrict hTU).spectralSystem :=
  D.spectralSystem.sameEulerPolynomials_restrict U hTU

end UnramifiedData

section FiniteFamily

variable {J : Type uJ} [Fintype J] {r : J → ℕ}
variable {V : ∀ _j : J, FinitePlace F → Type uV}
variable [∀ j v, AddCommGroup (V j v)] [∀ j v, Module ℂ (V j v)]
variable {ρ : ∀ j v, Representation ℂ (FiniteLocalGL F (r j + 1) v) (V j v)}
variable {E : J → Finset (FinitePlace F)} {e : ∀ j v, V j v}
variable {he : ∀ j v, v ∉ E j →
  ∀ g ∈ localIntegral F (r j + 1) v, ρ j v g (e j v) = e j v}
variable {S : ∀ j, FiniteRealization F (r j + 1)}
variable {P : ∀ j, FiniteTensorPresentation F (r j + 1) (ρ j) (E j) (e j) (he j) (S j)}
variable {hS : ∀ j, (S j).IsNonzero F (r j + 1)}
variable {T : J → Finset (FinitePlace F)}
variable (D : ∀ j, (P j).UnramifiedData (hS j) (T j))

/-- Numerical concatenation of spectra supplied by a finite mixed-rank family
of actual presentations. This does not construct an isobaric representation. -/
def spectralSum : SpectralSystem (FinitePlace F) (∑ j, (r j + 1)) :=
  SpectralSystem.finiteSum fun j => (D j).spectralSystem

/-- Every constituent's exceptional set is contained in the common finite set. -/
theorem subset_spectralSum_exceptional (j : J) :
    T j ⊆ (spectralSum D).exceptional :=
  SpectralSystem.exceptional_subset_family (fun j => (D j).spectralSystem) j

theorem not_mem_spectralSum_exceptional (v : FinitePlace F)
    (hv : v ∉ (spectralSum D).exceptional) (j : J) : v ∉ T j :=
  fun h => hv (subset_spectralSum_exceptional D j h)

@[simp] theorem spectralSum_powerTrace (v : FinitePlace F)
    (hv : v ∉ (spectralSum D).exceptional) (k : ℕ) :
    (spectralSum D).powerTrace v hv k =
      ∑ j, (D j).powerTrace v (not_mem_spectralSum_exceptional D v hv j) k :=
  SpectralSystem.finiteSum_powerTrace _ _ _ _

@[simp] theorem spectralSum_eulerPolynomial (v : FinitePlace F)
    (hv : v ∉ (spectralSum D).exceptional) :
    (spectralSum D).eulerPolynomial v hv =
      ∏ j, (D j).eulerPolynomial v (not_mem_spectralSum_exceptional D v hv j) :=
  SpectralSystem.finiteSum_eulerPolynomial _ _ _

theorem spectralSum_eulerPolynomial_natDegree (v : FinitePlace F)
    (hv : v ∉ (spectralSum D).exceptional) :
    (∏ j, (D j).eulerPolynomial v
      (not_mem_spectralSum_exceptional D v hv j)).natDegree = ∑ j, (r j + 1) := by
  rw [← spectralSum_eulerPolynomial D v hv]
  exact SpectralSystem.eulerPolynomial_natDegree _ _ _

/-- Comparing the family to any supplied system tests the literal sum of
actual-data traces outside one finite set uniform in all positive powers. -/
theorem spectralSum_samePowerTraces_iff {n : ℕ}
    (t : SpectralSystem (FinitePlace F) n) :
    (spectralSum D).SamePowerTraces t ↔
      ∀ᶠ v in Filter.cofinite,
        ∀ (hD : v ∉ (spectralSum D).exceptional) (ht : v ∉ t.exceptional),
          ∀ k : ℕ, 0 < k →
            (∑ j, (D j).powerTrace v (not_mem_spectralSum_exceptional D v hD j) k) =
              t.powerTrace v ht k := by
  constructor
  · intro h
    exact h.mono fun v hv hD ht k hk =>
      (spectralSum_powerTrace D v hD k).symm.trans (hv hD ht k hk)
  · intro h
    exact h.mono fun v hv hD ht k hk =>
      (spectralSum_powerTrace D v hD k).trans (hv hD ht k hk)

theorem spectralSum_sameEulerPolynomials_iff {n : ℕ}
    (t : SpectralSystem (FinitePlace F) n) :
    (spectralSum D).SameEulerPolynomials t ↔
      ∀ᶠ v in Filter.cofinite,
        ∀ (hD : v ∉ (spectralSum D).exceptional) (ht : v ∉ t.exceptional),
          (∏ j, (D j).eulerPolynomial v (not_mem_spectralSum_exceptional D v hD j)) =
            t.eulerPolynomial v ht := by
  constructor
  · intro h
    exact h.mono fun v hv hD ht =>
      (spectralSum_eulerPolynomial D v hD).symm.trans (hv hD ht)
  · intro h
    exact h.mono fun v hv hD ht =>
      (spectralSum_eulerPolynomial D v hD).trans (hv hD ht)

end FiniteFamily
end FiniteTensorPresentation
end Langlands.Automorphic
