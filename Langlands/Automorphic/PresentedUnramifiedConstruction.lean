import Langlands.Automorphic.PresentedSpectralSystem
import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Derived unramified spectra of actual tensor presentations -/

noncomputable section
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F]

local instance constructedUnramifiedRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance constructedUnramifiedContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance constructedUnramifiedSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance constructedUnramifiedFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance constructedUnramifiedSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ} (L : LocalRealization F (r + 1) v)

/-- The actual irreducible admissible spherical component has a whole-space spectrum. -/
theorem exists_sphericalHeckeSpectrum (hI : L.IsIrreducible) (hA : L.IsAdmissible)
    (hfixed : L.SphericalVectors ≠ ⊥) :
    ∃ s : Unramified.Eigenvalues (r + 1), L.HasSphericalHeckeSpectrum s :=
  Unramified.sphericalHeckeSpectrumExistence _ (CompletionPadic.padicField v) r
    (L.padicObject hI hA) hfixed

/-- Separation for the original standard operators, with every multiplicity retained. -/
theorem eq_of_hasSphericalHeckeSpectrum (hI : L.IsIrreducible) (hA : L.IsAdmissible)
    {s t : Unramified.Eigenvalues (r + 1)}
    (hs : L.HasSphericalHeckeSpectrum s) (ht : L.HasSphericalHeckeSpectrum t) : s = t :=
  Unramified.eq_of_hasSphericalHeckeSpectrum (CompletionPadic.padicField v)
    (A := L.padicObject hI hA) hs ht

/-- The spectrum of the original nonzero spherical component is uniquely determined. -/
theorem existsUnique_sphericalHeckeSpectrum
    (hI : L.IsIrreducible) (hA : L.IsAdmissible) (hfixed : L.SphericalVectors ≠ ⊥) :
    ∃! s : Unramified.Eigenvalues (r + 1), L.HasSphericalHeckeSpectrum s := by
  obtain ⟨s, hs⟩ := L.exists_sphericalHeckeSpectrum hI hA hfixed
  exact ⟨s, hs, fun _ ht => L.eq_of_hasSphericalHeckeSpectrum hI hA ht hs⟩

end LocalRealization

namespace FiniteTensorPresentation

variable {r : ℕ} {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)

/-- The actual integral-fixed reference vector gives a nonzero spherical submodule. -/
theorem localComponent_sphericalVectors_ne_bot (hS : S.IsNonzero F (r + 1))
    (v : FinitePlace F) (hv : v ∉ E) :
    (P.localComponent hS v).SphericalVectors ≠ ⊥ := by
  obtain ⟨f, hf, hfix⟩ := P.localComponent_exists_integral_fixed hS v hv
  apply ((P.localComponent hS v).SphericalVectors).ne_bot_iff.mpr
  refine ⟨f, ?_, hf⟩
  change f ∈ Langlands.fixedVectors _ _
  rw [← localIntegral_eq_sphericalSubgroup F v r]
  intro g
  exact hfix g g.property

/-- Construct actual unramified data from factor hypotheses; no spectra are supplied. -/
def unramifiedData (hS : S.IsNonzero F (r + 1)) (T : Finset (FinitePlace F))
    (hET : E ⊆ T) (hI : ∀ v ∉ T, (ρ v).IsIrreducible)
    (hA : ∀ v ∉ T, Langlands.IsAdmissible (ρ v)) : P.UnramifiedData hS T where
  exceptional_subset := hET
  irreducible := hI
  admissible := hA
  eigenvalues v hv := Classical.choose
    ((P.localComponent hS v).exists_sphericalHeckeSpectrum
      ((P.localComponent_isIrreducible_iff hS v).mpr (hI v hv))
      ((P.localComponent_isAdmissible_iff hS v).mpr (hA v hv))
      (P.localComponent_sphericalVectors_ne_bot hS v (fun h => hv (hET h))))
  hasSpectrum v hv := Classical.choose_spec
    ((P.localComponent hS v).exists_sphericalHeckeSpectrum
      ((P.localComponent_isIrreducible_iff hS v).mpr (hI v hv))
      ((P.localComponent_isAdmissible_iff hS v).mpr (hA v hv))
      (P.localComponent_sphericalVectors_ne_bot hS v (fun h => hv (hET h))))

namespace UnramifiedData

variable {P} {hS : S.IsNonzero F (r + 1)} {T : Finset (FinitePlace F)}

/-- Two data objects on this actual presentation have the same unordered spectrum. -/
theorem eigenvalues_eq (D D' : P.UnramifiedData hS T)
    (v : FinitePlace F) (hv : v ∉ T) : D.eigenvalues v hv = D'.eigenvalues v hv :=
  (P.localComponent hS v).eq_of_hasSphericalHeckeSpectrum
    ((P.localComponent_isIrreducible_iff hS v).mpr (D.irreducible v hv))
    ((P.localComponent_isAdmissible_iff hS v).mpr (D.admissible v hv))
    (D.hasSpectrum v hv) (D'.hasSpectrum v hv)

/-- Spectral separation and proof irrelevance make all these data unique. -/
theorem unique (D D' : P.UnramifiedData hS T) : D = D' := by
  have h : D.eigenvalues = D'.eigenvalues := by
    funext v hv
    exact D.eigenvalues_eq D' v hv
  cases D
  cases D'
  cases h
  rfl

instance : Subsingleton (P.UnramifiedData hS T) := ⟨unique⟩

end UnramifiedData

variable (hS : S.IsNonzero F (r + 1)) (T : Finset (FinitePlace F))
variable (hET : E ⊆ T) (hI : ∀ v ∉ T, (ρ v).IsIrreducible)
variable (hA : ∀ v ∉ T, Langlands.IsAdmissible (ρ v))

/-- Every supplied data object equals the derived construction on this presentation. -/
theorem unramifiedData_eq (D : P.UnramifiedData hS T) :
    P.unramifiedData hS T hET hI hA = D := Subsingleton.elim _ _

/-- Constructing spectra commutes with enlargement of the exceptional set. -/
theorem unramifiedData_restrict {U : Finset (FinitePlace F)} (hTU : T ⊆ U) :
    (P.unramifiedData hS T hET hI hA).restrict hTU =
      P.unramifiedData hS U (hET.trans hTU)
        (fun v hv => hI v (fun h => hv (hTU h)))
        (fun v hv => hA v (fun h => hv (hTU h))) := Subsingleton.elim _ _

/-- Constructing spectra commutes with transport of the same full tensor family. -/
theorem unramifiedData_transport {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS' : S'.IsNonzero F (r + 1)) :
    (P.unramifiedData hS T hET hI hA).transport Q hS' =
      Q.unramifiedData hS' T hET hI hA := Subsingleton.elim _ _

/-- The derived numerical system is independent of the actual target presentation
of the fixed tensor family. -/
theorem unramifiedData_spectralSystem_eq {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (hS' : S'.IsNonzero F (r + 1)) :
    (P.unramifiedData hS T hET hI hA).spectralSystem =
      (Q.unramifiedData hS' T hET hI hA).spectralSystem := by
  calc
    _ = ((P.unramifiedData hS T hET hI hA).transport Q hS').spectralSystem :=
      ((P.unramifiedData hS T hET hI hA).transport_spectralSystem Q hS').symm
    _ = _ := congrArg (fun D : Q.UnramifiedData hS' T => D.spectralSystem)
      (P.unramifiedData_transport hS T hET hI hA Q hS')

end FiniteTensorPresentation
end Langlands.Automorphic
