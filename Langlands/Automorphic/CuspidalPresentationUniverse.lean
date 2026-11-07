import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.PresentedUnramifiedConstruction
import Langlands.Representation.Smooth.SmallRealizationProof

/-! # Independent carrier universes for cuspidal spectral presentations -/

noncomputable section

universe uF uV uW

namespace Langlands.Global.FiniteAdelicGL

open Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : FinitePlace F → Type uV} {W : FinitePlace F → Type uW}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]

/-- Local equivalences preserving the references induce an equivalence of the
actual finite adelic tensor actions, also when the carrier universes differ. -/
def tensorEquiv
    (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
    (σ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (W v))
    (E E' : Finset (FinitePlace F)) (e : ∀ v, V v) (e' : ∀ v, W v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (he' : ∀ v ∉ E', ∀ g ∈ localIntegral F n v, σ v g (e' v) = e' v)
    (f : ∀ v, (ρ v).Equiv (σ v))
    (hf : ∀ᶠ v in Filter.cofinite, f v (e v) = e' v) :
    (tensorRepresentation F n ρ E e he).Equiv
      (tensorRepresentation F n σ E' e' he') :=
  Representation.Equiv.mk
    (Langlands.RestrictedTensor.congr E E' e e' (fun v => (f v).toLinearEquiv) hf)
    (fun g => map_intertwines
      (fun v => (localIntegral F n v).toSubgroup) ρ σ E E' e e' he he'
      (fun v => (f v).toLinearEquiv.toLinearMap) hf
      (fun v h => (f v).isIntertwining' h) (restrictedProductEquiv F n g))

end Langlands.Global.FiniteAdelicGL

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F]

/-- The completion's own topological data lets the small-realization theorem
apply directly to an actual finite local group. -/
theorem exists_small_finiteLocalFactor (n : ℕ) (v : FinitePlace F)
    (π : Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteLocalGL F n v))
    (hπ : π.IsIrreducible) :
    ∃ σ : Langlands.SmoothRep.{0, uF, uW} ℂ (FiniteLocalGL F n v),
      σ.IsIrreducible ∧ Nonempty (π.representation.Equiv σ.representation) :=
  Langlands.padicIrreducibleSmoothSmallRealization
    (CompletionPadic.residuePrime v) (CompletionPadic.padicField v)
    (CompletionPadic.topologicalData v) n π hπ

namespace FiniteTensorPresentation

variable {n : ℕ} {V : FinitePlace F → Type uV} {W : FinitePlace F → Type uW}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

include he in
/-- Transporting a reference vector by an intertwiner preserves integral fixedness. -/
theorem mapReferences_fixed
    (σ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (W v))
    (f : ∀ v, (ρ v).Equiv (σ v))
    (v : FinitePlace F) (hv : v ∉ E) (g : FiniteLocalGL F n v)
    (hg : g ∈ localIntegral F n v) :
    σ v g (f v (e v)) = f v (e v) := by
  calc
    σ v g (f v (e v)) = f v (ρ v g (e v)) :=
      (Representation.IntertwiningMap.isIntertwining _ _
        (f v).toIntertwiningMap g (e v)).symm
    _ = f v (e v) := congrArg (f v) (he v hv g hg)

/-- Replace every factor by an equivalent action, carrying all references and
the genuine tensor equivalence to the same embedded finite realization. -/
def mapFactors (P : FiniteTensorPresentation F n ρ E e he S)
    (σ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (W v))
    (f : ∀ v, (ρ v).Equiv (σ v)) :
    FiniteTensorPresentation F n σ E (fun v => f v (e v))
      (mapReferences_fixed (he := he) σ f) S where
  reference_nonzero v hv hz :=
    P.reference_nonzero v hv ((f v).injective (hz.trans (map_zero (f v)).symm))
  equiv :=
    (tensorEquiv F n ρ σ E E e (fun v => f v (e v)) he
      (mapReferences_fixed (he := he) σ f) f
      (Filter.Eventually.of_forall fun _ => rfl)).symm.trans P.equiv

end FiniteTensorPresentation

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
variable {S : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uV} S)

/-- Rebuild a complete spectral presentation using equivalent irreducible
admissible factors. The finite slice is retained and spectra are constructed
from the transported actual local actions. -/
def mapFactors
    (σ : ∀ v, Langlands.SmoothRep.{0, uF, uW} ℂ (FiniteLocalGL F (r + 1) v))
    (f : ∀ v, (P.localFactor v).representation.Equiv (σ v).representation)
    (hI : ∀ v, (σ v).IsIrreducible)
    (hA : ∀ v, Langlands.IsAdmissible (σ v).representation) :
    CuspidalSpectralPresentation.{uF, uW} S where
  finiteSlice := P.finiteSlice
  localFactor := σ
  tensorExceptional := P.tensorExceptional
  reference v := f v (P.reference v)
  reference_fixed := FiniteTensorPresentation.mapReferences_fixed
    (he := P.reference_fixed) (fun v => (σ v).representation) f
  presentation := P.presentation.mapFactors (fun v => (σ v).representation) f
  exceptional := P.tensorExceptional
  unramified :=
    (P.presentation.mapFactors (fun v => (σ v).representation) f).unramifiedData
      P.finiteSlice.nonzero P.tensorExceptional (fun _ hv => hv)
      (fun v _ => hI v) (fun v _ => hA v)

/-- An all-place irreducible admissible spectral presentation can be realized
in any independently prescribed carrier universe, including `Type 0`. -/
theorem exists_small
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧
      (P.localComponent v).IsAdmissible) :
    ∃ Q : CuspidalSpectralPresentation.{uF, uW} S,
      ∀ v, (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible := by
  classical
  have hsmall : ∀ v, ∃ σ : Langlands.SmoothRep.{0, uF, uW} ℂ
      (FiniteLocalGL F (r + 1) v),
      σ.IsIrreducible ∧ Langlands.IsAdmissible σ.representation ∧
        Nonempty ((P.localFactor v).representation.Equiv σ.representation) := by
    intro v
    have hI := (P.presentation.localComponent_isIrreducible_iff
      P.finiteSlice.nonzero v).mp (hP v).1
    have hA := (P.presentation.localComponent_isAdmissible_iff
      P.finiteSlice.nonzero v).mp (hP v).2
    obtain ⟨σ, hσ, ⟨f⟩⟩ := exists_small_finiteLocalFactor (r + 1) v (P.localFactor v) hI
    exact ⟨σ, hσ, Langlands.isAdmissible_of_equiv f hA, ⟨f⟩⟩
  choose σ hI hA hf using hsmall
  let f := fun v => Classical.choice (hf v)
  let Q := P.mapFactors σ f hI hA
  refine ⟨Q, fun v => ⟨?_, ?_⟩⟩
  · exact (Q.presentation.localComponent_isIrreducible_iff Q.finiteSlice.nonzero v).mpr (hI v)
  · exact (Q.presentation.localComponent_isAdmissible_iff Q.finiteSlice.nonzero v).mpr (hA v)

end CuspidalSpectralPresentation
end Langlands.Automorphic
