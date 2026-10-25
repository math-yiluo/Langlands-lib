import Langlands.Automorphic.CuspidalFiniteSlice
import Langlands.Automorphic.PresentedSpectralSystem

/-! # Spectral presentations attached to actual cuspidal classes -/

noncomputable section
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance cuspidalSpectralRationalAddCommGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalSpectralContinuousAddCommGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalSpectralSmoothAddCommGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalSpectralFormsAddCommGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- Supplied genuine tensor and spectral data on a nonzero finite subspace
inside an actual full cuspidal realization. Existence is not asserted. -/
structure CuspidalSpectralPresentation {r : ℕ} (S : CuspidalOperatorRealization F r) where
  finiteSlice : S.FiniteSlice
  localFactor : ∀ v, Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteLocalGL F (r + 1) v)
  tensorExceptional : Finset (FinitePlace F)
  reference : ∀ v, localFactor v
  reference_fixed : ∀ v ∉ tensorExceptional, ∀ g ∈ localIntegral F (r + 1) v,
    (localFactor v).representation g (reference v) = reference v
  presentation : FiniteTensorPresentation F (r + 1)
    (fun v => (localFactor v).representation) tensorExceptional reference reference_fixed
    finiteSlice.subspace
  exceptional : Finset (FinitePlace F)
  unramified : presentation.UnramifiedData finiteSlice.nonzero exceptional

namespace CuspidalSpectralPresentation

variable {r : ℕ} {S T : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uV} S)

/-- The numerical system is taken from the actual component's supplied spectra. -/
def spectralSystem : SpectralSystem (FinitePlace F) (r + 1) :=
  P.unramified.spectralSystem

@[simp] theorem spectralSystem_exceptional :
    P.spectralSystem.exceptional = P.exceptional := rfl

/-- The actual embedded local copy of the supplied factor. -/
def localComponent (v : FinitePlace F) : LocalRealization F (r + 1) v :=
  P.presentation.localComponent P.finiteSlice.nonzero v

theorem localComponent_ne_bot (v : FinitePlace F) : P.localComponent v ≠ ⊥ :=
  P.presentation.localComponent_ne_bot P.finiteSlice.nonzero v

theorem localComponent_isCuspidal (v : FinitePlace F) :
    (P.localComponent v).IsCuspidal :=
  P.presentation.localComponent_isCuspidal P.finiteSlice.nonzero v P.finiteSlice.isCuspidal

/-- The spectrum satisfies the normalized equations on the whole fixed space. -/
theorem hasSpectrum (v : FinitePlace F) (hv : v ∉ P.exceptional) :
    (P.localComponent v).HasSphericalHeckeSpectrum (P.spectralSystem.eigenvalues v hv) :=
  P.unramified.hasSpectrum v hv

/-- Enlarge the exceptional set while retaining the complete actual presentation. -/
def restrict {U : Finset (FinitePlace F)} (h : P.exceptional ⊆ U) :
    CuspidalSpectralPresentation S where
  finiteSlice := P.finiteSlice
  localFactor := P.localFactor
  tensorExceptional := P.tensorExceptional
  reference := P.reference
  reference_fixed := P.reference_fixed
  presentation := P.presentation
  exceptional := U
  unramified := P.unramified.restrict h

@[simp] theorem restrict_spectralSystem {U : Finset (FinitePlace F)}
    (h : P.exceptional ⊆ U) :
    (P.restrict h).spectralSystem = P.spectralSystem.restrict U h := rfl

variable (e : S.Equivalence T)

/-- Compose the genuine tensor equivalence with transport of the actual finite slice. -/
def transportedPresentation :
    FiniteTensorPresentation F (r + 1) (fun v => (P.localFactor v).representation)
      P.tensorExceptional P.reference P.reference_fixed (P.finiteSlice.transport e).subspace where
  reference_nonzero := P.presentation.reference_nonzero
  equiv := P.presentation.equiv.trans (P.finiteSlice.transportEquiv e)

/-- Full equivalence transports the actual slice, retaining the same factor family. -/
def transport : CuspidalSpectralPresentation T where
  finiteSlice := P.finiteSlice.transport e
  localFactor := P.localFactor
  tensorExceptional := P.tensorExceptional
  reference := P.reference
  reference_fixed := P.reference_fixed
  presentation := P.transportedPresentation e
  exceptional := P.exceptional
  unramified := P.unramified.transport (P.transportedPresentation e)
    (P.finiteSlice.transport e).nonzero

@[simp] theorem transport_spectralSystem :
    (P.transport e).spectralSystem = P.spectralSystem := rfl

/-- Local class equality follows from the unchanged genuine tensor family. -/
theorem transport_localComponent_isoClass (v : FinitePlace F) :
    ((P.transport e).localComponent v).isoClass = (P.localComponent v).isoClass :=
  (P.presentation.localComponentClass_eq (P.transportedPresentation e)
    P.finiteSlice.nonzero (P.finiteSlice.transport e).nonzero v).symm

end CuspidalSpectralPresentation

namespace CuspidalOperatorRealization
namespace IsoClass

variable {r : ℕ}

/-- An actual presentation witnesses attachment of a numerical spectrum to a full
cuspidal class. This relation does not assert existence or uniqueness. -/
def HasSpectralSystem (c : IsoClass F r) (s : SpectralSystem (FinitePlace F) (r + 1)) : Prop :=
  ∃ (S : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uV} S),
    S.isoClass = c ∧ P.spectralSystem = s

/-- An attached system can be witnessed at every actual representative. -/
theorem hasSpectralSystem_iff (S : CuspidalOperatorRealization F r)
    (s : SpectralSystem (FinitePlace F) (r + 1)) :
    HasSpectralSystem.{uF, uV} S.isoClass s ↔
      ∃ P : CuspidalSpectralPresentation.{uF, uV} S, P.spectralSystem = s := by
  constructor
  · rintro ⟨T, P, hc, hs⟩
    obtain ⟨e⟩ := (T.isoClass_eq_iff S).mp hc
    exact ⟨P.transport e, hs⟩
  · rintro ⟨P, hs⟩
    exact ⟨S, P, rfl, hs⟩

/-- Forgetting data at finitely many additional places preserves attachment. -/
theorem HasSpectralSystem.restrict {c : IsoClass F r}
    {s : SpectralSystem (FinitePlace F) (r + 1)}
    (hs : HasSpectralSystem.{uF, uV} c s) {U : Finset (FinitePlace F)}
    (h : s.exceptional ⊆ U) :
    HasSpectralSystem.{uF, uV} c (s.restrict U h) := by
  rcases hs with ⟨S, P, hc, rfl⟩
  exact ⟨S, P.restrict h, hc, rfl⟩

end IsoClass
end CuspidalOperatorRealization

namespace PositiveRankCuspidalClass

/-- The mixed-rank relation retains the rank of the actual cuspidal class. -/
def HasSpectralSystem (c : PositiveRankCuspidalClass F)
    (s : SpectralSystem (FinitePlace F) c.rank) : Prop :=
  CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uV} c.2 s

@[simp] theorem hasSpectralSystem_ofFixedRank {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass F r)
    (s : SpectralSystem (FinitePlace F) (r + 1)) :
    HasSpectralSystem.{uF, uV} (ofFixedRank c) s ↔
      CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uF, uV} c s := Iff.rfl

end PositiveRankCuspidalClass
end Langlands.Automorphic
