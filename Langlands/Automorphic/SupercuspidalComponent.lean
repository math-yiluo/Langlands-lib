import Langlands.Automorphic.PadicLocalCategory
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Correspondence.SupercuspidalRelations

/-!
# Supercuspidal local components of cuspidal classes

A local realization at a finite place is supercuspidal when it is irreducible
and admissible and its canonical `p`-adic class lies in the published
Jacquet-vanishing supercuspidal class space. A cuspidal class has a
supercuspidal component at `v` when some actual spectral presentation of a
representative has a supercuspidal local component at `v`.
-/

noncomputable section

universe uF uV

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F]

local instance supercuspidalComponentRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance supercuspidalComponentContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance supercuspidalComponentSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance supercuspidalComponentFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance supercuspidalComponentLocalSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ}

/-- The actual local realization is irreducible, admissible, and its canonical
`p`-adic class is supercuspidal. -/
def IsSupercuspidal (S : LocalRealization F (r + 1) v) : Prop :=
  ∃ (hI : S.IsIrreducible) (hA : S.IsAdmissible),
    Correspondence.IsSupercuspidalClass (CompletionPadic.padicField v) (S.padicClass hI hA)

/-- Supercuspidality depends only on the smooth isomorphism class. -/
theorem IsSupercuspidal.of_isoClass_eq {S T : LocalRealization F (r + 1) v}
    (hST : S.isoClass = T.isoClass) (hS : S.IsSupercuspidal) : T.IsSupercuspidal := by
  obtain ⟨hI, hA, hsc⟩ := hS
  obtain ⟨e⟩ := (S.isoClass_eq_iff T).mp hST
  have hI' : T.IsIrreducible := (Langlands.isIrreducible_iff_of_equiv e).mp hI
  have hA' : T.IsAdmissible := (Langlands.isAdmissible_iff_of_equiv e).mp hA
  refine ⟨hI', hA', ?_⟩
  rwa [← (S.padicClass_eq_iff_isoClass_eq T hI hA hI' hA').mpr hST]

/-- Supercuspidality is invariant under smooth isomorphism. -/
theorem isSupercuspidal_iff_of_isoClass_eq {S T : LocalRealization F (r + 1) v}
    (hST : S.isoClass = T.isoClass) : S.IsSupercuspidal ↔ T.IsSupercuspidal :=
  ⟨IsSupercuspidal.of_isoClass_eq hST, IsSupercuspidal.of_isoClass_eq hST.symm⟩

end LocalRealization

namespace CuspidalOperatorRealization.IsoClass

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The cuspidal class `c` has a supercuspidal local component at the finite
place `v`: some actual spectral presentation of a representative has a
supercuspidal local component at `v`. -/
def HasSupercuspidalComponent (c : IsoClass F r) (v : FinitePlace F) : Prop :=
  ∃ (S : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uV} S),
    S.isoClass = c ∧ (P.localComponent v).IsSupercuspidal

/-- A supercuspidal component can be witnessed at every actual representative. -/
theorem hasSupercuspidalComponent_iff (S : CuspidalOperatorRealization F r)
    (v : FinitePlace F) :
    HasSupercuspidalComponent.{uF, uV} S.isoClass v ↔
      ∃ P : CuspidalSpectralPresentation.{uF, uV} S, (P.localComponent v).IsSupercuspidal := by
  constructor
  · rintro ⟨T, P, hc, hP⟩
    obtain ⟨e⟩ := (T.isoClass_eq_iff S).mp hc
    refine ⟨P.transport e, ?_⟩
    exact hP.of_isoClass_eq (P.transport_localComponent_isoClass e v).symm
  · rintro ⟨P, hP⟩
    exact ⟨S, P, rfl, hP⟩

end CuspidalOperatorRealization.IsoClass

end Langlands.Automorphic
