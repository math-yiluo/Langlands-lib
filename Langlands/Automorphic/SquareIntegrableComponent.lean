import Langlands.Automorphic.PadicLocalCategory
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Representation.Classification.Tempered

/-!
# Square-integrable local components of cuspidal classes

A local realization at a finite place is square-integrable when it is
irreducible and its actual action of `GL_{r+1}(F_v)` is square-integrable
modulo the center, for the canonical `p`-adic topology of the completion. A
cuspidal class has a square-integrable component at `v` when some actual
spectral presentation of a representative has a square-integrable local
component at `v`.
-/

noncomputable section

universe uF uV

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F]

local instance squareIntegrableComponentRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance squareIntegrableComponentContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance squareIntegrableComponentSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance squareIntegrableComponentFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance squareIntegrableComponentLocalSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} {r : ℕ}

/-- The actual local realization is irreducible and its action of
`GL_{r+1}(F_v)` is square-integrable modulo the center, for the canonical
topology of the completion `F_v` as a finite extension of `ℚ_p`. -/
def IsSquareIntegrable (S : LocalRealization F (r + 1) v) : Prop :=
  S.IsIrreducible ∧
    (CompletionPadic.padicField v).canonicalTopologicalData.IsSquareIntegrable
      S.representation

/-- Square-integrability depends only on the smooth isomorphism class. -/
theorem IsSquareIntegrable.of_isoClass_eq {S T : LocalRealization F (r + 1) v}
    (hST : S.isoClass = T.isoClass) (hS : S.IsSquareIntegrable) : T.IsSquareIntegrable := by
  obtain ⟨hI, hsq⟩ := hS
  obtain ⟨e⟩ := (S.isoClass_eq_iff T).mp hST
  exact ⟨(Langlands.isIrreducible_iff_of_equiv e).mp hI,
    (PadicField.TopologicalData.isSquareIntegrable_iff_of_equiv e).mp hsq⟩

/-- Square-integrability is invariant under smooth isomorphism. -/
theorem isSquareIntegrable_iff_of_isoClass_eq {S T : LocalRealization F (r + 1) v}
    (hST : S.isoClass = T.isoClass) : S.IsSquareIntegrable ↔ T.IsSquareIntegrable :=
  ⟨IsSquareIntegrable.of_isoClass_eq hST, IsSquareIntegrable.of_isoClass_eq hST.symm⟩

end LocalRealization

namespace CuspidalOperatorRealization.IsoClass

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The cuspidal class `c` has a square-integrable local component at the
finite place `v`: some actual spectral presentation of a representative has a
square-integrable local component at `v`. -/
def HasSquareIntegrableComponent (c : IsoClass F r) (v : FinitePlace F) : Prop :=
  ∃ (S : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uV} S),
    S.isoClass = c ∧ (P.localComponent v).IsSquareIntegrable

/-- A square-integrable component can be witnessed at every actual representative. -/
theorem hasSquareIntegrableComponent_iff (S : CuspidalOperatorRealization F r)
    (v : FinitePlace F) :
    HasSquareIntegrableComponent.{uF, uV} S.isoClass v ↔
      ∃ P : CuspidalSpectralPresentation.{uF, uV} S,
        (P.localComponent v).IsSquareIntegrable := by
  constructor
  · rintro ⟨T, P, hc, hP⟩
    obtain ⟨e⟩ := (T.isoClass_eq_iff S).mp hc
    refine ⟨P.transport e, ?_⟩
    exact hP.of_isoClass_eq (P.transport_localComponent_isoClass e v).symm
  · rintro ⟨P, hP⟩
    exact ⟨S, P, rfl, hP⟩

end CuspidalOperatorRealization.IsoClass

end Langlands.Automorphic
