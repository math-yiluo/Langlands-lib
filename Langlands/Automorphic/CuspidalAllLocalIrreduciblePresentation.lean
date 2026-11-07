import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.PresentedLocalCategory

/-! # Actual cuspidal presentations irreducible at every finite place

Two proposition definitions for later proofs: existence of an irreducible
admissible actual finite slice, and existence of an auxiliary spectral
presentation, with factors in the form-space universe, whose actual local
components are irreducible and admissible at every finite place. Their derived
source provenance and proof route are described in the companion Markdown.
-/

noncomputable section

universe u uQ

namespace Langlands.Automorphic

open Langlands.Global

section

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance allLocalRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance allLocalContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance allLocalSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance allLocalFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance allLocalFiniteSpaceAddCommGroup (A : FiniteRealization F n) :
    AddCommGroup A.Space := Submodule.addCommGroup _

/-- Every actual cuspidal realization contains a nonzero actual finite slice
whose finite adelic action is irreducible and admissible. -/
def CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (S : CuspidalOperatorRealization F r),
    ∃ A : S.FiniteSlice,
      A.subspace.IsIrreducible ∧ Langlands.IsAdmissible A.subspace.representation

/-- Every actual cuspidal realization with a supplied presentation in any factor
universe also has an auxiliary presentation with factors in the form-space
universe, irreducible and admissible at every finite place. -/
def CuspidalAllLocalIrreduciblePresentationExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (S : CuspidalOperatorRealization F r)
    (_P : CuspidalSpectralPresentation.{u, uQ} S),
    ∃ Q : CuspidalSpectralPresentation.{u, u} S,
      ∀ v : FinitePlace F,
        (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible

end

end Langlands.Automorphic
