import Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement
import Langlands.Automorphic.CuspidalWhittaker.LocalFunctional
import Langlands.Automorphic.LocalWhittakerCharacterBridge
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-!
# Actual local genericity of cuspidal presentations

Every irreducible admissible local component of a spectral presentation of a cuspidal
realization is generic for every nontrivial unitary additive character of the local field.
The global Whittaker coefficient gives a nonzero functional on the local component that is
equivariant for the local component of the standard character of `𝔸_K / K`; that character is
trivial on the local integers and nontrivial, so the character-change bridge applies.
-/

noncomputable section

universe uF uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.HarmonicAnalysis
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- **Local genericity** of the actual local components of cuspidal spectral presentations. -/
theorem cuspidalUnitaryLocalGenericity : CuspidalUnitaryLocalGenericityStatement.{uF, uQ} := by
  intro F _ _ _ r T _ P v hI hA
  have hne : CuspidalWhittaker.localCharacter F v ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := CuspidalWhittaker.exists_localCharacter_ne_one F v
    exact ht (by rw [h, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional (P.localComponent v)
    (P.localComponent_isCuspidal v) (P.localComponent_ne_bot v)
  exact (P.localComponent v).isGeneric_of_integerTrivial_character hI hA
    (CuspidalWhittaker.localCharacter F v) hne
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one F hx) ℓ hℓ heq

variable {K : Type uF} [Field K] [NumberField K] {n : ℕ}

local instance genericRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance genericContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance genericSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance genericFormAddCommGroup : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance genericLocalAddCommGroup {v : FinitePlace K} (A : LocalRealization K n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- An irreducible admissible component of a unitary cusp is generic for a nontrivial
unitary additive character of the actual finite completion. -/
theorem CuspidalSpectralPresentation.exists_generic_at_completion
    {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} {S : CuspidalOperatorRealization F r}
    (P : CuspidalSpectralPresentation.{uF, uQ} S) (hS : HasUnitaryCentralCharacter S)
    (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible) :
    ∃ ψ : UnitaryAdditiveCharacter (FiniteCompletion F v),
      Whittaker.IsGeneric ψ r (P.localComponent v).representation := by
  let Fv := CompletionPadic.padicField v
  let T := Fv.canonicalTopologicalData
  obtain ⟨ψ⟩ := padicUnitaryAdditiveCharacterExists Fv T
  have hgen := cuspidalUnitaryLocalGenericity F r S hS P v hI hA ψ
  let genericAtTopology (t : TopologicalSpace (FiniteCompletion F v)) : Prop :=
    letI := t
    ∃ ψ : UnitaryAdditiveCharacter (FiniteCompletion F v),
      Whittaker.IsGeneric ψ r (P.localComponent v).representation
  have hcanonical : genericAtTopology T.topology := ⟨ψ, hgen⟩
  exact (congrArg genericAtTopology (CompletionPadic.completion_topology_eq v)).mpr hcanonical

end Langlands.Automorphic
