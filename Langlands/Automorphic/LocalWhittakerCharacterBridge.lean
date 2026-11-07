import Langlands.Automorphic.PadicLocalCategory
import Langlands.Representation.Whittaker.PadicCharacterIndependence

/-! # Raw-character Whittaker functionals on actual automorphic local components -/

noncomputable section

universe uF

namespace Langlands.Global.CompletionPadic

open Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F] (v : FinitePlace F)

/-- Bundle an integer-trivial completion character with continuity for the
canonical p-adic topology, retaining its original values. -/
def unitaryAdditiveCharacterOfTrivialOnIntegers
    (χ : AddChar (FiniteCompletion F v) Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ v.adicCompletionIntegers F, χ x = 1) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
      (padicField v).canonicalTopologicalData.topology :=
  (padicField v).canonicalTopologicalData.unitaryAdditiveCharacterOfTrivialOnIntegers
    χ hχ (fun x hx => hO x ((mem_localIntegers_iff_canonical F v x).mpr hx))

@[simp]
theorem unitaryAdditiveCharacterOfTrivialOnIntegers_apply
    (χ : AddChar (FiniteCompletion F v) Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ v.adicCompletionIntegers F, χ x = 1) (x : FiniteCompletion F v) :
    unitaryAdditiveCharacterOfTrivialOnIntegers v χ hχ hO x = χ x := rfl

end Langlands.Global.CompletionPadic

namespace Langlands.Automorphic.LocalRealization

open Langlands.Global Langlands.Global.CompletionPadic

variable {F : Type uF} [Field F] [NumberField F] {v : FinitePlace F} {r : ℕ}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance (S : LocalRealization F (r + 1) v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable (S : LocalRealization F (r + 1) v)

/-- An actual raw-character functional, as a standard Whittaker functional on
the same local action for the canonical p-adic field topology. -/
def whittakerFunctionalOfIntegerTrivial
    (χ : AddChar (FiniteCompletion F v) Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ v.adicCompletionIntegers F, χ x = 1)
    (ℓ : Module.Dual ℂ S.Space)
    (heq : ∀ (u : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) (x : S.Space),
      ℓ (S.representation u.val x) =
        (χ (∑ i : Fin r, u.val i.castSucc i.succ) : ℂ) * ℓ x) :
    letI := (padicField v).canonicalTopologicalData.topology
    Whittaker.glFunctionals (unitaryAdditiveCharacterOfTrivialOnIntegers v χ hχ hO)
      r S.representation :=
  ⟨ℓ, heq⟩

/-- A nonzero raw-character functional implies genericity of exactly the
original canonical p-adic object, for every continuous nontrivial character. -/
theorem isGeneric_of_integerTrivial_character
    (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (χ : AddChar (FiniteCompletion F v) Circle) (hχ : χ ≠ 1)
    (hO : ∀ x ∈ v.adicCompletionIntegers F, χ x = 1)
    (ℓ : Module.Dual ℂ S.Space) (hℓ : ℓ ≠ 0)
    (heq : ∀ (u : GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v)) (x : S.Space),
      ℓ (S.representation u.val x) =
        (χ (∑ i : Fin r, u.val i.castSucc i.succ) : ℂ) * ℓ x) :
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
    ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier,
      Whittaker.IsGeneric ψ r ((S.padicObject hI hA).obj.representation) := by
  let := (padicField v).canonicalTopologicalData.topology
  let := (padicField v).canonicalGeneralLinearTopology (r + 1)
  intro ψ
  let χ' := unitaryAdditiveCharacterOfTrivialOnIntegers v χ hχ hO
  change Whittaker.IsGeneric ψ r S.representation
  apply ((padicField v).canonicalTopologicalData.isGeneric_iff_character
    S.representation χ' ψ).mp
  exact ⟨hI, S.isAdmissible_canonical_iff.mpr hA,
    ⟨S.whittakerFunctionalOfIntegerTrivial χ hχ hO ℓ heq, hℓ⟩⟩

end Langlands.Automorphic.LocalRealization
