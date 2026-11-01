import Langlands.Automorphic.OperatorCMTransport
import Langlands.Automorphic.FiniteLocalCMTransport

/-! # Actual finite images of full CM operator realizations -/

noncomputable section
universe uK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {K : Type uK} [Field K] [NumberField K] [NumberField.IsCMField K] {n : ℕ}

local instance operatorCMComparisonRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance operatorCMComparisonContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance operatorCMComparisonFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance operatorCMComparisonFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance operatorCMComparisonStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization K n)

local instance operatorCMComparisonSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The finite action on the actual full CM image is genuinely equivalent to
the source finite action pulled back along arithmetic CM conjugation. -/
def complexConjFiniteEquiv :
    Representation.Equiv
      (S.finiteRepresentation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      S.complexConj.finiteRepresentation :=
  Representation.Equiv.mk S.complexConjEquiv.toLinearEquiv (fun g => by
    apply LinearMap.ext
    intro f
    exact (S.complexConjEquiv_finite g f).symm)

/-- The standard infinite compact transforms by its actual CM group map. -/
def complexConjCompactEquiv :
    Representation.Equiv
      (S.compactRepresentation.comp (CMConjugation.compactConj K n))
      S.complexConj.compactRepresentation :=
  Representation.Equiv.mk S.complexConjEquiv.toLinearEquiv (fun g => by
    apply LinearMap.ext
    intro f
    exact (S.complexConjEquiv_compact g f).symm)

@[simp] theorem complexConjFiniteEquiv_apply (f : S.Space) :
    S.complexConjFiniteEquiv f = S.complexConjEquiv f := rfl

@[simp] theorem complexConjCompactEquiv_apply (f : S.Space) :
    S.complexConjCompactEquiv f = S.complexConjEquiv f := rfl

/-- Taking the actual finite form image commutes with the actual full CM image. -/
@[simp] theorem toFiniteRealization_complexConj :
    S.complexConj.toFiniteRealization = S.toFiniteRealization.complexConj := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro f
  change (∃ g : S.complexConj.Space, S.complexConj.formInclusion g = f) ↔
    ∃ g, (∃ h : S.Space, S.formInclusion h = g) ∧ AutomorphicForms.complexConj n g = f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨S.formInclusion (S.complexConjEquiv.symm g),
      ⟨S.complexConjEquiv.symm g, rfl⟩, ?_⟩
    have h := S.formInclusion_complexConjEquiv (S.complexConjEquiv.symm g)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
    exact ⟨S.complexConjEquiv h, S.formInclusion_complexConjEquiv h⟩

/-- The same comparison on actual finite images retains the canonical finite
image equivalences on both sides. -/
def complexConjFiniteImageEquiv :
    Representation.Equiv
      (S.toFiniteRealization.representation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      S.complexConj.toFiniteRealization.representation := by
  let e : Representation.Equiv
      (S.finiteRepresentation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      (S.toFiniteRealization.representation.comp (CMConjugation.finiteConj K n).toMonoidHom) :=
    Representation.Equiv.mk S.finiteEquiv.toLinearEquiv
      (fun g => S.finiteEquiv.isIntertwining' (CMConjugation.finiteConj K n g))
  let e' : Representation.Equiv
      (S.finiteRepresentation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      S.complexConj.toFiniteRealization.representation :=
    Representation.Equiv.trans
      (ρ := S.finiteRepresentation.comp (CMConjugation.finiteConj K n).toMonoidHom)
      (σ := S.complexConj.finiteRepresentation)
      (τ := S.complexConj.toFiniteRealization.representation)
      S.complexConjFiniteEquiv S.complexConj.finiteEquiv
  exact Representation.Equiv.trans
    (ρ := S.toFiniteRealization.representation.comp
      (CMConjugation.finiteConj K n).toMonoidHom)
    (σ := S.finiteRepresentation.comp (CMConjugation.finiteConj K n).toMonoidHom)
    (τ := S.complexConj.toFiniteRealization.representation) e.symm e'

@[simp] theorem complexConjFiniteImageEquiv_apply (f : S.Space) :
    S.complexConjFiniteImageEquiv (S.finiteEquiv f) =
      S.complexConj.finiteEquiv (S.complexConjEquiv f) := by
  change S.complexConj.finiteEquiv
    (S.complexConjEquiv (S.finiteEquiv.symm (S.finiteEquiv f))) = _
  exact congrArg (fun x : S.Space => S.complexConj.finiteEquiv (S.complexConjEquiv x))
    (S.finiteEquiv.symm_apply_apply f)

@[simp] theorem evaluate_complexConjFiniteImageEquiv (f : S.Space) (g : AdelicGL K n) :
    evaluate K n (S.complexConj.toFiniteRealization.toContinuous
        (S.complexConjFiniteImageEquiv (S.finiteEquiv f))) g =
      evaluate K n (S.toContinuous f) (CMConjugation.adelicConj K n g) := by
  rw [complexConjFiniteImageEquiv_apply]
  exact S.evaluate_complexConjEquiv f g

/-- At corresponding finite places the actual embedded whole-carrier local
restrictions agree as well. -/
@[simp] theorem toLocal_toFiniteRealization_complexConj (v : FinitePlace K) :
    S.complexConj.toFiniteRealization.toLocal K n
        (AdelicFunctoriality.finitePlaceEquiv (CMConjugation.fieldConj K) v) =
      (S.toFiniteRealization.toLocal K n v).complexConj := by
  rw [toFiniteRealization_complexConj, FiniteRealization.toLocal_complexConj]

end OperatorRealization
end Langlands.Automorphic
