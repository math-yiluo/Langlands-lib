import Langlands.Representation.Exponents.DualJacquet
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite spectrum of a commutative action with finite operator span

A derived algebraic statement: if the actual operators of a commutative group
span a finite-dimensional space of endomorphisms and depend locally constantly
on the group element, then only finitely many open-kernel characters occur as
ordinary eigencharacters, each generalized component has a finite uniform
nilpotence order, and these components span the whole carrier. The carrier
itself need not be finite dimensional. This is a statement, not a proof.
-/

namespace Langlands

universe uA uV

/-- For a commutative group acting on a complex vector space whose action
operators span a finite-dimensional subspace of `Module.End ℂ V` and depend
locally constantly on the group element, the open-kernel characters with a
nonzero ordinary eigenspace form a finite set, each of them has a finite
uniform nilpotence index on its entire generalized component, and the
generalized components of exactly these characters span the carrier. -/
def FiniteActionCommutativeSpectrumStatement : Prop :=
  ∀ (A : Type uA) [CommGroup A] [TopologicalSpace A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ A V),
    Module.Finite ℂ (Submodule.span ℂ (Set.range ρ)) →
    IsLocallyConstant (fun a : A => ρ a) →
      {χ : A →* ℂˣ |
        IsOpen (χ.ker : Set A) ∧
          commutativeCharacterSpace ρ χ 1 ≠ ⊥}.Finite ∧
      (∀ χ : A →* ℂˣ,
        (IsOpen (χ.ker : Set A) ∧
          commutativeCharacterSpace ρ χ 1 ≠ ⊥) →
          commutativeCharacterNilpotenceIndex ρ χ < ⊤) ∧
      (⨆ (χ : A →* ℂˣ)
          (_ : IsOpen (χ.ker : Set A) ∧
            commutativeCharacterSpace ρ χ 1 ≠ ⊥),
        (generalizedCommutativeCharacterSpace ρ χ).toSubmodule) = ⊤

end Langlands
