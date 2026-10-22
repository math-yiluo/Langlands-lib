import Langlands.Representation.CuspidalSupport.LeviDefinitions

/-! Algebraic relation laws for the actual Weyl-association predicates. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW uX

/-- Association of actual standard Levi subgroups is an equivalence relation. -/
def LeviAssociationEquivalenceTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (n : ℕ),
    (∀ B : BlockShape n, LevisAssociated (F := F) B B) ∧
    (∀ B C : BlockShape n,
      LevisAssociated (F := F) B C → LevisAssociated (F := F) C B) ∧
    (∀ B C D : BlockShape n,
      LevisAssociated (F := F) B C → LevisAssociated (F := F) C D →
        LevisAssociated (F := F) B D)

/-- Every actual Levi representation is associated to itself. -/
def RepresentationAssociationReflexivityTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (n : ℕ) (B : BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V),
    RepresentationsAssociated B B ρ ρ

/-- Association is symmetric across independent representation universes. -/
def RepresentationAssociationSymmetryTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (n : ℕ) (B C : BlockShape n)
    (V : Type uV) (W : Type uW)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B.Levi F) V)
    (σ : Representation ℂ (C.Levi F) W),
    RepresentationsAssociated B C ρ σ → RepresentationsAssociated C B σ ρ

/-- Association composes through a third, independently sized carrier. -/
def RepresentationAssociationTransitivityTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (n : ℕ) (B C D : BlockShape n)
    (V : Type uV) (W : Type uW) (X : Type uX)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (B.Levi F) V)
    (σ : Representation ℂ (C.Levi F) W)
    (τ : Representation ℂ (D.Levi F) X),
    RepresentationsAssociated B C ρ σ → RepresentationsAssociated C D σ τ →
      RepresentationsAssociated B D ρ τ

/-- The algebraic association laws needed to compose the two associations
obtained from a common Jacquet constituent. -/
def AssociationRelationLawsTheorem : Prop :=
  LeviAssociationEquivalenceTheorem.{uF} ∧
  RepresentationAssociationReflexivityTheorem.{uF, uV} ∧
  RepresentationAssociationSymmetryTheorem.{uF, uV, uW} ∧
  RepresentationAssociationTransitivityTheorem.{uF, uV, uW, uX}

end Langlands.CuspidalSupport
