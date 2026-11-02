import Langlands.Sheaf.Renard.GermDescent
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Renard II.2.1: universal properties of the actual germ sheafification

These proposition definitions specify the published units and descent maps.
The natural Hom equivalences and the actual direct adjunction are existential
conclusions. The original value universe is independent of the space universe.
-/

open CategoryTheory

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- Direct factorization and universal uniqueness for the actual descent map. -/
def GermUniversalFactorizationStatement (B : OpenBasis X) : Prop :=
  ∀ (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B) (ψ : F ⟶ G.obj),
    ((germSheafUnit.{u,v} B).app F ≫
        (sheafForget.{u,max u v} B).map (germDesc.{u,v} ψ) = ψ) ∧
    ∀ χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G,
      ((germSheafUnit.{u,v} B).app F ≫
          (sheafForget.{u,max u v} B).map χ = ψ ↔
        χ = germDesc.{u,v} ψ)

/-- At arbitrary original values, universal descent targets the actual joint lift. -/
def LiftedGermUniversalFactorizationStatement (B : OpenBasis X) : Prop :=
  ∀ (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B) (ψ : F ⟶ G.obj),
    ((germSheafLiftUnit.{u,v} B).app F ≫
        (sheafForget.{u,max u v} B).map (liftedGermDesc.{u,v} ψ) =
      (presheafLiftJoint.{u,v} B).map ψ) ∧
    ∀ χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G,
      ((germSheafLiftUnit.{u,v} B).app F ≫
          (sheafForget.{u,max u v} B).map χ =
        (presheafLiftJoint.{u,v} B).map ψ ↔
        χ = liftedGermDesc.{u,v} ψ)

/-- Inverse naturality in both variables for the literal direct descent maps. -/
def GermDescentNaturalityStatement (B : OpenBasis X) : Prop :=
  (∀ (E F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B)
      (φ : E ⟶ F) (ψ : F ⟶ G.obj),
    germDesc.{u,v} (φ ≫ ψ) =
      (germSheafFunctor.{u,max u v} B).map φ ≫ germDesc.{u,v} ψ) ∧
  (∀ (F : Presheaf.{u,max u v} B) (G H : BasisSheaf.{u,max u v} B)
      (ψ : F ⟶ G.obj) (θ : G ⟶ H),
    germDesc.{u,v} (ψ ≫ (sheafForget.{u,max u v} B).map θ) =
      germDesc.{u,v} ψ ≫ θ)

/-- Inverse naturality for lifted descent uses the actual sheaf lift on targets. -/
def LiftedGermDescentNaturalityStatement (B : OpenBasis X) : Prop :=
  (∀ (E F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B)
      (φ : E ⟶ F) (ψ : F ⟶ G.obj),
    liftedGermDesc.{u,v} (φ ≫ ψ) =
      (germSheafFunctor.{u,v} B).map φ ≫ liftedGermDesc.{u,v} ψ) ∧
  (∀ (F : Presheaf.{u,v} B) (G H : BasisSheaf.{u,v} B)
      (ψ : F ⟶ G.obj) (θ : G ⟶ H),
    liftedGermDesc.{u,v} (ψ ≫ (sheafForget.{u,v} B).map θ) =
      liftedGermDesc.{u,v} ψ ≫ (sheafLiftJoint.{u,v} B).map θ)

/-- Existence of the direct Hom equivalences, with specified maps and forward naturality. -/
def GermNaturalHomEquivalenceStatement (B : OpenBasis X) : Prop :=
  ∃ e : ∀ (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B),
      ((germSheafFunctor.{u,max u v} B).obj F ⟶ G) ≃ (F ⟶ G.obj),
    (∀ (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B)
        (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G),
      e F G χ =
        (germSheafUnit.{u,v} B).app F ≫ (sheafForget.{u,max u v} B).map χ) ∧
    (∀ (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B) (ψ : F ⟶ G.obj),
      (e F G).symm ψ = germDesc.{u,v} ψ) ∧
    (∀ (E F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B)
        (φ : E ⟶ F) (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G),
      e E G ((germSheafFunctor.{u,max u v} B).map φ ≫ χ) = φ ≫ e F G χ) ∧
    (∀ (F : Presheaf.{u,max u v} B) (G H : BasisSheaf.{u,max u v} B)
        (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G) (θ : G ⟶ H),
      e F H (χ ≫ θ) = e F G χ ≫ (sheafForget.{u,max u v} B).map θ)

/-- The lifted forward map lowers only the morphism between actual lifted presheaves. -/
def LiftedGermNaturalHomEquivalenceStatement (B : OpenBasis X) : Prop :=
  ∃ e : ∀ (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B),
      ((germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G) ≃
        (F ⟶ G.obj),
    (∀ (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B)
        (χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G),
      e F G χ = presheafLower.{u,v,u}
        ((germSheafLiftUnit.{u,v} B).app F ≫ (sheafForget.{u,max u v} B).map χ)) ∧
    (∀ (F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B) (ψ : F ⟶ G.obj),
      (e F G).symm ψ = liftedGermDesc.{u,v} ψ) ∧
    (∀ (E F : Presheaf.{u,v} B) (G : BasisSheaf.{u,v} B)
        (φ : E ⟶ F)
        (χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G),
      e E G ((germSheafFunctor.{u,v} B).map φ ≫ χ) = φ ≫ e F G χ) ∧
    (∀ (F : Presheaf.{u,v} B) (G H : BasisSheaf.{u,v} B)
        (χ : (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G)
        (θ : G ⟶ H),
      e F H (χ ≫ (sheafLiftJoint.{u,v} B).map θ) =
        e F G χ ≫ (sheafForget.{u,v} B).map θ)

/-- An actual direct adjunction with the canonical unit, Hom maps, and descent counit. -/
def GermAdjunctionStatement (B : OpenBasis X) : Prop :=
  ∃ a : germSheafFunctor.{u,max u v} B ⊣ sheafForget.{u,max u v} B,
    a.unit = germSheafUnit.{u,v} B ∧
    (∀ (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B)
        (χ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G),
      a.homEquiv F G χ =
        (germSheafUnit.{u,v} B).app F ≫ (sheafForget.{u,max u v} B).map χ) ∧
    (∀ (F : Presheaf.{u,max u v} B) (G : BasisSheaf.{u,max u v} B) (ψ : F ⟶ G.obj),
      (a.homEquiv F G).symm ψ = germDesc.{u,v} ψ) ∧
    (∀ G : BasisSheaf.{u,max u v} B,
      a.counit.app G = germDesc.{u,v} (𝟙 G.obj))

/-- The closed universal-property family for all supplied topologies and actual chosen bases. -/
def GermUniversalStatement : Prop :=
  ∀ (X : Type u) (_ : TopologicalSpace X) (B : OpenBasis X),
    GermUniversalFactorizationStatement.{u,v} B ∧
    LiftedGermUniversalFactorizationStatement.{u,v} B ∧
    GermDescentNaturalityStatement.{u,v} B ∧
    LiftedGermDescentNaturalityStatement.{u,v} B ∧
    GermNaturalHomEquivalenceStatement.{u,v} B ∧
    LiftedGermNaturalHomEquivalenceStatement.{u,v} B ∧
    GermAdjunctionStatement.{u,v} B

end Langlands.Sheaf.Renard
