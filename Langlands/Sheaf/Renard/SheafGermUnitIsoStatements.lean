import Langlands.Sheaf.Renard.GermDescent

/-!
# Renard II.2.1: the canonical germ unit on sheaves

These proposition definitions state bijectivity of the original section map,
invertibility of the actual canonical units, and natural isomorphisms with
those units as forward maps and descent of identity as inverse maps.
They supply no proofs.
-/

open CategoryTheory

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The actual original-section germ map of a basis sheaf is bijective on every basis open. -/
def SheafSectionGermsBijectiveStatement (G : BasisSheaf.{u,v} B) : Prop :=
  ∀ U : BasisOpen B, Function.Bijective (sectionGerms G.obj.obj U)

/-- The actual lifted canonical unit is invertible at a basis sheaf. -/
def SheafGermLiftUnitIsIsoStatement (G : BasisSheaf.{u,v} B) : Prop :=
  IsIso ((germSheafLiftUnit.{u,v} B).app G.obj)

/-- The lifted sheaf is naturally identified with its germ sheaf by the canonical unit,
with inverse equal to the published lifted descent of identity. -/
def SheafGermLiftUnitNatIsoStatement (B : OpenBasis X) : Prop :=
  ∃ e : sheafLiftJoint.{u,v} B ≅
      sheafForget.{u,v} B ⋙ germSheafFunctor.{u,v} B,
    ∀ G : BasisSheaf.{u,v} B,
      (sheafForget.{u,max u v} B).map (e.hom.app G) =
          (germSheafLiftUnit.{u,v} B).app G.obj ∧
        e.inv.app G = liftedGermDesc.{u,v} (𝟙 G.obj)

/-- At the joint value universe, the actual identity-source canonical unit is invertible. -/
def SheafGermUnitIsIsoStatement (G : BasisSheaf.{u,max u v} B) : Prop :=
  IsIso ((germSheafUnit.{u,v} B).app G.obj)

/-- The identity-source natural isomorphism at the joint value universe has the canonical
unit as its underlying forward map and descent of identity as its inverse. -/
def SheafGermUnitNatIsoStatement (B : OpenBasis X) : Prop :=
  ∃ e : 𝟭 (BasisSheaf.{u,max u v} B) ≅
      sheafForget.{u,max u v} B ⋙ germSheafFunctor.{u,max u v} B,
    ∀ G : BasisSheaf.{u,max u v} B,
      (sheafForget.{u,max u v} B).map (e.hom.app G) =
          (germSheafUnit.{u,v} B).app G.obj ∧
        e.inv.app G = germDesc.{u,v} (𝟙 G.obj)

/-- The closed canonical germ-unit invertibility target, for every space, supplied topology
and chosen open basis, with independent space and original-section universes. -/
def RenardSheafGermUnitIsoStatement : Prop :=
  ∀ (X : Type u) (_ : TopologicalSpace X) (B : OpenBasis X),
    (∀ G : BasisSheaf.{u,v} B, SheafSectionGermsBijectiveStatement G) ∧
    (∀ G : BasisSheaf.{u,v} B, SheafGermLiftUnitIsIsoStatement G) ∧
    SheafGermLiftUnitNatIsoStatement.{u,v} B ∧
    (∀ G : BasisSheaf.{u,max u v} B, SheafGermUnitIsIsoStatement.{u,v} G) ∧
    SheafGermUnitNatIsoStatement.{u,v} B

end Langlands.Sheaf.Renard
