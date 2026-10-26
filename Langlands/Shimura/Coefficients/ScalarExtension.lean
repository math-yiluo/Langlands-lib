import Langlands.Shimura.Coefficients.ScalarRestriction
import Langlands.Geometry.EtaleScalarExtension

/-! # Adjoint scalar extension of associated coefficient sheaves -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry Langlands.Geometry.EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable (X : Scheme.{u}) {G : Type u} [Group G]

/-- The tensor-sheaf unit is equivariant for every coefficient action. -/
def coefficientExtensionActionUnit :
    𝟭 (Action (EtaleDerivedSections.ModuleSheaf X R) G) ⟶
      (sheafExtendScalars φ X).mapAction G ⋙ (sheafRestrictScalars φ X).mapAction G where
  app F :=
    { hom := (sheafExtensionUnit φ X).app F.V
      comm g := (sheafExtensionUnit φ X).naturality (F.ρ g) }
  naturality {F F'} f := by
    apply Action.hom_injective
    exact (sheafExtensionUnit φ X).naturality f.hom

variable (Y : Action X.Etale G)

/-- Map an invariant sheaf to the restricted associated scalar extension. -/
def associatedExtensionUnit :
    associatedFunctor X.smallEtaleTopology Y ⟶
      (sheafExtendScalars φ X).mapAction G ⋙
        associatedFunctor X.smallEtaleTopology Y ⋙ sheafRestrictScalars φ X :=
  Functor.whiskerRight (coefficientExtensionActionUnit φ X)
      (associatedFunctor X.smallEtaleTopology Y) ≫
    Functor.whiskerLeft ((sheafExtendScalars φ X).mapAction G)
      (associatedRestrictScalarsIso X.smallEtaleTopology φ Y).inv

/-- The associated unit retains the ordinary inclusion into sections over the cover. -/
@[reassoc (attr := simp)]
theorem associatedExtensionUnit_inclusion
    (F : Action (EtaleDerivedSections.ModuleSheaf X R) G) :
    (associatedExtensionUnit φ X Y).app F ≫
        (sheafRestrictScalars φ X).map
          (inclusion X.smallEtaleTopology Y ((sheafExtendScalars φ X).mapAction G |>.obj F)) =
      inclusion X.smallEtaleTopology Y F ≫
        (productSheaf X.smallEtaleTopology Y.V).map ((sheafExtensionUnit φ X).app F.V) := by
  dsimp only [associatedExtensionUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc]
  erw [associatedRestrictScalarsIso_inv_inclusion X.smallEtaleTopology φ Y
    (((sheafExtendScalars φ X).mapAction G).obj F)]
  exact inclusion_natural X.smallEtaleTopology Y ((coefficientExtensionActionUnit φ X).app F)

/-- Canonical adjoint comparison from extension of invariants to invariants of extension. -/
def associatedExtendScalarsComparison :
    associatedFunctor X.smallEtaleTopology Y ⋙ sheafExtendScalars φ X ⟶
      (sheafExtendScalars φ X).mapAction G ⋙ associatedFunctor X.smallEtaleTopology Y where
  app F := sheafExtensionLift φ X ((associatedExtensionUnit φ X Y).app F)
  naturality {F F'} f := by
    change (sheafExtendScalars φ X).map
        ((associatedFunctor X.smallEtaleTopology Y).map f) ≫
          sheafExtensionLift φ X ((associatedExtensionUnit φ X Y).app F') =
      sheafExtensionLift φ X ((associatedExtensionUnit φ X Y).app F) ≫
        (associatedFunctor X.smallEtaleTopology Y).map
          (((sheafExtendScalars φ X).mapAction G).map f)
    rw [← sheafExtensionLift_precomp, ← sheafExtensionLift_postcomp]
    exact congrArg (sheafExtensionLift φ X)
      ((associatedExtensionUnit φ X Y).naturality f)

/-- The comparison is the adjoint transpose of the constructed associated unit. -/
@[reassoc (attr := simp)]
theorem associatedExtendScalarsComparison_unit
    (F : Action (EtaleDerivedSections.ModuleSheaf X R) G) :
    (sheafExtensionUnit φ X).app (associated X.smallEtaleTopology Y F) ≫
        (sheafRestrictScalars φ X).map ((associatedExtendScalarsComparison φ X Y).app F) =
      (associatedExtensionUnit φ X Y).app F :=
  sheafExtensionUnit_lift φ X _

/-- The unit equation determines the scalar-extension comparison uniquely. -/
theorem associatedExtendScalarsComparison_unique
    (F : Action (EtaleDerivedSections.ModuleSheaf X R) G)
    (f : (sheafExtendScalars φ X).obj (associated X.smallEtaleTopology Y F) ⟶
      associated X.smallEtaleTopology Y ((sheafExtendScalars φ X).mapAction G |>.obj F))
    (h : (sheafExtensionUnit φ X).app (associated X.smallEtaleTopology Y F) ≫
      (sheafRestrictScalars φ X).map f = (associatedExtensionUnit φ X Y).app F) :
    f = (associatedExtendScalarsComparison φ X Y).app F :=
  sheafExtensionLift_unique φ X _ f h

/-- The comparison carries invariant sections into the tensor-sheaf extension. -/
@[reassoc]
theorem associatedExtendScalarsComparison_unit_inclusion
    (F : Action (EtaleDerivedSections.ModuleSheaf X R) G) :
    (sheafExtensionUnit φ X).app (associated X.smallEtaleTopology Y F) ≫
        (sheafRestrictScalars φ X).map
          ((associatedExtendScalarsComparison φ X Y).app F ≫
            inclusion X.smallEtaleTopology Y
              ((sheafExtendScalars φ X).mapAction G |>.obj F)) =
      inclusion X.smallEtaleTopology Y F ≫
        (productSheaf X.smallEtaleTopology Y.V).map ((sheafExtensionUnit φ X).app F.V) := by
  rw [Functor.map_comp, ← Category.assoc, associatedExtendScalarsComparison_unit,
    associatedExtensionUnit_inclusion]

end Langlands.Shimura.Coefficients
