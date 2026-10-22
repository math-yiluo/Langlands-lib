import Langlands.AlgebraicGeometry.Modules.RigidificationBaseChange
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry

/-! # Rigidified line bundles and their pullback -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule.RigidifiedModule

variable {S X S' X' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'}

/-- Pullback of rigidified modules with the canonical structure-sheaf comparison. -/
def pullback (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) :
    RigidifiedModule ε ⥤ RigidifiedModule ε' :=
  pullbackWithUnit f g comm (Langlands.Scheme.Modules.pullbackUnitIso g).symm

/-- Canonical rigidified pullback has the ordinary underlying module pullback. -/
def pullbackForgetIso (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) :
    pullback f g comm ⋙ forget ε' ≅ forget ε ⋙ Scheme.Modules.pullback f :=
  Iso.refl _

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

variable {S X S' X' : Scheme.{u}}

/-- Rigidified modules whose underlying sheaves are locally free of rank one. -/
abbrev RigidifiedLineBundle (ε : S ⟶ X) :=
  ObjectProperty.FullSubcategory
    (fun M : RigidifiedModule ε ↦ IsLocallyFreeRankOne M.carrier)

namespace RigidifiedLineBundle

variable {ε : S ⟶ X} {ε' : S' ⟶ X'}

/-- Equip an actual line bundle with a specified rigidification. -/
def ofLineBundle (L : LineBundle X)
    (α : structureModule S ≅ (Scheme.Modules.pullback ε).obj L.obj) :
    RigidifiedLineBundle ε :=
  ⟨⟨L.obj, α⟩, L.property⟩

/-- Forget only the local rank-one property, retaining the rigidification. -/
def forgetToRigidified (ε : S ⟶ X) :
    RigidifiedLineBundle ε ⥤ RigidifiedModule ε :=
  ObjectProperty.ι _

/-- Forget the rigidification, retaining the underlying line bundle. -/
def forget (ε : S ⟶ X) : RigidifiedLineBundle ε ⥤ LineBundle X :=
  ObjectProperty.lift IsLocallyFreeRankOne
    (forgetToRigidified ε ⋙ RigidifiedModule.forget ε) (fun L ↦ L.property)

instance : (forget ε).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    exact congrArg (fun k ↦ k.hom) h

/-- The structure sheaf with its canonical rigidification. -/
def trivial (ε : S ⟶ X) : RigidifiedLineBundle ε :=
  ofLineBundle (LineBundle.trivial X) (Langlands.Scheme.Modules.pullbackUnitIso ε).symm

/-- Construct an isomorphism from a compatible isomorphism of the module sheaves. -/
def isoMk {L M : RigidifiedLineBundle ε} (e : L.obj.carrier ≅ M.obj.carrier)
    (comm : L.obj.rigidification.hom ≫ (Scheme.Modules.pullback ε).map e.hom =
      M.obj.rigidification.hom) : L ≅ M :=
  ObjectProperty.isoMk _ (RigidifiedModule.isoMk e comm)

/-- Transport the rigidification and local rank-one property along an isomorphism. -/
def transport (L : RigidifiedLineBundle ε) {M : X.Modules} (e : L.obj.carrier ≅ M) :
    RigidifiedLineBundle ε :=
  ⟨RigidifiedModule.transport L.obj e, L.property.of_iso e⟩

/-- The transported object is isomorphic as a rigidified line bundle. -/
def transportIso (L : RigidifiedLineBundle ε) {M : X.Modules} (e : L.obj.carrier ≅ M) :
    L ≅ transport L e :=
  ObjectProperty.isoMk _ (RigidifiedModule.transportIso L.obj e)

/-- Pullback of rigidified line bundles along a commuting square of schemes. -/
def pullback (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) :
    RigidifiedLineBundle ε ⥤ RigidifiedLineBundle ε' :=
  ObjectProperty.lift (fun M : RigidifiedModule ε' ↦ IsLocallyFreeRankOne M.carrier)
    (forgetToRigidified ε ⋙ RigidifiedModule.pullback f g comm)
    (fun L ↦ L.property.pullback f)

/-- Forgetting rigidification recovers the actual line-bundle pullback. -/
def pullbackForgetIso (f : X' ⟶ X) (g : S' ⟶ S) (comm : ε' ≫ f = g ≫ ε) :
    pullback f g comm ⋙ forget ε' ≅ forget ε ⋙ LineBundle.pullback f :=
  Iso.refl _

/-- The category of rigidified line bundles over a member of the relative family. -/
abbrev relative (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    (T : Over S) :=
  RigidifiedLineBundle ((relativeSection f ε section_eq).app T)

/-- Pullback along a morphism of base schemes in the relative family. -/
def relativePullback (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    {T U : Over S} (h : T ⟶ U) :
    relative f ε section_eq U ⥤ relative f ε section_eq T :=
  pullback ((relativeSpace f).map h) h.left
    ((relativeSection f ε section_eq).naturality h).symm

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
