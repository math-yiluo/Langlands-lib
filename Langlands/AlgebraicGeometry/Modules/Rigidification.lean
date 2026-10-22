import Langlands.AlgebraicGeometry.Modules.SectionLocus

/-! # Rigidified sheaves of modules -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule

variable {S X : Scheme.{u}}

/-- A sheaf of modules with a chosen trivialization after pullback along `ε`. -/
structure RigidifiedModule (ε : S ⟶ X) where
  carrier : X.Modules
  rigidification : structureModule S ≅ (Scheme.Modules.pullback ε).obj carrier

namespace RigidifiedModule

variable {ε : S ⟶ X}

/-- A module homomorphism compatible with the chosen rigidifications. -/
def Hom (M N : RigidifiedModule ε) :=
  {f : M.carrier ⟶ N.carrier //
    M.rigidification.hom ≫ (Scheme.Modules.pullback ε).map f = N.rigidification.hom}

instance : Category (RigidifiedModule ε) where
  Hom := Hom
  id M := ⟨𝟙 M.carrier, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by
    rw [Functor.map_comp, ← Category.assoc, f.property, g.property]⟩
  id_comp f := by apply Subtype.ext; exact Category.id_comp f.val
  comp_id f := by apply Subtype.ext; exact Category.comp_id f.val
  assoc f g h := by apply Subtype.ext; exact Category.assoc f.val g.val h.val

/-- Forgetting the chosen rigidification keeps the actual module and its morphisms. -/
def forget (ε : S ⟶ X) : RigidifiedModule ε ⥤ X.Modules where
  obj M := M.carrier
  map f := f.val

instance : (forget ε).Faithful where
  map_injective := Subtype.ext

/-- Build an isomorphism of rigidified modules from a compatible module isomorphism. -/
def isoMk {M N : RigidifiedModule ε} (e : M.carrier ≅ N.carrier)
    (comm : M.rigidification.hom ≫ (Scheme.Modules.pullback ε).map e.hom =
      N.rigidification.hom) : M ≅ N where
  hom := ⟨e.hom, comm⟩
  inv := ⟨e.inv, by
    rw [← comm, Category.assoc, ← Functor.map_comp, e.hom_inv_id]
    simp⟩
  hom_inv_id := by apply Subtype.ext; exact e.hom_inv_id
  inv_hom_id := by apply Subtype.ext; exact e.inv_hom_id

/-- Transport a rigidification along an actual isomorphism of the underlying modules. -/
def transport (M : RigidifiedModule ε) {N : X.Modules} (e : M.carrier ≅ N) :
    RigidifiedModule ε where
  carrier := N
  rigidification := M.rigidification ≪≫ (Scheme.Modules.pullback ε).mapIso e

/-- Transport preserves the rigidified module up to its specified compatible isomorphism. -/
def transportIso (M : RigidifiedModule ε) {N : X.Modules} (e : M.carrier ≅ N) :
    M ≅ transport M e :=
  isoMk e rfl

end RigidifiedModule
end Langlands.SchemeModule
