import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-! # Adjusting a trivialization to respect a rigidification -/

universe u v w

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace RigidificationAdjustment

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
  (F : C ⥤ D) (G : D ⥤ C) (η : G ⋙ F ≅ 𝟭 D)
  {A : C} {B : D} (e : G.obj B ≅ A)

/-- Lift an automorphism through a functor with a specified right inverse,
at an object isomorphic to one in the image of that right inverse. -/
def liftAutomorphism (a : F.obj A ≅ F.obj A) : A ≅ A :=
  e.symm ≪≫
    G.mapIso ((η.app B).symm ≪≫ F.mapIso e ≪≫ a ≪≫
      (F.mapIso e).symm ≪≫ η.app B) ≪≫ e

lemma map_liftAutomorphism (a : F.obj A ≅ F.obj A) :
    F.map (liftAutomorphism F G η e a).hom = a.hom := by
  let b := (η.app B).symm ≪≫ F.mapIso e ≪≫ a ≪≫
    (F.mapIso e).symm ≪≫ η.app B
  have hn : F.map (G.map b.hom) ≫ (η.app B).hom =
      (η.app B).hom ≫ b.hom := η.hom.naturality b.hom
  have he : F.map (G.map b.hom) =
      (η.app B).hom ≫ b.hom ≫ (η.app B).inv := by
    rw [← Category.assoc, ← hn]
    simp
  change F.map (e.inv ≫ G.map b.hom ≫ e.hom) = a.hom
  simp only [Functor.map_comp, he]
  dsimp [b]
  simp [Category.assoc, ← Functor.map_comp]

/-- Correct an isomorphism using a prescribed comparison after applying `F`. -/
def adjustIso {M : C} {U : D} (q : M ≅ A)
    (α : U ≅ F.obj M) (β : U ≅ F.obj A) : M ≅ A :=
  q ≪≫ liftAutomorphism F G η e ((F.mapIso q).symm ≪≫ α.symm ≪≫ β)

lemma adjustIso_compatible {M : C} {U : D} (q : M ≅ A)
    (α : U ≅ F.obj M) (β : U ≅ F.obj A) :
    α.hom ≫ F.map (adjustIso F G η e q α β).hom = β.hom := by
  change α.hom ≫ F.map (q.hom ≫
    (liftAutomorphism F G η e ((F.mapIso q).symm ≪≫ α.symm ≪≫ β)).hom) = β.hom
  rw [Functor.map_comp, map_liftAutomorphism]
  simp

end RigidificationAdjustment

namespace RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- An ordinary trivialization can be adjusted to respect any chosen
rigidification along a section. -/
def trivialIsoOfCarrierIso (L : RigidifiedLineBundle ε)
    (e : L.obj.carrier ≅ structureModule X) :
    L ≅ trivial ε := by
  let F := Scheme.Modules.pullback ε
  let G := Scheme.Modules.pullback f
  let η : G ⋙ F ≅ 𝟭 S.Modules :=
    Scheme.Modules.pullbackComp ε f ≪≫
      Scheme.Modules.pullbackCongr section_eq ≪≫ Scheme.Modules.pullbackId S
  exact isoMk
    (RigidificationAdjustment.adjustIso F G η
      (Langlands.Scheme.Modules.pullbackUnitIso f) e
      L.obj.rigidification (trivial ε).obj.rigidification)
    (RigidificationAdjustment.adjustIso_compatible F G η
      (Langlands.Scheme.Modules.pullbackUnitIso f) e
      L.obj.rigidification (trivial ε).obj.rigidification)

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
