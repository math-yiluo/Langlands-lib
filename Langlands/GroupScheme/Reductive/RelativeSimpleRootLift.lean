import Langlands.GroupScheme.Reductive.RelativeExponentCharacterLift
import Langlands.GroupScheme.Reductive.AffinePinnedModel

/-! # Fppf simple-root values in supplied torus coordinates -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- The actual simple-root character on a torus with supplied model coordinates. -/
def simpleRootCharacter (T : GroupScheme M.base)
    (e : splitTorus M.base M.coordinates ≅ T) (a : M.basis.support) :
    T ⟶ (Gm M.base).toGrp :=
  splitTorus.exponentCharacterOnTorus M.base T e (M.rootDatum.root a)

/-- Canonical fppf local realization of arbitrary simple-root unit values. -/
def simpleRootUnitsLift (V : Over M.base)
    (c : M.basis.support → (Γ(V.left, ⊤))ˣ) :
    AutomorphicAction.FppfQuotientPointLift
      (splitTorus.exponentTorusProjection (CommRingCat.of M.ring)
        (fun a : M.basis.support => M.rootDatum.root a))
      ((splitTorus.pointsEquiv M.basis.support V).symm c) :=
  splitTorus.exponentUnitsLift (CommRingCat.of M.ring)
    (fun a : M.basis.support => M.rootDatum.root a)
    M.basis.linearIndepOn_root.linearIndependent V c

/-- The lifted coordinate point, expressed in the supplied torus, has all prescribed
simple-root values. -/
theorem simpleRootUnitsLift_character (T : GroupScheme M.base)
    (e : splitTorus M.base M.coordinates ≅ T) (V : Over M.base)
    (c : M.basis.support → (Γ(V.left, ⊤))ˣ) (a : M.basis.support) :
    let L := M.simpleRootUnitsLift V c
    Gm.pointsEquiv M.base L.cover
      ((L.lift ≫ e.hom.hom.hom) ≫ (M.simpleRootCharacter T e a).hom.hom) =
      splitTorus.unitsRestrict M.basis.support L.projection c a := by
  exact splitTorus.exponentUnitsLift_character (CommRingCat.of M.ring) T e
    (fun a : M.basis.support => M.rootDatum.root a)
    M.basis.linearIndepOn_root.linearIndependent V c a

/-- The prescribed simple-root values persist on every refinement of the lift. -/
theorem simpleRootUnitsLift_character_naturality (T : GroupScheme M.base)
    (e : splitTorus M.base M.coordinates ≅ T) (V : Over M.base)
    (c : M.basis.support → (Γ(V.left, ⊤))ˣ)
    (W : Over M.base) (b : W ⟶ (M.simpleRootUnitsLift V c).cover)
    (a : M.basis.support) :
    let L := M.simpleRootUnitsLift V c
    Gm.pointsEquiv M.base W
      ((b ≫ L.lift ≫ e.hom.hom.hom) ≫ (M.simpleRootCharacter T e a).hom.hom) =
      splitTorus.unitsRestrict M.basis.support (b ≫ L.projection) c a := by
  exact splitTorus.exponentUnitsLift_character_naturality (CommRingCat.of M.ring) T e
    (fun a : M.basis.support => M.rootDatum.root a)
    M.basis.linearIndepOn_root.linearIndependent V c W b a

/-- Any tuple of simple-root unit values is realized fppf-locally by a point of
the supplied coordinate torus. -/
theorem exists_fppf_simpleRoot_values (T : GroupScheme M.base)
    (e : splitTorus M.base M.coordinates ≅ T) (V : Over M.base)
    (c : M.basis.support → (Γ(V.left, ⊤))ˣ) :
    ∃ (W : Over M.base) (b : W ⟶ V) (t : W ⟶ T.X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (U : Over M.base) (d : U ⟶ W) (a : M.basis.support),
        Gm.pointsEquiv M.base U (d ≫ t ≫ (M.simpleRootCharacter T e a).hom.hom) =
          splitTorus.unitsRestrict M.basis.support (d ≫ b) c a := by
  exact splitTorus.exists_fppf_exponent_character_values (CommRingCat.of M.ring) T e
    (fun a : M.basis.support => M.rootDatum.root a)
    M.basis.linearIndepOn_root.linearIndependent V c

end Langlands.GroupScheme.AffinePinnedModel
