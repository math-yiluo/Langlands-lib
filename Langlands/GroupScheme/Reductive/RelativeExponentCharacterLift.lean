import Langlands.GroupScheme.Reductive.RelativeRootScalingLift
import Langlands.GroupScheme.Torus.ExponentCharacters

/-! # Fppf values of actual characters in supplied torus coordinates -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

variable (S : Scheme.{u}) {I : Type u} [Fintype I]

/-- The actual character transported from a fixed exponent vector through supplied
coordinates on a torus. -/
def exponentCharacterOnTorus (T : GroupScheme S) (e : splitTorus S I ≅ T)
    (m : I → ℤ) : T ⟶ (Gm S).toGrp :=
  e.inv ≫ CommGroupScheme.groupHom (exponentCharacter S I m)

/-- Transporting a coordinate point and evaluating the transported actual character
gives its exponent monomial. -/
theorem pointsEquiv_exponentCharacterOnTorus (T : GroupScheme S)
    (e : splitTorus S I ≅ T) (m : I → ℤ) (V : Over S)
    (x : V ⟶ (splitTorus S I).X) :
    Gm.pointsEquiv S V
      ((x ≫ e.hom.hom.hom) ≫ (exponentCharacterOnTorus S T e m).hom.hom) =
      ∏ i, pointsEquiv I V x i ^ m i := by
  unfold exponentCharacterOnTorus
  rw [Grp.comp_hom_hom, Category.assoc, ← Category.assoc e.hom.hom.hom,
    ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.id_comp]
  exact pointsEquiv_exponentCharacter S I m x

variable (R : CommRingCat.{u}) {J : Type u} [Fintype J]

/-- The canonical monomial lift realizes the prescribed values under actual
characters on a torus with supplied coordinates. -/
theorem exponentUnitsLift_character (T : GroupScheme (Spec R))
    (e : splitTorus (Spec R) I ≅ T)
    (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ) (j : J) :
    let L := exponentUnitsLift R m hm V c
    Gm.pointsEquiv (Spec R) L.cover
      ((L.lift ≫ e.hom.hom.hom) ≫
        (exponentCharacterOnTorus (Spec R) T e (m j)).hom.hom) =
      unitsRestrict J L.projection c j := by
  dsimp only
  let L := exponentUnitsLift R m hm V c
  exact (pointsEquiv_exponentCharacterOnTorus (Spec R) T e (m j) L.cover L.lift).trans
    (exponentUnitsLift_equation R m hm V c j)

/-- Prescribed actual-character values persist on every refinement of the lift. -/
theorem exponentUnitsLift_character_naturality (T : GroupScheme (Spec R))
    (e : splitTorus (Spec R) I ≅ T)
    (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ)
    (W : Over (Spec R)) (b : W ⟶ (exponentUnitsLift R m hm V c).cover) (j : J) :
    let L := exponentUnitsLift R m hm V c
    Gm.pointsEquiv (Spec R) W
      ((b ≫ L.lift ≫ e.hom.hom.hom) ≫
        (exponentCharacterOnTorus (Spec R) T e (m j)).hom.hom) =
      unitsRestrict J (b ≫ L.projection) c j := by
  dsimp only
  let L := exponentUnitsLift R m hm V c
  calc
    _ = Units.map b.left.appTop.hom.toMonoidHom
        (Gm.pointsEquiv (Spec R) L.cover
          ((L.lift ≫ e.hom.hom.hom) ≫
            (exponentCharacterOnTorus (Spec R) T e (m j)).hom.hom)) := by
      simpa only [Category.assoc] using Gm.pointsEquiv_naturality (Spec R) b
        ((L.lift ≫ e.hom.hom.hom) ≫
          (exponentCharacterOnTorus (Spec R) T e (m j)).hom.hom)
    _ = Units.map b.left.appTop.hom.toMonoidHom
        (unitsRestrict J L.projection c j) :=
      congrArg (Units.map b.left.appTop.hom.toMonoidHom)
        (exponentUnitsLift_character R T e m hm V c j)
    _ = unitsRestrict J (b ≫ L.projection) c j := by
      change Units.map b.left.appTop.hom.toMonoidHom
          (Units.map L.projection.left.appTop.hom.toMonoidHom (c j)) =
        Units.map (b ≫ L.projection).left.appTop.hom.toMonoidHom (c j)
      apply Units.ext
      change b.left.appTop (L.projection.left.appTop (c j).val) =
        (b ≫ L.projection).left.appTop (c j).val
      simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl

/-- Independent exponent characters on a supplied coordinate torus attain arbitrary
unit values fppf-locally, with the equations retained on all refinements. -/
theorem exists_fppf_exponent_character_values (T : GroupScheme (Spec R))
    (e : splitTorus (Spec R) I ≅ T)
    (m : J → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec R)) (c : J → (Γ(V.left, ⊤))ˣ) :
    ∃ (W : Over (Spec R)) (b : W ⟶ V) (t : W ⟶ T.X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (U : Over (Spec R)) (d : U ⟶ W) (j : J),
        Gm.pointsEquiv (Spec R) U
          (d ≫ t ≫ (exponentCharacterOnTorus (Spec R) T e (m j)).hom.hom) =
          unitsRestrict J (d ≫ b) c j := by
  let L := exponentUnitsLift R m hm V c
  refine ⟨L.cover, L.projection, L.lift ≫ e.hom.hom.hom,
    L.flat, L.surjective, L.locallyOfFinitePresentation, ?_⟩
  intro U d j
  simpa only [Category.assoc] using
    exponentUnitsLift_character_naturality R T e m hm V c U d j

end Langlands.GroupScheme.splitTorus
