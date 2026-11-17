import Langlands.GroupScheme.Torus.GrouplikeMonomialLocus
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof

/-! # Idempotent restriction loci of actual diagonalizable homomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

open DiagonalizableCharacter CharacterAction

variable {R : CommRingCat.{u}} {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]
    (f : (groupScheme R Γ).toGrp ⟶ (groupScheme R Λ).toGrp)

/-- The universal character-coordinate family of an actual group homomorphism. -/
def homCharacterFamily :
    Multiplicative Λ →* (CharacterAction.algebra (M := Γ) (baseAlg R))ˣ :=
  (Units.map (sectionsIso R Γ).hom.hom.toRingHom.toMonoidHom).comp
    (characterPointsEquiv R Λ (groupScheme R Γ).X f.hom.hom)

theorem homCharacterFamily_val (m : Multiplicative Λ) :
    (homCharacterFamily f m : AddMonoidAlgebra R Γ) =
      (NaturalUnits.ofHom f m.toAdd).value := by
  simp only [homCharacterFamily, NaturalUnits.value, NaturalUnits.ofHom,
    MonoidHom.comp_apply, Units.coe_map]
  rfl

theorem homCharacterFamily_isGrouplike (m : Multiplicative Λ) :
    IsGrouplike (M := Γ)
      (homCharacterFamily f m : AddMonoidAlgebra R Γ) := by
  rw [homCharacterFamily_val]
  exact (NaturalUnits.ofHom f m.toAdd).isGrouplike_value

/-- Monomial specialization of the universal family controls the homomorphism
on the entire point group of the corresponding test scheme. -/
theorem points_eq_of_monomial_specialization (p : Λ →+ Γ)
    (U : Over (Spec R))
    (a : baseAlg R ⟶ ((algΓ R).obj U).unop)
    (ha : mapCharacter (coefficientMap (M := Γ) a) (homCharacterFamily f) =
      (universal (M := Γ) ((algΓ R).obj U).unop).comp
        (AddMonoidHom.toMultiplicative p))
    (x : U ⟶ (groupScheme R Γ).X) :
    x ≫ f.hom.hom = x ≫ (restrictMap R p).hom.hom := by
  apply (characterPointsEquiv R Λ U).injective
  apply MonoidHom.ext
  intro m
  let C := ((algΓ R).obj U).unop
  let χ := characterPointsEquiv R Γ U x
  let c := NaturalUnits.ofHom f m.toAdd
  have hc : (coefficientMap (M := Γ) a).hom
      (homCharacterFamily f m : AddMonoidAlgebra R Γ) =
      AddMonoidAlgebra.single (p m.toAdd) 1 :=
    congrArg (fun t : Multiplicative Λ →* (CharacterAction.algebra (M := Γ) C)ˣ =>
      ((t m : (CharacterAction.algebra (M := Γ) C)ˣ) : AddMonoidAlgebra C Γ)) ha
  rw [homCharacterFamily_val] at hc
  have heval := congrArg (evaluate (𝟙 C) χ).hom hc
  change (coefficientMap a ≫ evaluate (𝟙 C) χ).hom c.value =
    (evaluate (𝟙 C) χ).hom (AddMonoidAlgebra.single (p m.toAdd) 1) at heval
  rw [coefficientMap_evaluate, Category.comp_id, evaluate_eq_lift,
    evaluate_single, map_one, one_mul] at heval
  calc
    characterPointsEquiv R Λ U (x ≫ f.hom.hom) m = c.app U x := rfl
    _ = χ (.ofAdd (p m.toAdd)) := by
      apply Units.ext
      rw [c.app_eq]
      exact heval
    _ = characterPointsEquiv R Λ U
        (x ≫ (restrictMap R p).hom.hom) m :=
      (pointsEquiv_restrictMap R p x m.toAdd).symm

/-- Every domain specialization supplies a character map describing the
actual homomorphism on every test where one idempotent becomes one. -/
theorem exists_idempotent_restriction_locus [AddGroup.FG Λ]
    {C : CommAlgCat.{u} R} [IsDomain C] (a : baseAlg R ⟶ C) :
    ∃ (p : Λ →+ Γ) (e : R), IsIdempotentElem e ∧ a.hom e = 1 ∧
      ∀ (U : Over (Spec R)) (x : U ⟶ (groupScheme R Γ).X),
        algebraMap R (((algΓ R).obj U).unop) e = 1 →
          x ≫ f.hom.hom = x ≫ (restrictMap R p).hom.hom := by
  obtain ⟨p, e, he, hea, hloc⟩ :=
    exists_idempotent_monomial_presentation (homCharacterFamily_isGrouplike f) a
  refine ⟨p, e, he, hea, fun U x hx => ?_⟩
  let b : baseAlg R ⟶ ((algΓ R).obj U).unop :=
    CommAlgCat.ofHom (Algebra.ofId R _)
  apply points_eq_of_monomial_specialization f p U b
  exact (hloc _ b).2 hx

end Langlands.GroupScheme.Diagonalizable
