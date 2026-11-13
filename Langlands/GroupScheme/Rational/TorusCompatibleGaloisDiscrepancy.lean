import Langlands.GroupScheme.Rational.FiniteGaloisBaseChangeDiscrepancy
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.CharacterBaseChange

/-! # Galois discrepancies preserving an actual torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisDiscrepancy

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {D T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The automorphism comparing the Galois pullback of an isomorphism with itself. -/
def groupIso
    (E : (baseChange (algebraBaseMap k L)).obj G ≅
      (baseChange (algebraBaseMap k L)).obj H)
    (σ : L ≃ₐ[k] L) :
    (baseChange (algebraBaseMap k L)).obj G ≅
      (baseChange (algebraBaseMap k L)).obj G :=
  Descent.pullIso (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    (galoisBaseMap_over k L σ) E ≪≫ E.symm

/-- Canonical Galois transport of an actual isomorphism of the base-changed tori. -/
def pulledTorusIso
    (t : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (σ : L ≃ₐ[k] L) :
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T :=
  (CommGroupScheme.isoOfGroupIso
    (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) D.toGrp)).symm ≪≫
    (CommGroupScheme.baseChange (galoisBaseMap k L σ)).mapIso t ≪≫
    CommGroupScheme.isoOfGroupIso
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) T.toGrp)

/-- The forward torus map is exactly the canonical pullback of its underlying map. -/
theorem pulledTorusIso_hom
    (t : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (σ : L ≃ₐ[k] L) :
    CommGroupScheme.groupHom (pulledTorusIso t σ).hom =
      Descent.pullHom (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
        (galoisBaseMap_over k L σ) (CommGroupScheme.groupHom t.hom) := rfl

/-- The torus automorphism comparing the Galois pullback of its identification with itself. -/
def torusIso
    (t : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (σ : L ≃ₐ[k] L) :
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D :=
  pulledTorusIso t σ ≪≫ t.symm

/-- The actual inclusion square survives Galois pullback. -/
theorem pulled_square
    (i : D.toGrp ⟶ G) (j : T.toGrp ⟶ H)
    (E : (baseChange (algebraBaseMap k L)).obj G ≅
      (baseChange (algebraBaseMap k L)).obj H)
    (t : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (hsq : (baseChange (algebraBaseMap k L)).map i ≫ E.hom =
      CommGroupScheme.groupHom t.hom ≫ (baseChange (algebraBaseMap k L)).map j)
    (σ : L ≃ₐ[k] L) :
    (baseChange (algebraBaseMap k L)).map i ≫
        (Descent.pullIso (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
          (galoisBaseMap_over k L σ) E).hom =
      CommGroupScheme.groupHom (pulledTorusIso t σ).hom ≫
        (baseChange (algebraBaseMap k L)).map j := by
  rw [pulledTorusIso_hom, Descent.pullIso_hom]
  have h := congrArg (Descent.pullHom (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) (galoisBaseMap_over k L σ)) hsq
  rw [Descent.pullHom_comp, Descent.pullHom_comp,
    Descent.pullHom_map, Descent.pullHom_map] at h
  exact h

private theorem inverse_square {C : Type*} [Category C]
    {D' T' G' H' : C} (i : D' ⟶ G') (j : T' ⟶ H')
    (E : G' ≅ H') (t : D' ⟶ T') (s : T' ⟶ D')
    (ht : s ≫ t = 𝟙 T') (hsq : i ≫ E.hom = t ≫ j) :
    j ≫ E.inv = s ≫ i := by
  calc
    j ≫ E.inv = (s ≫ t) ≫ j ≫ E.inv := by rw [ht, Category.id_comp]
    _ = s ≫ (i ≫ E.hom) ≫ E.inv := by rw [hsq]; simp only [Category.assoc]
    _ = s ≫ i := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem comp_square {C : Type*} [Category C]
    {D' T' G' H' : C} (i : D' ⟶ G') (j : T' ⟶ H')
    (E F : G' ≅ H') (t : D' ⟶ T') (s : T' ⟶ D')
    (hsq : i ≫ F.hom = t ≫ j) (hi : j ≫ E.inv = s ≫ i) :
    i ≫ (F ≪≫ E.symm).hom = (t ≫ s) ≫ i := by
  change i ≫ F.hom ≫ E.inv = _
  rw [← Category.assoc, hsq, Category.assoc, hi, ← Category.assoc]

/-- The discrepancy automorphism preserves the actual source torus. -/
theorem square
    (i : D.toGrp ⟶ G) (j : T.toGrp ⟶ H)
    (E : (baseChange (algebraBaseMap k L)).obj G ≅
      (baseChange (algebraBaseMap k L)).obj H)
    (t : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (hsq : (baseChange (algebraBaseMap k L)).map i ≫ E.hom =
      CommGroupScheme.groupHom t.hom ≫ (baseChange (algebraBaseMap k L)).map j)
    (σ : L ≃ₐ[k] L) :
    (baseChange (algebraBaseMap k L)).map i ≫ (groupIso E σ).hom =
      CommGroupScheme.groupHom (torusIso t σ).hom ≫
        (baseChange (algebraBaseMap k L)).map i := by
  exact comp_square _ _ E _ _ _ (pulled_square i j E t hsq σ)
    (inverse_square _ _ E _ _
      (congrArg CommGroupScheme.groupHom t.inv_hom_id) hsq)

/-- Every character of a ground-field split torus is fixed by the Galois action. -/
theorem split_character_fixed (hD : IsSplitTorus D.toGrp) (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj D)) :
    characterLattice.galoisRepresentation k L D σ χ = χ := by
  obtain ⟨ψ, rfl⟩ :=
    (hD.characterLattice_baseChange_bijective (algebraBaseMap k L) D).surjective χ
  exact characterLattice.galoisRepresentation_baseChange k L D σ ψ

/-- Pullback by the torus discrepancy is conjugate to the inverse Galois action
on the target character lattice when the source torus is split over the ground field. -/
theorem torusIso_character
    (hD : IsSplitTorus D.toGrp)
    (t : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj D ≅
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj D)) :
    (torusIso t σ).hom ≫ χ =
      t.hom ≫ characterLattice.galoisRepresentation k L T σ⁻¹ (t.inv ≫ χ) := by
  have hσ (ψ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)) :
      characterLattice.galoisRepresentation k L T σ
        (characterLattice.galoisRepresentation k L T σ⁻¹ ψ) = ψ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  change (galoisHomTransport σ t.hom ≫ t.inv) ≫ χ = _
  rw [Category.assoc]
  calc
    _ = galoisHomTransport σ t.hom ≫
        characterLattice.galoisRepresentation k L T σ
          (characterLattice.galoisRepresentation k L T σ⁻¹ (t.inv ≫ χ)) :=
      congrArg (fun ψ => galoisHomTransport σ t.hom ≫ ψ) (hσ (t.inv ≫ χ)).symm
    _ = characterLattice.galoisRepresentation k L D σ
        (t.hom ≫ characterLattice.galoisRepresentation k L T σ⁻¹ (t.inv ≫ χ)) :=
      galoisHomTransport_comp σ t.hom _
    _ = _ := split_character_fixed hD σ _

end Langlands.GroupScheme.GaloisDiscrepancy
