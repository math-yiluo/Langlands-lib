import Langlands.GroupScheme.Dynamic.SchemeDecomposition

/-! # The inverse coordinates of the represented dynamic multiplication isomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

open SubgroupFunctor.IsRepresentedBy

variable {S : Scheme.{u}} {G : GroupScheme S} {χ : (Gm S).toGrp ⟶ G} [IsSeparated G.X.hom]
  {P Z U : GroupScheme S} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)

/-- The limit of a product `u z` is its centralizer coordinate, as an equality of scheme maps. -/
theorem multiplication_comp_limitGroupHom :
    multiplication hP hZ hU ≫ (limitGroupHom hP hZ).hom.hom = snd U.X Z.X := by
  let := hZ.1
  apply (cancel_mono iZ.hom.hom).1
  rw [limitGroupHom_comp]
  have hp := pointsEquiv_comp_multiplication hP hZ hU (𝟙 (U.X ⊗ Z.X))
  simp only [Category.id_comp] at hp
  rw [hp]
  exact limit_mul χ _ _

/-- The centralizer coordinate of the inverse multiplication is the actual limit morphism. -/
theorem multiplicationIso_inv_snd :
    (multiplicationIso hP hZ hU).inv ≫ snd U.X Z.X =
      (limitGroupHom hP hZ).hom.hom := by
  rw [← multiplication_comp_limitGroupHom hP hZ hU]
  change (multiplicationIso hP hZ hU).inv ≫
    (multiplicationIso hP hZ hU).hom ≫ (limitGroupHom hP hZ).hom.hom = _
  simp

/-- The unipotent coordinate of the inverse multiplication is `p (lim p)⁻¹` in the ambient
group, as an equality of scheme maps. -/
theorem multiplicationIso_inv_fst_comp :
    ((multiplicationIso hP hZ hU).inv ≫ fst U.X Z.X) ≫ iU.hom.hom =
      iP.hom.hom * ((limitGroupHom hP hZ).hom.hom ≫ iZ.hom.hom)⁻¹ := by
  have hm := congrArg ((multiplicationIso hP hZ hU).inv ≫ ·)
    (multiplication_comp hP hZ hU)
  change (multiplicationIso hP hZ hU).inv ≫
      (multiplicationIso hP hZ hU).hom ≫ iP.hom.hom =
    (multiplicationIso hP hZ hU).inv ≫
      ((fst U.X Z.X ≫ iU.hom.hom) * (snd U.X Z.X ≫ iZ.hom.hom)) at hm
  rw [Iso.inv_hom_id_assoc, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
    multiplicationIso_inv_snd hP hZ hU] at hm
  exact eq_mul_inv_iff_mul_eq.2 hm.symm

end Langlands.GroupScheme.Dynamic
