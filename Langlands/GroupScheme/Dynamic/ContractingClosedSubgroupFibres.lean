import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Unipotent field fibres of closed contracting subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Dynamic

variable {R : Type u} [CommRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G) (j : H ⟶ G)
  (hj : IsClosedSubgroup j) (hle : SubgroupFunctor.range j ≤ unipotent χ)

include χ j hj hle

/-- A closed subgroup contracted by a cocharacter has unipotent fibres over every field
point of the base. No smoothness or connectedness assumption on the subgroup is required. -/
theorem isUnipotent_baseChange_of_range_le_unipotent
    (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    IsUnipotent ((GroupScheme.baseChange y).obj H) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let U := Affine.unipotentScheme χ
  let u : U ⟶ G := Affine.unipotentHom χ
  have hu : (unipotent χ).IsRepresentedBy u := Affine.isRepresentedBy_unipotentHom χ
  have huc : IsClosedSubgroup u := Affine.isClosedSubgroup_unipotentHom χ
  let f : H ⟶ U := hu.factorHom j hle
  have hf : f ≫ u = j := hu.factorHom_comp j hle
  have hfc : IsClosedSubgroup f := IsClosedSubgroup.of_comp huc (by rw [hf]; exact hj)
  have : Smooth U.X.hom := (dynamicSmooth_ring R G χ U u).2.2 hu
  have : IsAffineHom U.X.hom := huc.isAffineHom
  have hGk : Smooth ((GroupScheme.baseChange y).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom y)
    infer_instance
  have hGka : IsAffineHom ((GroupScheme.baseChange y).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom y)
    infer_instance
  have hUk : Smooth ((GroupScheme.baseChange y).obj U).X.hom := by
    change Smooth (pullback.snd U.X.hom y)
    infer_instance
  have hUka : IsAffineHom ((GroupScheme.baseChange y).obj U).X.hom := by
    change IsAffineHom (pullback.snd U.X.hom y)
    infer_instance
  have huk : (unipotent (baseChangeCocharacter y χ)).IsRepresentedBy
      ((GroupScheme.baseChange y).map u) := by
    rw [unipotent_baseChange]
    exact hu.baseChange y
  exact unipotentClosedSubgroup K _ _ ((GroupScheme.baseChange y).map f)
    (hfc.baseChange y)
    (dynamicUnipotentUnipotence K _ (baseChangeCocharacter y χ) _ _ huk)

/-- In particular, every geometric fibre of a closed contracting subgroup is unipotent. -/
theorem isUnipotent_geometricFiber_of_range_le_unipotent
    (s : Spec (CommRingCat.of R)) : IsUnipotent (geometricFiber H s) :=
  isUnipotent_baseChange_of_range_le_unipotent χ j hj hle _
    (geometricPoint (Spec (CommRingCat.of R)) s)

end Langlands.GroupScheme.Dynamic
