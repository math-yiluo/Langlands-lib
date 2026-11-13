import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Finite presentation of the affine dynamic inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.DynamicBaseRepresentability

open Corepresented Langlands.CommutativeAlgebra.GradedFormallySmooth

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- A finitely generated cutting ideal gives a finitely presented closed inclusion. -/
theorem locallyOfFinitePresentation_cutHom
    {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {I : Ideal B}
    (hI : IsCutOutBy e H I) (hfg : I.FG) :
    LocallyOfFinitePresentation (cutHom hI).hom.hom.left := by
  rw [cutHom_left, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  refine RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_
  rw [CommRingCat.hom_ofHom, Ideal.mk_ker]
  exact hfg

variable [Algebra.FiniteType R B]
  (χ : (Gm (Spec R)).toGrp ⟶ Corepresented.groupScheme F e)

/-- The negative coefficients cut out a finitely presented parabolic inclusion. -/
theorem locallyOfFinitePresentation_coreParabolicHom :
    LocallyOfFinitePresentation (Corepresented.parabolicHom χ).hom.hom.left :=
  locallyOfFinitePresentation_cutHom _
    (negIdeal_fg (R := R) (Corepresented.coaction χ).hom
      (Corepresented.coaction_algebraMap χ))

/-- The off-diagonal coefficients cut out a finitely presented centralizer inclusion. -/
theorem locallyOfFinitePresentation_coreCentralizerHom :
    LocallyOfFinitePresentation (Corepresented.centralizerHom χ).hom.hom.left :=
  locallyOfFinitePresentation_cutHom _
    (offIdeal_fg (R := R) (Corepresented.coaction χ).hom
      (Corepresented.coaction_algebraMap χ))

/-- The negative and constant coefficients cut out a finitely presented unipotent inclusion. -/
theorem locallyOfFinitePresentation_coreUnipotentHom :
    LocallyOfFinitePresentation (Corepresented.unipotentHom χ).hom.hom.left :=
  locallyOfFinitePresentation_cutHom _
    (unipIdeal_fg (R := R) (Corepresented.coaction χ).hom
      ((algebraMap R B).comp (Corepresented.counit e).hom)
      (Corepresented.coaction_algebraMap χ)
      (fun r => by
        change algebraMap R B ((Corepresented.counit e).hom (algebraMap R B r)) = _
        rw [DynamicSmoothRing.counit_algebraMap]))

section Affine

variable {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (χ : (Gm (Spec R)).toGrp ⟶ G)

omit [LocallyOfFiniteType G.X.hom] in
/-- The affine coordinate identification is an isomorphism of underlying schemes. -/
theorem isIso_coordinates_hom :
    IsIso (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left :=
  (inferInstance : IsIso ((Over.forget _).mapIso
    ((Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G))).hom)

/-- The actual affine parabolic inclusion is finitely presented. -/
theorem locallyOfFinitePresentation_parabolicHom :
    LocallyOfFinitePresentation (Dynamic.Affine.parabolicHom χ).hom.hom.left := by
  have := locallyOfFinitePresentation_coreParabolicHom (Dynamic.Affine.cocharacter χ)
  have := isIso_coordinates_hom (G := G)
  change LocallyOfFinitePresentation
    ((Corepresented.parabolicHom (Dynamic.Affine.cocharacter χ)).hom.hom.left ≫
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left)
  infer_instance

/-- The actual affine centralizer inclusion is finitely presented. -/
theorem locallyOfFinitePresentation_centralizerHom :
    LocallyOfFinitePresentation (Dynamic.Affine.centralizerHom χ).hom.hom.left := by
  have := locallyOfFinitePresentation_coreCentralizerHom (Dynamic.Affine.cocharacter χ)
  have := isIso_coordinates_hom (G := G)
  change LocallyOfFinitePresentation
    ((Corepresented.centralizerHom (Dynamic.Affine.cocharacter χ)).hom.hom.left ≫
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left)
  infer_instance

/-- The actual affine unipotent inclusion is finitely presented. -/
theorem locallyOfFinitePresentation_unipotentHom :
    LocallyOfFinitePresentation (Dynamic.Affine.unipotentHom χ).hom.hom.left := by
  have := locallyOfFinitePresentation_coreUnipotentHom (Dynamic.Affine.cocharacter χ)
  have := isIso_coordinates_hom (G := G)
  change LocallyOfFinitePresentation
    ((Corepresented.unipotentHom (Dynamic.Affine.cocharacter χ)).hom.hom.left ≫
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom.left)
  infer_instance

end Affine

end Langlands.GroupScheme.DynamicBaseRepresentability
