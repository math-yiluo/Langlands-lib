import Langlands.GroupScheme.Dynamic.Representability
import Langlands.GroupScheme.Dynamic.SchemeCoordinates

/-! # Limit, kernel and multiplication for the constructed affine dynamic subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

local instance : IsAffine (groupScheme F e).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))

local instance : IsAffineHom (groupScheme F e).X.hom :=
  isAffineHom_of_isAffine _

variable (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- Limit at zero on the constructed affine dynamic subgroup schemes. -/
def limitGroupHom : parabolicScheme χ ⟶ centralizerScheme χ :=
  Dynamic.limitGroupHom (isRepresentedBy_parabolicHom χ) (isRepresentedBy_centralizerHom χ)

/-- The inclusion of the constructed centralizer into the constructed parabolic. -/
def centralizerToParabolic : centralizerScheme χ ⟶ parabolicScheme χ :=
  Dynamic.centralizerToParabolic
    (isRepresentedBy_parabolicHom χ) (isRepresentedBy_centralizerHom χ)

theorem centralizerToParabolic_comp :
    centralizerToParabolic χ ≫ parabolicHom χ = centralizerHom χ :=
  Dynamic.centralizerToParabolic_comp _ _

theorem centralizerToParabolic_comp_limitGroupHom :
    centralizerToParabolic χ ≫ limitGroupHom χ = 𝟙 (centralizerScheme χ) :=
  Dynamic.centralizerToParabolic_comp_limitGroupHom _ _

/-- The affine limit homomorphism is the limit of the actual conjugation orbit on every test. -/
theorem limitGroupHom_comp {T : Over (Spec R)} (p : T ⟶ (parabolicScheme χ).X) :
    (p ≫ (limitGroupHom χ).hom.hom) ≫ (centralizerHom χ).hom.hom =
      Dynamic.limit χ ((isRepresentedBy_parabolicHom χ).pointsEquiv T p) :=
  Dynamic.limitGroupHom_comp _ _ p

/-- The constructed affine unipotent subgroup is the scheme-theoretic kernel of the limit. -/
def unipotentIsoKernel : unipotentScheme χ ≅ kernel (limitGroupHom χ) :=
  Dynamic.unipotentIsoKernel
    (hP := isRepresentedBy_parabolicHom χ) (hZ := isRepresentedBy_centralizerHom χ)
    (isRepresentedBy_unipotentHom χ)

theorem unipotentIsoKernel_hom_comp :
    (unipotentIsoKernel χ).hom ≫ kernelι (limitGroupHom χ) ≫ parabolicHom χ =
      unipotentHom χ :=
  Dynamic.unipotentIsoKernel_hom_comp _

/-- Multiplication is an isomorphism on the explicit affine quotient schemes. -/
def multiplicationIso :
    (unipotentScheme χ).X ⊗ (centralizerScheme χ).X ≅ (parabolicScheme χ).X :=
  Dynamic.multiplicationIso (isRepresentedBy_parabolicHom χ)
    (isRepresentedBy_centralizerHom χ) (isRepresentedBy_unipotentHom χ)

theorem multiplicationIso_hom_comp :
    (multiplicationIso χ).hom ≫ (parabolicHom χ).hom.hom =
      (fst (unipotentScheme χ).X (centralizerScheme χ).X ≫ (unipotentHom χ).hom.hom) *
        (snd (unipotentScheme χ).X (centralizerScheme χ).X ≫ (centralizerHom χ).hom.hom) :=
  Dynamic.multiplication_comp (isRepresentedBy_parabolicHom χ)
    (isRepresentedBy_centralizerHom χ) (isRepresentedBy_unipotentHom χ)

/-- The map on pairs of arbitrary test points is multiplication in the ambient group. -/
theorem lift_comp_multiplicationIso_hom_comp {T : Over (Spec R)}
    (u : T ⟶ (unipotentScheme χ).X) (z : T ⟶ (centralizerScheme χ).X) :
    (lift u z ≫ (multiplicationIso χ).hom) ≫ (parabolicHom χ).hom.hom =
      (u ≫ (unipotentHom χ).hom.hom) * (z ≫ (centralizerHom χ).hom.hom) := by
  rw [Category.assoc, multiplicationIso_hom_comp, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc]

theorem multiplicationIso_inv_snd :
    (multiplicationIso χ).inv ≫ snd (unipotentScheme χ).X (centralizerScheme χ).X =
      (limitGroupHom χ).hom.hom :=
  Dynamic.multiplicationIso_inv_snd (isRepresentedBy_parabolicHom χ)
    (isRepresentedBy_centralizerHom χ) (isRepresentedBy_unipotentHom χ)

theorem multiplicationIso_inv_fst_comp :
    ((multiplicationIso χ).inv ≫ fst (unipotentScheme χ).X (centralizerScheme χ).X) ≫
        (unipotentHom χ).hom.hom =
      (parabolicHom χ).hom.hom *
        ((limitGroupHom χ).hom.hom ≫ (centralizerHom χ).hom.hom)⁻¹ :=
  Dynamic.multiplicationIso_inv_fst_comp (isRepresentedBy_parabolicHom χ)
    (isRepresentedBy_centralizerHom χ) (isRepresentedBy_unipotentHom χ)

end Langlands.GroupScheme.Corepresented
