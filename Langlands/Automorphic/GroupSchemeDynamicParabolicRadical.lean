import Langlands.Automorphic.GroupSchemeParabolicRadicals
import Langlands.GroupScheme.Rational.ParabolicFunctorCocharacter
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Rational.GeometricUnipotentRadicalComparison
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof

/-! # Canonical parabolic radical images in dynamic coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The actual dynamic parabolic, with geometric parabolicity supplied by the
explicit parabolic-dynamic structural premise. -/
def dynamicParabolicFunctor : ParabolicFunctor G :=
  ⟨Dynamic.parabolic χ, isParabolicFunctor_dynamic_of_parabolicDynamic hPD hG χ⟩

include hPD hG

/-- The identity-limit functor is the ambient image of a greatest ground-field
unipotent radical of the actual dynamic parabolic. -/
theorem isRationalParabolicRadical_dynamic :
    IsRationalParabolicRadical (Dynamic.parabolic χ) (Dynamic.unipotent χ) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let p := Dynamic.Affine.parabolicHom χ
  let j := Dynamic.Affine.unipotentHom χ
  let hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let φ := fun T => Subgroup.inclusion (Dynamic.unipotent_le_parabolic χ T)
  let r := hu.lift hp φ (fun _ _ => rfl)
  have hr : r ≫ p = j :=
    hu.lift_comp_eq hp φ (fun _ _ => rfl) (fun _ _ => rfl)
  have hur : (Dynamic.unipotent χ).IsRepresentedBy (r ≫ p) := by
    rw [hr]
    exact hu
  have hgeom := dynamicGeometricUnipotentRadical_of_centralizer
    dynamicCentralizerReductive F G hG χ _ _ p r hp hur
  let : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  have hrad := hgeom.isUnipotentRadical_of_unipotentFieldExtension
    unipotentFieldExtensionStatement
  exact ⟨_, _, p, r,
    Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic hPD hG χ,
    hp.2, hrad, hur.2⟩

/-- The chosen all-test radical image agrees with the actual identity-limit
subgroup, independently of the chosen radical presentation. -/
theorem rationalParabolicRadical_dynamic :
    rationalParabolicRadical hPD hG (dynamicParabolicFunctor hPD hG χ) =
      Dynamic.unipotent χ :=
  (rationalParabolicRadical_spec hPD hG (dynamicParabolicFunctor hPD hG χ)).unique
    (isRationalParabolicRadical_dynamic hPD hG χ)

/-- The same identity applies to any rational parabolic identified with the
dynamic parabolic on every test scheme. -/
theorem rationalParabolicRadical_eq_dynamic (P : ParabolicFunctor G)
    (hP : P.val = Dynamic.parabolic χ) :
    rationalParabolicRadical hPD hG P = Dynamic.unipotent χ := by
  apply (rationalParabolicRadical_spec hPD hG P).unique
  rw [hP]
  exact isRationalParabolicRadical_dynamic hPD hG χ

end Langlands.Automorphic.GroupSchemeFunctions
