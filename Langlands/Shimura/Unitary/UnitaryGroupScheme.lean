import Langlands.Shimura.Unitary.RationalGroupScheme
import Langlands.AbelianScheme.Kernel

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.AlgebraInvolution.SchemeModel

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ R A) (σ : AlgebraInvolution R A)

/-- The unitary group scheme is the actual fibre of the multiplier over the unit. -/
abbrev unitaryGroupScheme : GroupScheme (Spec (CommRingCat.of R)) :=
  GroupScheme.kernel (multiplier b σ)

/-- The unitary group scheme's canonical inclusion in the similitude group scheme. -/
def unitaryInclusion : unitaryGroupScheme b σ ⟶ groupScheme b σ :=
  GroupScheme.kernelι (multiplier b σ)

private def kernelComparison (T : Over (Spec (CommRingCat.of R))) :
    (((yonedaGrp.map (multiplier b σ)).app (op T)).hom.ker) ≃*
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).multiplier.ker where
  toFun x := ⟨pointsEquiv b σ T x.val, by
    have hx : x.val ≫ (multiplier b σ).hom.hom = 1 := x.property
    change multiplierPoints b σ T x.val = 1
    rw [← multiplier_points, hx, _root_.map_one]⟩
  invFun x := ⟨(pointsEquiv b σ T).symm x.val, by
    change (pointsEquiv b σ T).symm x.val ≫ (multiplier b σ).hom.hom = 1
    apply (GroupScheme.Gm.pointsEquiv _ T).injective
    rw [multiplier_points, _root_.map_one]
    change (σ.baseChange _).multiplier
      (pointsEquiv b σ T ((pointsEquiv b σ T).symm x.val)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((pointsEquiv b σ T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((pointsEquiv b σ T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (_root_.map_mul (pointsEquiv b σ T) x.val y.val)

/-- Unitary scheme points are precisely the existing scalar-extended unitary elements. -/
def unitaryPointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (unitaryGroupScheme b σ).X) ≃*
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).unitary :=
  (GroupScheme.kernelPointsEquiv (multiplier b σ) T).trans
    ((kernelComparison b σ T).trans
      (σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).unitaryEquivKernel.symm)

/-- The recovered unit is the algebra-unit coordinate of the included similitude point. -/
theorem unitaryPointsEquiv_val (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (unitaryGroupScheme b σ).X) :
    (unitaryPointsEquiv b σ T x).val =
      (pointsEquiv b σ T (x ≫ (unitaryInclusion b σ).hom.hom)).val.1 := rfl

/-- On points the scheme inclusion is the algebraic inclusion with multiplier one. -/
theorem unitaryInclusion_points (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (unitaryGroupScheme b σ).X) :
    (σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).unitaryInclusion
        (unitaryPointsEquiv b σ T x) =
      pointsEquiv b σ T (x ≫ (unitaryInclusion b σ).hom.hom) :=
  congrArg Subtype.val
    ((σ.baseChange ((algΓ (CommRingCat.of R)).obj T).unop).unitaryEquivKernel.apply_symm_apply
      (kernelComparison b σ T (GroupScheme.kernelPointsEquiv (multiplier b σ) T x)))

/-- Restriction of unitary points is the original coefficient map on algebra units. -/
theorem unitaryPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (a : T' ⟶ T) (x : T ⟶ (unitaryGroupScheme b σ).X) :
    (unitaryPointsEquiv b σ T' (a ≫ x)).val =
      Units.map
        (changeCoefficients (A := A) ((algΓ (CommRingCat.of R)).map a).unop.hom).toMonoidHom
        (unitaryPointsEquiv b σ T x).val := by
  rw [unitaryPointsEquiv_val, Category.assoc, pointsEquiv_naturality, unitaryPointsEquiv_val]
  rfl

/-- The unitary inclusion is a closed immersion of the underlying schemes. -/
instance unitaryInclusion_isClosedImmersion :
    IsClosedImmersion (unitaryInclusion b σ).hom.hom.left := by
  let : IsSeparated (GroupScheme.Gm (Spec (CommRingCat.of R))).X.hom := by
    let : IsSeparated GroupScheme.Gm.overSpecZ.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ _)
    infer_instance
  exact GroupScheme.kernelι_isClosedImmersion (multiplier b σ)

/-- The unitary group scheme is affine as a closed subscheme of the affine similitude scheme. -/
instance unitaryGroupScheme_isAffine : IsAffine (unitaryGroupScheme b σ).X.left :=
  isAffine_of_isAffineHom (unitaryInclusion b σ).hom.hom.left

end Langlands.Shimura.AlgebraInvolution.SchemeModel

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

/-- The rational unitary group of the actual CM algebra, as the kernel of its multiplier. -/
abbrev rationalUnitaryGroupScheme : GroupScheme (Spec (CommRingCat.of ℚ)) :=
  AlgebraInvolution.SchemeModel.unitaryGroupScheme D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution

/-- The rational unitary group includes into the rational similitude group. -/
def rationalUnitaryInclusion : D.rationalUnitaryGroupScheme ⟶ D.rationalGroupScheme :=
  AlgebraInvolution.SchemeModel.unitaryInclusion D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution

/-- Its points are the unitary elements over relative rational global sections. -/
def rationalUnitaryPointsEquiv (T : Over (Spec (CommRingCat.of ℚ))) :
    (T ⟶ D.rationalUnitaryGroupScheme.X) ≃*
      (D.toSecondKindInvolution.rationalInvolution.baseChange
        ((algΓ (CommRingCat.of ℚ)).obj T).unop).unitary :=
  AlgebraInvolution.SchemeModel.unitaryPointsEquiv D.rationalBasis
    D.toSecondKindInvolution.rationalInvolution T

end Langlands.Shimura.CentralSimpleUnitaryData
