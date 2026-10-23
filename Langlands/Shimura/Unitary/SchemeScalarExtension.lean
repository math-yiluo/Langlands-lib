import Langlands.Shimura.Unitary.GroupSchemeBaseChange
import Langlands.Shimura.Unitary.InvolutionBaseChangeTower
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.AlgebraInvolution.SchemeModel

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The affine base morphism induced by extension of coefficients. -/
abbrev scalarBaseMap : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- Global sections with the structural action of the original coefficient ring. -/
abbrev restrictedSections (T : Over (Spec (CommRingCat.of S))) : CommAlgCat R :=
  ((algΓ (CommRingCat.of R)).obj ((Over.map (scalarBaseMap R S)).obj T)).unop

local instance sectionsSAlgebra (T : Over (Spec (CommRingCat.of S))) :
    Algebra S (restrictedSections R S T) :=
  inferInstanceAs (Algebra S ((algΓ (CommRingCat.of S)).obj T).unop)

local instance sectionsScalarTower (T : Over (Spec (CommRingCat.of S))) :
    IsScalarTower R S (restrictedSections R S T) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change (T.hom ≫ scalarBaseMap R S).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) =
    T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv (algebraMap R S r))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap R S))) r).symm

variable {R} {A : Type u} [Ring A] [Algebra R A]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ R A) (σ : AlgebraInvolution R A)

/-- All-scheme points compare the pullback with the model formed after scalar extension. -/
def scalarExtensionPointsEquiv (T : Over (Spec (CommRingCat.of S))) :
    (T ⟶ (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) ≃*
      (T ⟶ (groupScheme (b.baseChange S) (σ.baseChange S)).X) :=
  (baseChangedPointsEquiv b σ (scalarBaseMap R S) T).trans
    ((baseChangeTowerSimilitudes S (restrictedSections R S T) σ).trans
      (pointsEquiv (b.baseChange S) (σ.baseChange S) T).symm)

/-- The comparison has exactly the tensor-tower formula on algebraic points. -/
theorem scalarExtensionPointsEquiv_apply (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    pointsEquiv (b.baseChange S) (σ.baseChange S) T
        (scalarExtensionPointsEquiv S b σ T x) =
      baseChangeTowerSimilitudes S (restrictedSections R S T) σ
        (baseChangedPointsEquiv b σ (scalarBaseMap R S) T x) :=
  (pointsEquiv (b.baseChange S) (σ.baseChange S) T).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The point comparison commutes with restriction along every test-scheme morphism. -/
theorem scalarExtensionPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of S))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    scalarExtensionPointsEquiv S b σ T' (a ≫ x) =
      a ≫ scalarExtensionPointsEquiv S b σ T x := by
  apply (pointsEquiv (b.baseChange S) (σ.baseChange S) T').injective
  rw [scalarExtensionPointsEquiv_apply, pointsEquiv_naturality,
    scalarExtensionPointsEquiv_apply, baseChangedPointsEquiv_naturality]
  exact baseChangeTowerSimilitudes_naturality (R := R) (S := S)
    (T := restrictedSections R S T) (U := restrictedSections R S T') σ
    (((algΓ (CommRingCat.of S)).map a).unop.hom) _

/-- The scheme pullback is the actual similitude model of the scalar-extended involution. -/
def scalarExtensionIso :
    baseChangedGroupScheme b σ (scalarBaseMap R S) ≅
      groupScheme (b.baseChange S) (σ.baseChange S) :=
  GroupScheme.isoOfPoints (scalarExtensionPointsEquiv S b σ)
    (scalarExtensionPointsEquiv_naturality S b σ)

/-- The constructed scheme isomorphism induces the tensor-tower comparison. -/
theorem scalarExtensionIso_points (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    pointsEquiv (b.baseChange S) (σ.baseChange S) T
        (x ≫ (scalarExtensionIso S b σ).hom.hom.hom) =
      baseChangeTowerSimilitudes S (restrictedSections R S T) σ
        (baseChangedPointsEquiv b σ (scalarBaseMap R S) T x) := by
  rw [scalarExtensionIso, GroupScheme.comp_isoOfPoints_hom]
  exact scalarExtensionPointsEquiv_apply S b σ T x

/-- The model isomorphism commutes with the multiplier morphisms to the same `Gm`. -/
theorem scalarExtensionIso_multiplier :
    (scalarExtensionIso S b σ).hom ≫ multiplier (b.baseChange S) (σ.baseChange S) =
      baseChangedMultiplier b σ (scalarBaseMap R S) := by
  apply GroupScheme.hom_ext_points
  intro T x
  apply (GroupScheme.Gm.pointsEquiv _ T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, multiplier_points]
  change ((σ.baseChange S).baseChange _).multiplier
    (pointsEquiv (b.baseChange S) (σ.baseChange S) T
      (x ≫ (scalarExtensionIso S b σ).hom.hom.hom)) = _
  rw [scalarExtensionIso_points, baseChangedMultiplier_points]
  exact Units.ext rfl

/-- All-scheme unitary points compare the pullback and the extended coefficient model. -/
def scalarExtensionUnitaryPointsEquiv (T : Over (Spec (CommRingCat.of S))) :
    (T ⟶ (baseChangedUnitaryGroupScheme b σ (scalarBaseMap R S)).X) ≃*
      (T ⟶ (unitaryGroupScheme (b.baseChange S) (σ.baseChange S)).X) :=
  (baseChangedUnitaryPointsEquiv b σ (scalarBaseMap R S) T).trans
    ((baseChangeTowerUnitary S (restrictedSections R S T) σ).trans
      (unitaryPointsEquiv (b.baseChange S) (σ.baseChange S) T).symm)

theorem scalarExtensionUnitaryPointsEquiv_apply (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ (baseChangedUnitaryGroupScheme b σ (scalarBaseMap R S)).X) :
    unitaryPointsEquiv (b.baseChange S) (σ.baseChange S) T
        (scalarExtensionUnitaryPointsEquiv S b σ T x) =
      baseChangeTowerUnitary S (restrictedSections R S T) σ
        (baseChangedUnitaryPointsEquiv b σ (scalarBaseMap R S) T x) :=
  (unitaryPointsEquiv (b.baseChange S) (σ.baseChange S) T).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of unitary points commutes with the model comparison. -/
theorem scalarExtensionUnitaryPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of S))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangedUnitaryGroupScheme b σ (scalarBaseMap R S)).X) :
    scalarExtensionUnitaryPointsEquiv S b σ T' (a ≫ x) =
      a ≫ scalarExtensionUnitaryPointsEquiv S b σ T x := by
  apply (unitaryPointsEquiv (b.baseChange S) (σ.baseChange S) T').injective
  rw [scalarExtensionUnitaryPointsEquiv_apply]
  apply Subtype.ext
  rw [unitaryPointsEquiv_naturality, scalarExtensionUnitaryPointsEquiv_apply]
  apply Units.ext
  change baseChangeTowerEquiv R S (restrictedSections R S T') A
      ((baseChangedUnitaryPointsEquiv b σ (scalarBaseMap R S) T' (a ≫ x)).val :
        (restrictedSections R S T') ⊗[R] A) = _
  rw [baseChangedUnitaryPointsEquiv_naturality]
  exact baseChangeTowerEquiv_naturality
    (R := R) (S := S) (T := restrictedSections R S T) (U := restrictedSections R S T')
    (((algΓ (CommRingCat.of S)).map a).unop.hom) _

/-- The actual unitary scheme pullback agrees with the extended coefficient model. -/
def scalarExtensionUnitaryIso :
    baseChangedUnitaryGroupScheme b σ (scalarBaseMap R S) ≅
      unitaryGroupScheme (b.baseChange S) (σ.baseChange S) :=
  GroupScheme.isoOfPoints (scalarExtensionUnitaryPointsEquiv S b σ)
    (scalarExtensionUnitaryPointsEquiv_naturality S b σ)

theorem scalarExtensionUnitaryIso_points (T : Over (Spec (CommRingCat.of S)))
    (x : T ⟶ (baseChangedUnitaryGroupScheme b σ (scalarBaseMap R S)).X) :
    unitaryPointsEquiv (b.baseChange S) (σ.baseChange S) T
        (x ≫ (scalarExtensionUnitaryIso S b σ).hom.hom.hom) =
      baseChangeTowerUnitary S (restrictedSections R S T) σ
        (baseChangedUnitaryPointsEquiv b σ (scalarBaseMap R S) T x) := by
  rw [scalarExtensionUnitaryIso, GroupScheme.comp_isoOfPoints_hom]
  exact scalarExtensionUnitaryPointsEquiv_apply S b σ T x

set_option backward.isDefEq.respectTransparency false in
/-- Both isomorphisms respect the actual unitary inclusion in the similitude group. -/
theorem scalarExtensionIso_unitaryInclusion :
    (scalarExtensionUnitaryIso S b σ).hom ≫
        unitaryInclusion (b.baseChange S) (σ.baseChange S) =
      baseChangedUnitaryInclusion b σ (scalarBaseMap R S) ≫
        (scalarExtensionIso S b σ).hom := by
  apply GroupScheme.hom_ext_points
  intro T x
  apply (pointsEquiv (b.baseChange S) (σ.baseChange S) T).injective
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc,
    ← unitaryInclusion_points, scalarExtensionUnitaryIso_points,
    ← Category.assoc, scalarExtensionIso_points, ← baseChangedUnitaryInclusion_points]
  exact baseChangeTowerUnitary_inclusion S (restrictedSections R S T) σ _

end Langlands.Shimura.AlgebraInvolution.SchemeModel
