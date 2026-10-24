import Langlands.Shimura.Unitary.SchemeScalarExtension
import Langlands.GroupScheme.CorepresentedAffineComparison

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.AlgebraInvolution.SchemeModel

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

attribute [local instance] sectionsSAlgebra sectionsScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of the affine test scheme recover its algebra, retaining the
structural action of the original base ring. -/
def restrictedAffineSectionsEquiv :
    restrictedSections R S ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T))) ≃ₐ[R] T := by
  let e :
      restrictedSections R S ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T))) ≃ₐ[S] T :=
    GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of S) (CommAlgCat.of S T)
  exact e.restrictScalars R

/-- The normalized section map is the usual spectrum section map on underlying rings. -/
theorem restrictedAffineSectionsEquiv_ringHom :
    (restrictedAffineSectionsEquiv (R := R) (S := S) T).toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom :=
  GroupScheme.Corepresented.affineSectionsIso_hom_ringHom (R := CommRingCat.of S) (CommAlgCat.of S T)

variable {A : Type u} [Ring A] [Algebra R A]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ R A) (σ : AlgebraInvolution R A)

/-- Points of the scalar pullback over an affine test scheme, with coefficients
normalized to its actual test algebra. -/
def baseChangedAffinePointsEquiv :
    ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) ≃*
      (σ.baseChange T).similitudes :=
  (baseChangedPointsEquiv b σ (scalarBaseMap R S)
    ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)))).trans
      ((σ.similitudeFunctor.mapIso (CommAlgCat.isoMk
        (restrictedAffineSectionsEquiv (R := R) (S := S) T))).groupIsoToMulEquiv)

/-- Normalization is coefficient change by the actual relative section isomorphism. -/
theorem baseChangedAffinePointsEquiv_apply
    (x : (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    baseChangedAffinePointsEquiv (S := S) T b σ x =
      σ.baseChangeMap (CommAlgCat.ofHom
        (restrictedAffineSectionsEquiv (R := R) (S := S) T).toAlgHom)
        (baseChangedPointsEquiv b σ (scalarBaseMap R S)
          ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T))) x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar-extension scheme isomorphism has the tensor-tower formula
on normalized affine points. -/
theorem scalarExtensionIso_affinePoints
    (x : (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    affinePointsEquiv (b.baseChange S) (σ.baseChange S) (CommAlgCat.of S T)
        (x ≫ (scalarExtensionIso S b σ).hom.hom.hom) =
      baseChangeTowerSimilitudes S T σ (baseChangedAffinePointsEquiv (S := S) T b σ x) := by
  let : Algebra R
      (restrictedSections R S ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)))) :=
    CommAlgCat.algebra _
  rw [baseChangedAffinePointsEquiv_apply]
  have h := GroupScheme.Corepresented.map_affineSectionsIso_pointsEquiv
    (R := CommRingCat.of S) (σ.baseChange S).similitudeFunctor
    ((σ.baseChange S).similitudeCorepresentableBy (b.baseChange S))
    (CommAlgCat.of S T) (x ≫ (scalarExtensionIso S b σ).hom.hom.hom)
  change (σ.baseChange S).baseChangeMap
    (GroupScheme.Corepresented.affineSectionsIso (R := CommRingCat.of S) (CommAlgCat.of S T)).hom
    (pointsEquiv (b.baseChange S) (σ.baseChange S) _ _) = _ at h
  change _ = affinePointsEquiv (b.baseChange S) (σ.baseChange S) _ _ at h
  rw [← h, scalarExtensionIso_points]
  exact (baseChangeTowerSimilitudes_naturality (R := R) (S := S)
    (T := restrictedSections R S ((algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T))))
    (U := T) σ
    (GroupScheme.Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of S) (CommAlgCat.of S T)).toAlgHom _).symm

end Langlands.Shimura.AlgebraInvolution.SchemeModel
