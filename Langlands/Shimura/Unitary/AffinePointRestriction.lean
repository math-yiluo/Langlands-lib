import Langlands.Shimura.Unitary.AffineScalarExtension

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Shimura.AlgebraInvolution.SchemeModel

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The affine test scheme over S, viewed over R, is canonically Spec_R T. -/
def restrictedAffineTestIso :
    (Over.map (scalarBaseMap R S)).obj ((algSpec (CommRingCat.of S)).obj
      (op (CommAlgCat.of S T))) ≅
    (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R T)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S))
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq R S T))

@[simp] theorem restrictedAffineTestIso_hom_left :
    (restrictedAffineTestIso R S T).hom.left = 𝟙 (Spec (CommRingCat.of T)) := rfl

@[simp] theorem restrictedAffineTestIso_inv_left :
    (restrictedAffineTestIso R S T).inv.left = 𝟙 (Spec (CommRingCat.of T)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The section normalization agrees with restriction through the actual affine test isomorphism. -/
theorem restrictedAffineTestIso_sections :
    ((algΓ (CommRingCat.of R)).map (restrictedAffineTestIso R S T).inv).unop ≫
        (GroupScheme.Corepresented.affineSectionsIso (R := CommRingCat.of R)
          (CommAlgCat.of R T)).hom =
      CommAlgCat.ofHom (restrictedAffineSectionsEquiv (R := R) (S := S) T).toAlgHom := by
  apply CommAlgCat.hom_ext
  apply AlgHom.coe_ringHom_injective
  change (GroupScheme.Corepresented.affineSectionsIso (R := CommRingCat.of R)
    (CommAlgCat.of R T)).hom.hom.toRingHom.comp
      (restrictedAffineTestIso R S T).inv.left.appTop.hom =
    (restrictedAffineSectionsEquiv (R := R) (S := S) T).toRingHom
  rw [restrictedAffineSectionsEquiv_ringHom,
    GroupScheme.Corepresented.affineSectionsIso_hom_ringHom (R := CommRingCat.of R) (CommAlgCat.of R T),
    restrictedAffineTestIso_inv_left, Scheme.Hom.id_appTop]
  rfl

variable {R S T} {A : Type u} [Ring A] [Algebra R A]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ R A) (σ : AlgebraInvolution R A)

/-- Forget the new base of an affine pullback point and identify its affine test scheme. -/
def originalAffinePoint
    (x : (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R T)) ⟶ (groupScheme b σ).X :=
  (restrictedAffineTestIso R S T).inv ≫
    GroupScheme.baseChangePointsEquiv (scalarBaseMap R S) (groupScheme b σ) _ x

/-- On underlying schemes this operation is the first pullback projection. -/
theorem originalAffinePoint_left
    (x : (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    (originalAffinePoint b σ x).left =
      x.left ≫ Limits.pullback.fst (groupScheme b σ).X.hom (scalarBaseMap R S) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Normalized pullback coordinates are exactly the original affine coordinates. -/
theorem baseChangedAffinePointsEquiv_eq_originalAffinePoint
    (x : (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    baseChangedAffinePointsEquiv (S := S) T b σ x =
      affinePointsEquiv b σ (CommAlgCat.of R T) (originalAffinePoint b σ x) := by
  have h := GroupScheme.Corepresented.map_affineSectionsIso_pointsEquiv
    (R := CommRingCat.of R) σ.similitudeFunctor (σ.similitudeCorepresentableBy b)
    (CommAlgCat.of R T) (originalAffinePoint b σ x)
  change _ = affinePointsEquiv b σ _ _ at h
  rw [← h]
  change _ = σ.similitudeFunctor.map
    (GroupScheme.Corepresented.affineSectionsIso (R := CommRingCat.of R)
      (CommAlgCat.of R T)).hom
      (pointsEquiv b σ _ ((restrictedAffineTestIso R S T).inv ≫ _))
  rw [pointsEquiv_naturality]
  change _ = (σ.similitudeFunctor.map
      (((algΓ (CommRingCat.of R)).map (restrictedAffineTestIso R S T).inv).unop) ≫
    σ.similitudeFunctor.map
      (GroupScheme.Corepresented.affineSectionsIso (R := CommRingCat.of R)
        (CommAlgCat.of R T)).hom) _
  rw [← Functor.map_comp, restrictedAffineTestIso_sections]
  rfl

/-- Scalar extension has the tensor-tower formula in the original affine coordinates. -/
theorem scalarExtensionIso_originalAffinePoints
    (x : (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S T)) ⟶
      (baseChangedGroupScheme b σ (scalarBaseMap R S)).X) :
    affinePointsEquiv (b.baseChange S) (σ.baseChange S) (CommAlgCat.of S T)
        (x ≫ (scalarExtensionIso S b σ).hom.hom.hom) =
      baseChangeTowerSimilitudes S T σ
        (affinePointsEquiv b σ (CommAlgCat.of R T) (originalAffinePoint b σ x)) := by
  rw [scalarExtensionIso_affinePoints, baseChangedAffinePointsEquiv_eq_originalAffinePoint]

end Langlands.Shimura.AlgebraInvolution.SchemeModel
