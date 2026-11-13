import Langlands.GroupScheme.IntegralModel.BaseChangePoints

/-! # Descent of the original integral-point image across a coefficient square -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open GaloisPointComparison

def affinePointLift
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (f : S →ₐ[R] T) (hf : Function.Injective f)
    (p : RingPoint R X T)
    (hp : ∀ a : AffineCoordinateRing R X,
      affineSchemePointEquiv R X T p a ∈ f.range) :
    RingPoint R X S :=
  (affineSchemePointEquiv R X S).symm
    (AlgPoint.ofAlgHom ((AlgEquiv.ofInjective f hf).symm.toAlgHom.comp
      ((affineSchemePointEquiv R X T p).toAlgHom.codRestrict f.range hp)))

theorem affinePointLift_changeRing
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (f : S →ₐ[R] T) (hf : Function.Injective f)
    (p : RingPoint R X T)
    (hp : ∀ a : AffineCoordinateRing R X,
      affineSchemePointEquiv R X T p a ∈ f.range) :
    (affinePointLift X f hf p hp).changeRing f = p := by
  apply (affineSchemePointEquiv R X T).injective
  rw [affineSchemePointEquiv_changeRing]
  apply AlgPoint.ext
  intro a
  change f ((affineSchemePointEquiv R X S
    ((affineSchemePointEquiv R X S).symm _)) a) = _
  rw [Equiv.apply_symm_apply]
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective f hf).apply_symm_apply
      ⟨affineSchemePointEquiv R X T p a, hp a⟩)

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

private instance modelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

theorem genericModelPointEquiv_integralPointMap (s : M.integralSections) :
    M.genericModelPointEquiv K
      (rationalCoeffEquiv K G (M.integralPointMap s)) =
      (rationalPointEquiv R M.group.X s).changeRing (Algebra.ofId R K) := by
  apply Over.OverMorphism.ext
  rw [genericModelPointEquiv_left, rationalCoeffEquiv_left]
  have hi : M.genericIso.hom.hom.hom.left ≫
      M.genericIso.inv.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left) M.genericIso.hom_inv_id
  change (((baseChangeSectionHom (Spec.algebraMap R K) M.group s).left ≫
    M.genericIso.hom.hom.hom.left) ≫ M.genericIso.inv.hom.hom.left) ≫
      pullback.fst M.group.X.hom (Spec.algebraMap R K) =
    Spec.algebraMap R K ≫ (rationalPointEquiv R M.group.X s).left
  rw [Category.assoc _ M.genericIso.hom.hom.hom.left, hi, Category.comp_id,
    baseChangeSectionHom_fst, rationalPointEquiv_left]

/-- Descend the actual generic point to an original integral section when all
original-model coordinates lie in the original integral coefficient ring. -/
def integralSectionOfCoordinates (g : rationalPoints G)
    (hg : ∀ a : AffineCoordinateRing R M.group.X,
      G.affinePointEvaluation (CommAlgCat.of K K)
        (rationalCoeffEquiv K G g) (M.genericCoordinate a) ∈
          Set.range (algebraMap R K)) :
    M.integralSections :=
  (rationalPointEquiv R M.group.X).symm
    (affinePointLift M.group.X (Algebra.ofId R K) (IsFractionRing.injective R K)
      (M.genericModelPointEquiv K (rationalCoeffEquiv K G g))
      (fun a => by
        rw [genericModelPointEquiv_evaluation]
        exact hg a))

theorem integralPointMap_integralSectionOfCoordinates (g : rationalPoints G)
    (hg : ∀ a : AffineCoordinateRing R M.group.X,
      G.affinePointEvaluation (CommAlgCat.of K K)
        (rationalCoeffEquiv K G g) (M.genericCoordinate a) ∈
          Set.range (algebraMap R K)) :
    M.integralPointMap (M.integralSectionOfCoordinates g hg) = g := by
  apply (rationalCoeffEquiv K G).injective
  apply (M.genericModelPointEquiv K).injective
  rw [genericModelPointEquiv_integralPointMap]
  change ((rationalPointEquiv R M.group.X)
    ((rationalPointEquiv R M.group.X).symm _)).changeRing _ = _
  rw [Equiv.apply_symm_apply]
  exact affinePointLift_changeRing _ _ _ _ _

/-- Test membership in the original image using the actual original-model
coordinates and the supplied generic identification. -/
theorem mem_integralPoints_iff_genericCoordinates (g : rationalPoints G) :
    g ∈ M.integralPoints ↔
      ∀ a : AffineCoordinateRing R M.group.X,
        G.affinePointEvaluation (CommAlgCat.of K K)
          (rationalCoeffEquiv K G g) (M.genericCoordinate a) ∈
            Set.range (algebraMap R K) := by
  constructor
  · rintro ⟨s, rfl⟩ a
    rw [← genericModelPointEquiv_evaluation, genericModelPointEquiv_integralPointMap,
      affineSchemePointEquiv_changeRing]
    exact ⟨affineSchemePointEquiv R M.group.X R
      (rationalPointEquiv R M.group.X s) a, rfl⟩
  · intro hg
    exact ⟨M.integralSectionOfCoordinates g hg,
      M.integralPointMap_integralSectionOfCoordinates g hg⟩

variable (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- The integral image after coefficient extension is tested by the original
model's actual generic coordinates, with values in the extended integral ring. -/
theorem mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates
    (p : G.affinePoints (CommAlgCat.of K L)) :
    p ∈ (M.baseChange A L).coefficientIntegralPoints K L ↔
      ∀ a : AffineCoordinateRing R M.group.X,
        G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a) ∈
          Set.range (algebraMap A L) := by
  rw [M.mem_baseChange_coefficientIntegralPoints_iff A L]
  constructor
  · rintro ⟨q, hq⟩ a
    rw [← genericModelPointEquiv_evaluation, ← hq, affineSchemePointEquiv_changeRing]
    exact ⟨affineSchemePointEquiv R M.group.X A q a, rfl⟩
  · intro hp
    have hcoords : ∀ a : AffineCoordinateRing R M.group.X,
        affineSchemePointEquiv R M.group.X L (M.genericModelPointEquiv L p) a ∈
          (IsScalarTower.toAlgHom R A L).range := by
      intro a
      rw [genericModelPointEquiv_evaluation]
      exact hp a
    exact ⟨affinePointLift M.group.X (IsScalarTower.toAlgHom R A L)
      (IsFractionRing.injective A L) (M.genericModelPointEquiv L p) hcoords,
      affinePointLift_changeRing _ _ _ _ _⟩

/-- Integral membership reflects under the actual rational extension whenever
the extended integral ring meets the original fraction field in its integral ring. -/
theorem mem_integralPoints_rationalExtend_iff
    (hintersection : ∀ x : K,
      algebraMap K L x ∈ Set.range (algebraMap A L) ↔
        x ∈ Set.range (algebraMap R K))
    (g : rationalPoints G) :
    rationalExtend K L G g ∈ (M.baseChange A L).integralPoints ↔
      g ∈ M.integralPoints := by
  have hcoeff := (M.baseChange A L).mem_coefficientIntegralPoints_iff K L
    (baseChangeCoeffEquiv K L G (rationalExtend K L G g))
  rw [MulEquiv.symm_apply_apply] at hcoeff
  rw [← hcoeff]
  rw [baseChangeCoeffEquiv_rationalExtend,
    M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates A L,
    M.mem_integralPoints_iff_genericCoordinates]
  exact forall_congr' (fun a => by
    change G.affinePointEvaluation (CommAlgCat.of K L)
      (G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId K L))
        (rationalCoeffEquiv K G g)) (M.genericCoordinate a) ∈
          Set.range (algebraMap A L) ↔ _
    rw [G.affinePointEvaluation_map]
    exact hintersection _)

/-- The original image is the inverse image of the base-changed integral subgroup
under the existing rational-point homomorphism. -/
theorem integralPoints_eq_comap_baseChange
    (hintersection : ∀ x : K,
      algebraMap K L x ∈ Set.range (algebraMap A L) ↔
        x ∈ Set.range (algebraMap R K)) :
    M.integralPoints =
      (M.baseChange A L).integralPoints.comap (rationalExtend K L G) := by
  ext g
  exact (M.mem_integralPoints_rationalExtend_iff A L hintersection g).symm

end Langlands.GroupScheme.IntegralModel
