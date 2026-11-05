import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.GaloisPointDescent
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeGeneration
import Langlands.AlgebraicGeometry.PointTopology.IntegralPointCriterion

/-! # Actual generic coordinates of an integral group model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

private instance modelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

private instance genericAffine : IsAffine M.genericFibre.X.left := by
  change IsAffine (pullback M.group.X.hom (Spec.algebraMap R K))
  infer_instance

/-- Restrict an integral-model regular function to the specified generic group. -/
def genericCoordinate :
    AffineCoordinateRing R M.group.X →+* AffineCoordinateRing K G.X :=
  M.genericIso.inv.hom.hom.left.appTop.hom.comp
    (pullback.fst M.group.X.hom (Spec.algebraMap R K)).appTop.hom

variable [IsAffine G.X.left]

/-- Integral-model coordinates generate all regular functions on the generic group
after adjoining the generic field. -/
theorem adjoin_range_genericCoordinate_eq_top :
    Algebra.adjoin (A := AffineCoordinateRing K G.X) K
      (Set.range M.genericCoordinate) = ⊤ := by
  let e : AffineCoordinateRing K (ringBaseChange R K M.group.X) ≃ₐ[K]
      AffineCoordinateRing K G.X :=
    affineCoordinateAlgEquiv K ((Grp.forget _).mapIso M.genericIso.symm)
  have he : e.toAlgHom.range = ⊤ :=
    (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective
  have h := congrArg
    (fun A : Subalgebra K (AffineCoordinateRing K (ringBaseChange R K M.group.X)) =>
      A.map e.toAlgHom)
    (adjoin_range_baseChange_fst_eq_top R K M.group.X)
  rw [AlgHom.map_adjoin, Algebra.map_top, he] at h
  convert h using 1
  congr 1
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, rfl⟩
  · rintro ⟨c, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩

variable (L : Type u) [CommRing L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L]

/-- A point of the specified generic group is an actual point of the original model
over the same value algebra, with the integral base retained. -/
def genericModelPointEquiv :
    G.affinePoints (CommAlgCat.of K L) ≃ RingPoint R M.group.X L :=
  (Iso.homCongr (Iso.refl (ringTest K L))
    ((Grp.forget _).mapIso M.genericIso.symm)).trans
      (ringPointBaseChangeEquiv R K L M.group.X).symm

omit [IsAffine G.X.left] in
theorem genericModelPointEquiv_left
    (p : G.affinePoints (CommAlgCat.of K L)) :
    (M.genericModelPointEquiv L p).left =
      (p.left ≫ M.genericIso.inv.hom.hom.left) ≫
        pullback.fst M.group.X.hom (Spec.algebraMap R K) := by
  change ((ringPointBaseChangeEquiv R K L M.group.X).symm
    (𝟙 _ ≫ p ≫ M.genericIso.inv.hom.hom)).left = _
  rw [Category.id_comp, ringPointBaseChangeEquiv_symm_left]
  rfl

omit [IsDomain R] in
private theorem affine_coordinate_value
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (p : RingPoint R X L) (a : AffineCoordinateRing R X) :
    affineSchemePointEquiv R X L p a =
      (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom a := by
  have h : Spec.preimage (p.left ≫ X.left.isoSpec.hom) =
      p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, ← Scheme.isoSpec_Spec_hom]
    exact (Scheme.isoSpec_hom_naturality p.left).symm
  exact congrArg (fun f => f.hom a) h

omit [IsAffine G.X.left] in
/-- The original-model coordinate value is exactly evaluation of its generic
restriction on the original coefficient point. -/
theorem genericModelPointEquiv_evaluation
    (p : G.affinePoints (CommAlgCat.of K L))
    (a : AffineCoordinateRing R M.group.X) :
    affineSchemePointEquiv R M.group.X L (M.genericModelPointEquiv L p) a =
      G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a) := by
  rw [affine_coordinate_value, genericModelPointEquiv_left,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  rfl

end Langlands.GroupScheme.IntegralModel
