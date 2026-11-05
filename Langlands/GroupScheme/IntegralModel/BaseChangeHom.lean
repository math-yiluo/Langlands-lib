import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.IntegralModel

/-! # Changing the coefficient ring of actual integral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

variable {R A K : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Field K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- Pull an integral model to a new domain whose inclusion in the same generic
field factors through the given actual map of spectra. -/
def baseChangeModel (M : IntegralModel R K G)
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (hb : Spec.algebraMap A K ≫ b = Spec.algebraMap R K) : IntegralModel A K G where
  group := (GroupScheme.baseChange b).obj M.group
  affine := by
    change IsAffineHom (pullback.snd M.group.X.hom b)
    infer_instance
  flat := by
    change Flat (pullback.snd M.group.X.hom b)
    infer_instance
  finiteType := by
    change LocallyOfFiniteType (pullback.snd M.group.X.hom b)
    infer_instance
  genericIso := Descent.pullbackComparison b _ _ hb M.group ≪≫ M.genericIso

/-- Smoothness persists for the structural map of the changed actual model. -/
theorem smooth_baseChangeModel (M : IntegralModel R K G)
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (hb : Spec.algebraMap A K ≫ b = Spec.algebraMap R K)
    [Smooth M.group.X.hom] : Smooth (M.baseChangeModel b hb).group.X.hom := by
  change Smooth (pullback.snd M.group.X.hom b)
  infer_instance

/-- Change both models and their supplied generic-compatible homomorphism. -/
def Hom.baseChange {M : IntegralModel R K G} {N : IntegralModel R K H}
    {f : G ⟶ H} (φ : M.Hom N f)
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (hb : Spec.algebraMap A K ≫ b = Spec.algebraMap R K) :
    (M.baseChangeModel b hb).Hom (N.baseChangeModel b hb) f where
  hom := (GroupScheme.baseChange b).map φ.hom
  generic_comm := by
    change _ ≫ ((Descent.pullbackComparison b _ _ hb N.group).hom ≫ N.genericIso.hom) =
      ((Descent.pullbackComparison b _ _ hb M.group).hom ≫ M.genericIso.hom) ≫ f
    rw [← Category.assoc, Descent.pullbackComparison_naturality, Category.assoc,
      φ.generic_comm, Category.assoc]

/-- A closed model homomorphism remains closed after changing the base. -/
theorem Hom.isClosedImmersion_baseChange {M : IntegralModel R K G}
    {N : IntegralModel R K H} {f : G ⟶ H} (φ : M.Hom N f)
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (hb : Spec.algebraMap A K ≫ b = Spec.algebraMap R K)
    [IsClosedImmersion φ.hom.hom.hom.left] :
    IsClosedImmersion (φ.baseChange b hb).hom.hom.hom.left := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map φ.hom).hom.hom.left ≫ pullback.snd N.group.X.hom b)
      (pullback.fst M.group.X.hom b) b (φ.hom.hom.hom.left ≫ N.group.X.hom) := by
    change IsPullback (((Over.pullback b).map φ.hom.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w φ.hom.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback M.group.X.hom b).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange b).map φ.hom).hom.hom.left ≫
        pullback.fst N.group.X.hom b =
        pullback.fst M.group.X.hom b ≫ φ.hom.hom.hom.left by
      change ((Over.pullback b).map φ.hom.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback N.group.X.hom b).flip
  exact MorphismProperty.of_isPullback hp.flip inferInstance

end Langlands.GroupScheme.IntegralModel
