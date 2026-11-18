import Langlands.AlgebraicGeometry.DvrStableNormalization.AffineCover
import Langlands.AlgebraicGeometry.DvrStableNormalization.AffineHypotheses

/-! # The affine cover over a DVR and its base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section Cover

variable (X : Over (Spec (CommRingCat.of R))) [QuasiCompact X.hom]

instance compactSpace_left : CompactSpace X.left :=
  QuasiCompact.compactSpace_of_compactSpace X.hom

/-- The finite affine cover as a scheme over `Spec R`. -/
abbrev coverOver : Over (Spec (CommRingCat.of R)) := Over.mk (coverMap X.left ≫ X.hom)

/-- The covering map as a morphism over `Spec R`. -/
abbrev coverHom : coverOver X ⟶ X := Over.homMk (coverMap X.left)

instance quasiCompact_coverMap [IsSeparated X.hom] : QuasiCompact (coverMap X.left) :=
  QuasiCompact.of_comp _ X.hom

instance flat_coverOver [Flat X.hom] : Flat (coverOver X).hom := by
  change Flat (coverMap X.left ≫ X.hom); infer_instance

instance lft_coverOver [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (coverOver X).hom := by
  change LocallyOfFiniteType (coverMap X.left ≫ X.hom); infer_instance

instance smooth_generic_coverOver
    [Smooth (pullback.snd X.hom (Spec.algebraMap R (FractionRing R)))] :
    Smooth (pullback.snd (coverOver X).hom (Spec.algebraMap R (FractionRing R))) := by
  change Smooth (pullback.snd (coverMap X.left ≫ X.hom) (Spec.algebraMap R (FractionRing R)))
  have h := pullbackRightPullbackFstIso_hom_snd X.hom (Spec.algebraMap R (FractionRing R))
    (coverMap X.left)
  rw [← Iso.eq_inv_comp] at h
  rw [h]
  infer_instance

end Cover

section BaseChange

variable {R' : Type u} [CommRing R'] (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {Z X : Over (Spec (CommRingCat.of R))} (g : Z ⟶ X)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The base change of `g` along `b` is a pullback of `g.left`. -/
theorem isPullback_baseChange :
    IsPullback (pullback.fst Z.hom b) ((Over.pullback b).map g).left g.left
      (pullback.fst X.hom b) := by
  have hg : g.left ≫ X.hom = Z.hom := Over.w g
  have h2 : ((Over.pullback b).map g).left ≫ pullback.snd X.hom b = pullback.snd Z.hom b :=
    pullback.lift_snd _ _ _
  have h1 : ((Over.pullback b).map g).left ≫ pullback.fst X.hom b =
      pullback.fst Z.hom b ≫ g.left := pullback.lift_fst _ _ _
  refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback X.hom b)
  rw [h2, hg]
  exact IsPullback.of_hasPullback Z.hom b

end BaseChange

end Langlands.AlgebraicGeometry.DvrStableNormalization
