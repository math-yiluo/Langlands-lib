import Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness
import Langlands.AlgebraicGeometry.Picard.GenericFractionField
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Smoothness from the actual generic and special fibres over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- The canonical quotient residue field identifies with the scheme residue field
at the closed point of the spectrum of a local ring. -/
def closedPointResidueSpecIso (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ≅
      Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) :=
  let e := (RingEquiv.ofBijective
    (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R).ResidueField)
    (IsLocalRing.maximalIdeal R).bijective_algebraMap_quotient_residueField
    ).toCommRingCatIso
  Scheme.Spec.mapIso e.symm.op ≪≫
    Scheme.Spec.mapIso
      (Scheme.Spec.residueFieldIso (CommRingCat.of R) (IsLocalRing.closedPoint R)).op

/-- This comparison is over the original local ring and its actual quotient map. -/
@[reassoc]
theorem closedPointResidueSpecIso_hom_fromSpecResidueField
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (closedPointResidueSpecIso R).hom ≫
        (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) =
      Spec.algebraMap R (IsLocalRing.ResidueField R) := by
  let e : CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R) ≅
      CommRingCat.of (IsLocalRing.maximalIdeal R).ResidueField :=
    (RingEquiv.ofBijective _ (IsLocalRing.maximalIdeal R
      ).bijective_algebraMap_quotient_residueField).toCommRingCatIso
  change (Spec.map e.inv ≫
    Spec.map (Scheme.Spec.residueFieldIso
      (CommRingCat.of R) (IsLocalRing.closedPoint R)).hom) ≫ _ = _
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  dsimp only [IsLocalRing.closedPoint]
  simp only [Category.assoc, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
  rw [← Spec.map_comp]
  congr 1
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  ext r
  exact ((IsLocalRing.maximalIdeal R).algebraMap_quotient_residueField_mk r).symm

/-- Smoothness of a coefficient pullback persists after any further coefficient map. -/
theorem smooth_pullback_comp_right {X S T U : Scheme.{u}}
    (p : X ⟶ S) (b : T ⟶ S) (a : U ⟶ T)
    [Smooth (pullback.snd p b)] : Smooth (pullback.snd p (a ≫ b)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd p b a]
  infer_instance

private theorem smooth_fiber_of_coefficient_iso {R : Type u} [CommRing R]
    {X T : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (y : Spec (CommRingCat.of R)) (b : T ⟶ Spec (CommRingCat.of R))
    (e : T ≅ Spec ((Spec (CommRingCat.of R)).residueField y))
    (he : e.hom ≫ (Spec (CommRingCat.of R)).fromSpecResidueField y = b)
    [Smooth (pullback.snd p b)] : Smooth (p.fiberToSpecResidueField y) := by
  have hb : (Spec (CommRingCat.of R)).fromSpecResidueField y = e.inv ≫ b := by
    rw [← he, Iso.inv_hom_id_assoc]
  change Smooth (pullback.snd p ((Spec (CommRingCat.of R)).fromSpecResidueField y))
  rw [hb]
  exact smooth_pullback_comp_right p b e.inv

/-- A flat, locally finite-type family over a DVR is smooth if its actual
fraction-field and quotient-residue-field pullbacks are smooth. -/
theorem smooth_of_generic_special_fibers
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] [LocallyOfFiniteType p]
    [Smooth (pullback.snd p (Spec.algebraMap R K))]
    [Smooth (pullback.snd p (Spec.algebraMap R (IsLocalRing.ResidueField R)))] :
    Smooth p := by
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  rcases FlatReducedDvrConnectedness.point_eq_generic_or_closed R y with hy | hy
  · have hy' : y = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine]
      exact hy
    rw [hy']
    exact smooth_fiber_of_coefficient_iso p _ (Spec.algebraMap R K)
      (fractionFieldGenericPointIso (CommRingCat.of R) K)
      (fractionFieldGenericPointIso_hom_fromSpecResidueField (CommRingCat.of R) K)
  · subst y
    exact smooth_fiber_of_coefficient_iso p _
      (Spec.algebraMap R (IsLocalRing.ResidueField R))
      (closedPointResidueSpecIso R)
      (closedPointResidueSpecIso_hom_fromSpecResidueField R)

end Langlands.AlgebraicGeometry
