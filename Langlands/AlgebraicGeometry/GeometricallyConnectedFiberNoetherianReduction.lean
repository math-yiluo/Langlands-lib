import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberConstructibilityStatement
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian affine reduction for geometric-connectedness constructibility -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The Noetherian affine case of geometric-connectedness fibre constructibility. -/
def NoetherianAffineGeometricallyConnectedFiberConstructibility : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f],
      IsConstructible (geometricallyConnectedFiberLocus f)

/-- Actual finite-presentation approximation reduces every affine target to the
Noetherian affine assertion, without making the source affine or separated. -/
theorem isConstructible_geometricallyConnectedFiberLocus_spec_of_noetherianAffine
    (h : NoetherianAffineGeometricallyConnectedFiberConstructibility.{u})
    (R : Type u) [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    IsConstructible (geometricallyConnectedFiberLocus f) := by
  let : Algebra (ULift.{u} ℤ) R := ULift.algebra' ℤ R
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T, hT, _, X₀, f₀, π, hfp, hqc, hqs, hs⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent (A₀ := ULift.{u} ℤ) f ∅
  let : Algebra.FiniteType (ULift.{u} ℤ) T := T.fg_iff_finiteType.mp hT
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) T
  let := hfp
  let := hqc
  let := hqs
  rw [geometricallyConnectedFiberLocus_baseChange hs]
  exact (Spec.map (CommRingCat.ofHom (algebraMap T R))).isConstructible_preimage (h T f₀)

/-- Local constructibility on arbitrary schemes is equivalent to constructibility
over Noetherian affine bases. -/
theorem geometricallyConnectedFiberLocalConstructibility_iff_noetherianAffine :
    GeometricallyConnectedFiberLocalConstructibility.{u} ↔
      NoetherianAffineGeometricallyConnectedFiberConstructibility.{u} := by
  constructor
  · intro h R _ _ X f _ _ _
    exact (h f).isConstructible
  · intro h X Y f _ _ _
    apply IsLocallyConstructible.of_isOpenCover Y.affineCover.isOpenCover_opensRange
    intro i
    have : LocallyOfFinitePresentation (pullback.snd f (Y.affineCover.f i)) :=
      MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
    have : QuasiCompact (pullback.snd f (Y.affineCover.f i)) :=
      MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
    have : QuasiSeparated (pullback.snd f (Y.affineCover.f i)) :=
      MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ inferInstance
    have hi := isConstructible_geometricallyConnectedFiberLocus_spec_of_noetherianAffine h
      _ (pullback.snd f (Y.affineCover.f i))
    rw [geometricallyConnectedFiberLocus_baseChange (IsPullback.of_hasPullback f _)] at hi
    convert! hi.isLocallyConstructible.preimage_of_isOpenEmbedding
      (Y.affineCover.f i).isoOpensRange.inv.isOpenEmbedding using 1
    ext y
    change GeometricallyConnected (f.fiberToSpecResidueField y.val) ↔
      GeometricallyConnected
        (f.fiberToSpecResidueField
          ((Y.affineCover.f i) ((Y.affineCover.f i).isoOpensRange.inv y)))
    have hy : (Y.affineCover.f i) ((Y.affineCover.f i).isoOpensRange.inv y) = y.val := by
      change ((Y.affineCover.f i).isoOpensRange.inv ≫ Y.affineCover.f i) y = _
      rw [(Y.affineCover.f i).isoOpensRange_inv_comp]
      rfl
    rw [hy]

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
