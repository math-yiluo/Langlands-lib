import Langlands.AlgebraicGeometry.Modules.NilpotentBaseAffineness
import Langlands.GroupScheme.HomScheme.AffineFiberValuation
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Affine group-scheme pullbacks to local Artinian tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules

namespace Langlands.GroupScheme

/-- A locally finite-type group scheme with affine residue fibres is affine
on every local Artinian test. -/
def AffineResidueFiberArtinianPullbackStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [LocallyOfFiniteType G.X.hom],
    HasAffineResidueFibers G →
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (b : Spec (CommRingCat.of A) ⟶ S),
      IsAffineHom ((baseChange b).obj G).X.hom

/-- Affineness on a local Artinian test follows from the actual closed fibre
and nilpotence of the maximal ideal. -/
theorem isAffineHom_artinianPullback_of_residueFibers :
    AffineResidueFiberArtinianPullbackStatement.{u} := by
  intro S G _ h A _ _ _ b
  let H := (baseChange b).obj G
  let s := IsLocalRing.closedPoint A
  have : LocallyOfFiniteType H.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have hFibre : IsAffineHom (RelativeIdentityComponent.residueFiber H s).X.hom := h.baseChange b s
  have : IsAffine (H.X.hom.fiber s) :=
    @isAffine_of_isAffineHom _ _ (RelativeIdentityComponent.residueFiber H s).X.hom
      hFibre inferInstance
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal A) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have : IsAffine H.X.left :=
    isAffine_of_affine_nilpotent_base (IdealAdic.isPullback_fiberι_closedPoint H.X.hom) hnil
  exact isAffineHom_of_isAffine H.X.hom

end Langlands.GroupScheme
