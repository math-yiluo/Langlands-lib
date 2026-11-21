import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian

/-! # Closed ideals for equalities of affinoid-algebra points -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))} {R : PresentedAffinoidAlgebra K}

/-- The closed ideal of equality of two affinoid-algebra points. The
criterion is tested by every algebraic coefficient map. -/
structure AffinoidSectionEqualizer (x y : RingPoints K X R) where
  ideal : Ideal R
  isClosed : IsClosed (ideal : Set R)
  annihilates_iff {T : Type u} [CommRing T] [Algebra K T] (φ : R →ₐ[K] T) :
    (∀ r ∈ ideal, φ r = 0) ↔ RingPoints.changeRing φ x = RingPoints.changeRing φ y

set_option backward.isDefEq.respectTransparency false in
/-- The separated diagonal cuts out an actual closed ideal on an
affinoid-algebra test. -/
def affinoidSectionEqualizer (hX : IsSeparated X) (x y : RingPoints K X R) :
    AffinoidSectionEqualizer x y := by
  apply Classical.choice
  obtain ⟨Z, ι, hEq, hi⟩ := exists_representsEqualizer_of_relative_diag
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hX x y
  obtain ⟨I, e, he⟩ := _root_.AlgebraicGeometry.IsClosedImmersion.Spec_iff.mp hi
  let q := Ideal.Quotient.mkₐ K I
  have hLeft : ι.left = e.hom ≫ (ringTestMap K q).left := he
  let eZ : Z ≅ ringTest K (R ⧸ I) := Over.isoMk e (by
    change e.hom ≫ (ringTest K (R ⧸ I)).hom = Z.hom
    rw [← Over.w (ringTestMap K q), ← Category.assoc, ← hLeft, Over.w ι])
  have hFac : eZ.hom ≫ ringTestMap K q = ι := Over.OverMorphism.ext hLeft.symm
  refine ⟨⟨I, PresentedAffinoidAlgebra.isClosed_ideal R I, ?_⟩⟩
  intro T _ _ φ
  change (∀ r ∈ I, φ r = 0) ↔
    X.presheaf.map (ringTestMap K φ).op x = X.presheaf.map (ringTestMap K φ).op y
  rw [← hEq (ringTestMap K φ)]
  constructor
  · intro hφ
    let ψ : (R ⧸ I) →ₐ[K] T := Ideal.Quotient.liftₐ I φ hφ
    refine ⟨ringTestMap K ψ ≫ eZ.inv, ?_⟩
    rw [← hFac, Category.assoc, Iso.inv_hom_id_assoc, ← ringTestMap_comp]
    rfl
  · rintro ⟨k, hk⟩ r hr
    let ψ : (R ⧸ I) →ₐ[K] T := affineRingPointEquiv K (R ⧸ I) T (k ≫ eZ.hom)
    have hψ : ψ.comp q = φ := by
      apply (affineRingPointEquiv K R T).symm.injective
      change ringTestMap K (ψ.comp q) = ringTestMap K φ
      rw [ringTestMap_comp, ringTestMap_affineRingPointEquiv, Category.assoc, hFac, hk]
    rw [← hψ, AlgHom.comp_apply]
    change ψ (Ideal.Quotient.mk I r) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hr, map_zero]

end Langlands.Analytic.SpaceAnalytification
