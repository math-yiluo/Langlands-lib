import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointProof
import Langlands.Geometry.Analytic.PolynomialLocusCharts
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Connected

/-! # Finite polynomial tests for ring-valued points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

section FiniteStages

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]

private abbrev stage (s : Finset R) : Subalgebra K R := Algebra.adjoin K (s : Set R)

private theorem stage_mono {s t : Finset R} (h : s ≤ t) : stage K R s ≤ stage K R t :=
  Algebra.adjoin_mono (Finset.coe_subset.mpr h)

private def stageDiagram : Finset R ⥤ CommAlgCat.{u} K where
  obj s := CommAlgCat.of K (stage K R s)
  map h := CommAlgCat.ofHom (Subalgebra.inclusion (stage_mono K R h.le))
  map_id _ := by ext1; apply AlgHom.ext; intro x; rfl
  map_comp _ _ := by ext1; apply AlgHom.ext; intro x; rfl

private def stageCocone : Cocone (stageDiagram K R) where
  pt := CommAlgCat.of K R
  ι := { app s := CommAlgCat.ofHom (stage K R s).val
         naturality _ _ _ := by ext1; apply AlgHom.ext; intro x; rfl }

private def stageCoconeIsColimit : IsColimit (stageCocone K R) := by
  classical
  let : IsConnected (Finset R) := IsFiltered.isConnected _
  let Q := (commAlgCatEquivUnder (CommRingCat.of K)).functor
  let U := Under.forget (CommRingCat.of K)
  let F := _root_.CategoryTheory.forget CommRingCat.{u}
  have : ReflectsColimit ((stageDiagram K R ⋙ Q) ⋙ U) F :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects Q (isColimitOfReflects U (isColimitOfReflects F ?_))
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : R)
    exact ⟨{x}, (⟨x, Algebra.subset_adjoin (by simp)⟩ : stage K R {x}), rfl⟩
  · intro i j (x : stage K R i) (y : stage K R j) (h : (x : R) = y)
    refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    change Subalgebra.inclusion (stage_mono K R le_sup_left) x =
      Subalgebra.inclusion (stage_mono K R le_sup_right) y
    exact Subtype.ext h

end FiniteStages

/-- Over a field, ring-valued points of a locally finite type algebraic space
are obtained by changing coefficients from finite polynomial tests. -/
def PolynomialPointFactorizationStatement : Prop :=
  ∀ {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {X : AlgebraicSpace (Spec (CommRingCat.of K))},
    LocallyOfFiniteTypeOverBase X → ∀ x : RingPoints K X R,
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (_ : FinitePolynomialPresentation K A)
      (φ : A →ₐ[K] R) (y : RingPoints K X A), RingPoints.changeRing φ y = x

/-- Take a finite-subset stage of the coefficient algebra. -/
theorem exists_polynomial_point_factorization : PolynomialPointFactorizationStatement.{u} := by
  intro K R _ _ _ X hX x
  classical
  have hfp : LocallyOfFinitePresentationOverBase X := by
    obtain ⟨U, a, ha, hs, hU⟩ := hX.exists_atlas
    exact ⟨U, a, ha, hs, LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hU⟩
  obtain ⟨i, y, hy⟩ := SpaceFilteredRingPoints.exists_changeRing_eq_of_colimit
    (stageDiagram K R) (stageCocone K R) (stageCoconeIsColimit K R) hfp x
  let : Algebra.FiniteType K (stage K R i) := Algebra.FiniteType.adjoin_of_finite i.finite_toSet
  exact ⟨stage K R i, inferInstance, inferInstance, FinitePolynomialPresentation.ofFiniteType K _,
    (stage K R i).val, y, hy⟩

end Langlands.Analytic.SpaceAnalytification
