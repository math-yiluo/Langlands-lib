import Langlands.AlgebraicGeometry.PointTopology.BoundedAffineNeighborhoods
import Langlands.AlgebraicGeometry.FiniteAlgebraFiberBound

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

instance affineChartWeilRestriction_locallyOfFiniteType :
    LocallyOfFiniteType (affineChartWeilRestriction A B Y).hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (affineChartWeilRestrictionOpenCover A B Y)
  intro U
  change LocallyOfFiniteType
    ((affineChartWeilRestrictionι A B Y U).left ≫ (affineChartWeilRestriction A B Y).hom)
  rw [Over.w]
  infer_instance

variable [CompactSpace Y.left] [IsSeparated Y.hom]
  (hY : HasFiniteAffineNeighborhoods Y.left)

/-- The original target affine family indexed by a bound on every coefficient fiber. -/
def affineChartWeilRestrictionFiniteChartFamily : Finset Y.left.affineOpens :=
  boundedAffineNeighborhoodFamily Y.left hY (finiteAlgebraFiberBound A B)

/-- The selected original affine Weil charts cover every actual point of the glued scheme. -/
theorem affineChartWeilRestrictionFiniteChartFamily_covers
    (x : (affineChartWeilRestriction A B Y).left) :
    ∃ U ∈ affineChartWeilRestrictionFiniteChartFamily A B Y hY,
      ∃ z : (affineWeilRestriction A B (openOver B Y U.val)).left,
        (affineChartWeilRestrictionι A B Y U).left z = x := by
  classical
  let W := affineChartWeilRestriction A B Y
  let C := W.left.residueField x
  let : Algebra A C := (Spec.preimage (W.left.fromSpecResidueField x ≫ W.hom)).hom.toAlgebra
  let p : ringTest A C ⟶ W := Over.homMk (W.left.fromSpecResidueField x) (by
    change W.left.fromSpecResidueField x ≫ W.hom =
      Spec.map (Spec.preimage (W.left.fromSpecResidueField x ≫ W.hom))
    exact (Spec.map_preimage _).symm)
  let q := affineChartWeilRestrictionComparison A B Y (ringTest A C) p
  let e := ringBaseChangeSpectrumIso A B C
  let g := e.inv ≫ q
  let : IsArtinianRing (C ⊗[A] B) := isArtinian_of_tower C inferInstance
  let E := (PrimeSpectrum.comapEquiv (Algebra.TensorProduct.comm A B C).toRingEquiv).toEquiv
  let : Finite (PrimeSpectrum (B ⊗[A] C)) := Finite.of_equiv _ E.symm
  have hcard : Nat.card (PrimeSpectrum (B ⊗[A] C)) ≤ finiteAlgebraFiberBound A B := by
    rw [Nat.card_congr E]
    exact finiteAlgebraFiberBound_card A B C
  obtain ⟨U, hU, hg⟩ := boundedAffineNeighborhoodFamily_covers Y.left hY
    (finiteAlgebraFiberBound A B) hcard g.left
  have hq : Set.range q.left ⊆ U.val := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, rfl⟩ := e.inv.left.surjective z
    exact hg ⟨a, rfl⟩
  let qU := relativeOpenLift B q U.val hq
  let r := (affineWeilRestrictionTestEquiv A B (openOver B Y U.val) (ringTest A C)).symm qU
  have hr : r ≫ affineChartWeilRestrictionι A B Y U = p := by
    apply affineChartWeilRestrictionComparison_injective A B Y (ringTest A C)
    rw [affineChartWeilRestrictionComparison_chart]
    change affineWeilRestrictionTestEquiv A B (openOver B Y U.val) (ringTest A C)
      ((affineWeilRestrictionTestEquiv A B (openOver B Y U.val) (ringTest A C)).symm qU) ≫
        openOverι B Y U.val = q
    rw [Equiv.apply_symm_apply]
    exact relativeOpenLift_fac B q U.val hq
  refine ⟨U, hU, r.left (IsLocalRing.closedPoint C), ?_⟩
  have heq := congrArg (fun f : ringTest A C ⟶ W => f.left (IsLocalRing.closedPoint C)) hr
  change (affineChartWeilRestrictionι A B Y U).left (r.left (IsLocalRing.closedPoint C)) =
    W.left.fromSpecResidueField x (IsLocalRing.closedPoint C) at heq
  simpa only [Scheme.fromSpecResidueField_apply] using heq

/-- A finite open cover of the actual Weil scheme by its original affine Weil charts. -/
def affineChartWeilRestrictionFiniteOpenCover : (affineChartWeilRestriction A B Y).left.OpenCover where
  I₀ := affineChartWeilRestrictionFiniteChartFamily A B Y hY
  X U := (affineWeilRestriction A B (openOver B Y U.val.val)).left
  f U := (affineChartWeilRestrictionι A B Y U.val).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨U, hU, z, hz⟩ := affineChartWeilRestrictionFiniteChartFamily_covers A B Y hY x
    exact ⟨⟨U, hU⟩, z, hz⟩

include hY in
/-- Compactness is derived from the finite affine cover, rather than assumed of the Weil model. -/
theorem affineChartWeilRestriction_compactSpace :
    CompactSpace (affineChartWeilRestriction A B Y).left := by
  let : Finite (affineChartWeilRestrictionFiniteOpenCover A B Y hY).I₀ := by
    change Finite ↥(affineChartWeilRestrictionFiniteChartFamily A B Y hY)
    infer_instance
  let : ∀ i, CompactSpace ((affineChartWeilRestrictionFiniteOpenCover A B Y hY).X i) := by
    intro i
    change CompactSpace (affineWeilRestriction A B (openOver B Y i.val.val)).left
    infer_instance
  exact (affineChartWeilRestrictionFiniteOpenCover A B Y hY).compactSpace

include hY in
/-- Together with local finite type, this is the actual Weil model's finite-type property. -/
theorem affineChartWeilRestriction_quasiCompact :
    QuasiCompact (affineChartWeilRestriction A B Y).hom := by
  let := affineChartWeilRestriction_compactSpace A B Y hY
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology
