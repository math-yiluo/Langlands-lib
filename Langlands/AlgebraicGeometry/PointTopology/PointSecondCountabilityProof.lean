import Langlands.AlgebraicGeometry.PointTopology.PointSecondCountabilityStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs

/-!
# Second countability from finite coordinates and finite affine covers
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [SecondCountableTopology S]

/-- Finite coordinates embed the actual algebra-point space in a finite power. -/
theorem affineAlgebraPointSecondCountability :
    AffineAlgebraPointSecondCountability R S := by
  intro A _ _ _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  exact ((AlgPoint.polynomialPointHomeomorph (R := R) (S := S) (Fin n)).isEmbedding.comp
    (AlgPoint.isEmbedding_precomp_of_surjective f hf)).secondCountableTopology

/-- Transfer finite-coordinate second countability to actual affine scheme points. -/
theorem affineSchemePointSecondCountability :
    AffineSchemePointSecondCountability R S := by
  intro X _ _
  let : SecondCountableTopology (AlgPoint R (AffineCoordinateRing R X) S) :=
    affineAlgebraPointSecondCountability R S (AffineCoordinateRing R X)
  exact (affineSchemePointHomeomorph R X S).isEmbedding.secondCountableTopology

/-- A finite affine cover gives an open quotient of second-countable chart spaces. -/
theorem schemePointSecondCountability [IsLocalRing S] [IsOpenUnits S] :
    SchemePointSecondCountability R S := by
  intro X _ _
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  obtain ⟨C, hC, hcover⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
      (X := X.left) (U := Set.univ)).mp ⟨isCompact_univ, isOpen_univ⟩
  let : Fintype C := hC.fintype
  let affineC (U : C) : IsAffine (openOver R X U.val.val).left := U.val.property
  let τC (U : C) : TopologicalSpace (RingPoint R (openOver R X U.val.val) S) := by
    let := affineC U
    exact inferInstance
  let secondC (U : C) : SecondCountableTopology
      (RingPoint R (openOver R X U.val.val) S) := by
    let := affineC U
    let : LocallyOfFiniteType (openOver R X U.val.val).hom := by
      change LocallyOfFiniteType (U.val.val.ι ≫ X.hom)
      infer_instance
    exact affineSchemePointSecondCountability R S (openOver R X U.val.val)
  let f : (Σ U : C, RingPoint R (openOver R X U.val.val) S) → RingPoint R X S :=
    fun p => openPointMap R X S p.1.val.val p.2
  have hf : IsOpenQuotientMap f := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      have hp : p.left (IsLocalRing.closedPoint S) ∈ ⋃ U ∈ C, (U : Set X.left) := by
        rw [← hcover]
        trivial
      obtain ⟨U, hU⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hUC, hpU⟩ := Set.mem_iUnion.mp hU
      refine ⟨⟨⟨U, hUC⟩, openPointLift R X S U.val p
        ((range_subset_open_iff_closedPoint R X S U.val p).mpr hpU)⟩, ?_⟩
      exact openPointMap_lift R X S U.val p
        ((range_subset_open_iff_closedPoint R X S U.val p).mpr hpU)
    · exact continuous_sigma (fun U => schemePointTopology_continuous_chart R X S U.val)
    · exact isOpenMap_sigma.mpr
        (fun U => (isOpenEmbedding_schemeAffineChart R S X U.val).isOpenMap)
  exact hf.secondCountableTopology

/-- The grouped local second-countability statement. -/
theorem pointSecondCountability : PointSecondCountabilityStatement R S := by
  refine ⟨affineAlgebraPointSecondCountability R S,
    affineSchemePointSecondCountability R S, ?_⟩
  intro _ _
  exact schemePointSecondCountability R S

end Langlands.AlgebraicGeometry.PointTopology
