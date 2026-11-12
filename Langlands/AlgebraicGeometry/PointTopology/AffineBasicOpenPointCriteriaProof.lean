import Langlands.AlgebraicGeometry.PointTopology.AffineBasicOpenPointCriteriaStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineLinePunctureUnits
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs

/-!
# Basic open subschemes and points over a topological ring: proof

Proof of Conrad's basic-open criteria (printed pp.3–4). The backward directions use the
Library's localization point comparisons; the forward directions specialize to the affine line
`A = R[X]` and `f = X`, whose points are `S` and whose basic-open points are `Sˣ`.
-/

noncomputable section

universe u

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

section

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Clause 1: the image of the basic-open points is the unit locus of `f`. -/
theorem range_basicOpenPointMap (A : Type u) [CommRing A] [Algebra R A] (f : A) :
    Set.range (basicOpenPointMap R S A f) = {p : AlgPoint R A S | IsUnit (p f)} := by
  have h := AlgPoint.range_precomp_localization (R := R) (S := S)
    (L := Localization.Away f) (Submonoid.powers f)
  simp only [AlgPoint.unit_powers_iff] at h
  exact h

variable [TopologicalSpace S] [IsTopologicalRing S]

/-- Evaluation at the coordinate identifies the points of the affine line with `S`. -/
def lineCoordinateHomeomorph : AlgPoint R (MvPolynomial Unit R) S ≃ₜ S :=
  (AlgPoint.polynomialPointHomeomorph (R := R) (S := S) Unit).trans
    (Homeomorph.funUnique Unit S)

@[simp] theorem lineCoordinateHomeomorph_apply (p : AlgPoint R (MvPolynomial Unit R) S) :
    lineCoordinateHomeomorph R S p = p (MvPolynomial.X ()) := rfl

/-- On the affine line, `Units.val` is the basic-open point map at the coordinate, read through
the coordinate homeomorphisms. -/
theorem unitsVal_eq_basicOpenPointMap :
    (Units.val : Sˣ → S) = lineCoordinateHomeomorph R S ∘
      basicOpenPointMap R S (MvPolynomial Unit R) (MvPolynomial.X ()) ∘
        (AlgPoint.polynomialAwayUnitHomeomorph R S).symm := by
  funext u
  change (u : S) = (AlgPoint.polynomialAwayUnitEquiv R S).symm u
    (algebraMap _ _ (MvPolynomial.X () : MvPolynomial Unit R))
  rw [AlgPoint.polynomialAwayUnitEquiv_symm_algebraMap, MvPolynomial.aeval_X]

/-- Clause 2, forward: openness of all basic-open images forces the units to be open. -/
theorem isOpen_units_of_isOpen_range_basicOpenPointMap
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (f : A),
      IsOpen (Set.range (basicOpenPointMap R S A f))) :
    IsOpen {s : S | IsUnit s} := by
  have hA := h (MvPolynomial Unit R) (MvPolynomial.X ())
  rw [range_basicOpenPointMap] at hA
  exact (lineCoordinateHomeomorph R S).isOpen_preimage.mp hA

omit [IsTopologicalRing S] in
/-- Clause 2, backward: the image is the preimage of the units under evaluation at `f`. -/
theorem isOpen_range_basicOpenPointMap_of_isOpen_units (hS : IsOpen {s : S | IsUnit s})
    (A : Type u) [CommRing A] [Algebra R A] (f : A) :
    IsOpen (Set.range (basicOpenPointMap R S A f)) := by
  rw [range_basicOpenPointMap]
  exact hS.preimage (AlgPoint.continuous_eval f)

/-- Clause 3, forward: the embedding property on the affine line is that of `Units.val`. -/
theorem isEmbedding_unitsVal_of_isEmbedding_basicOpenPointMap
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (f : A),
      IsEmbedding (basicOpenPointMap R S A f)) :
    IsEmbedding (Units.val : Sˣ → S) := by
  rw [unitsVal_eq_basicOpenPointMap R S]
  exact (lineCoordinateHomeomorph R S).isEmbedding.comp
    ((h (MvPolynomial Unit R) (MvPolynomial.X ())).comp
      (AlgPoint.polynomialAwayUnitHomeomorph R S).symm.isEmbedding)

/-- Clause 3, backward: localization points embed when units carry the subspace topology. -/
theorem isEmbedding_basicOpenPointMap_of_isEmbedding_unitsVal
    (hS : IsEmbedding (Units.val : Sˣ → S)) (A : Type u) [CommRing A] [Algebra R A] (f : A) :
    IsEmbedding (basicOpenPointMap R S A f) :=
  AlgPoint.isEmbedding_precomp_localization (R := R) (S := S) (L := Localization.Away f)
    (Submonoid.powers f) hS

/-- Clause 4, forward: combine the forward directions of clauses 2 and 3. -/
theorem isOpenEmbedding_unitsVal_of_isOpenEmbedding_basicOpenPointMap
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (f : A),
      IsOpenEmbedding (basicOpenPointMap R S A f)) :
    IsOpenEmbedding (Units.val : Sˣ → S) :=
  ⟨isEmbedding_unitsVal_of_isEmbedding_basicOpenPointMap R S
      (fun A _ _ _ f => (h A f).isEmbedding),
    isOpen_units_of_isOpen_range_basicOpenPointMap R S
      (fun A _ _ _ f => (h A f).isOpen_range)⟩

/-- Clause 4, backward: an open embedding `Units.val` is Mathlib's `IsOpenUnits`, under which
restriction from a localization away from one element is an open embedding. -/
theorem isOpenEmbedding_basicOpenPointMap_of_isOpenEmbedding_unitsVal
    (hS : IsOpenEmbedding (Units.val : Sˣ → S))
    (A : Type u) [CommRing A] [Algebra R A] (f : A) :
    IsOpenEmbedding (basicOpenPointMap R S A f) :=
  haveI : IsOpenUnits S := ⟨hS⟩
  AlgPoint.isOpenEmbedding_precomp_away (R := R) (S := S) (L := Localization.Away f) f

end

/-- Conrad's basic-open criteria (printed pp.3–4) hold. -/
theorem affineBasicOpenPointCriteria : AffineBasicOpenPointCriteria.{u} := by
  intro R S _ _ _ _ _
  exact ⟨range_basicOpenPointMap R S,
    ⟨isOpen_units_of_isOpen_range_basicOpenPointMap R S,
      fun hS A _ _ _ f => isOpen_range_basicOpenPointMap_of_isOpen_units R S hS A f⟩,
    ⟨isEmbedding_unitsVal_of_isEmbedding_basicOpenPointMap R S,
      fun hS A _ _ _ f => isEmbedding_basicOpenPointMap_of_isEmbedding_unitsVal R S hS A f⟩,
    ⟨isOpenEmbedding_unitsVal_of_isOpenEmbedding_basicOpenPointMap R S,
      fun hS A _ _ _ f => isOpenEmbedding_basicOpenPointMap_of_isOpenEmbedding_unitsVal R S hS A f⟩⟩

end Langlands.AlgebraicGeometry.PointTopology
