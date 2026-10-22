import Langlands.Representation.CompactCoefficient.Isotypic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Natural compact-isotypic projectors with intrinsic range and kernel

This proposition states Bernstein--Zelevinsky (1976), §§2.42--2.44, with
intrinsic range and kernel identifications and their elementary consequences.
It supplies no proof or chosen projector.
-/

namespace Langlands

open MeasureTheory

universe uG uV uW

/-- A simultaneous natural family of equivariant compact-isotypic projectors
on arbitrary smooth complex representations. The class-representative and
ambient carrier universes are independent. Range, kernel, orthogonality,
compact coefficients of the range and fixed-vector vanishing are conclusions.
The group and Haar hypotheses are those of the compact-coefficient splitting
and semisimplicity statements. -/
def CompactCoefficientProjectorStatement
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
    [Measure.IsMulRightInvariant μ] : Prop :=
  ∃ P : (c : CompactCoefficientClass.{uG, uV} G) →
      (A : SmoothRep.{0, uG, uW} ℂ G) →
        A.representation.IntertwiningMap A.representation,
    (∀ c A, (P c A).comp (P c A) = P c A) ∧
    (∀ c A,
      (P c A).range = CompactCoefficientClass.isotypicSubrepresentation c A ∧
      (P c A).ker = CompactCoefficientClass.annihilatorSubrepresentation c A) ∧
    (∀ c (A B : SmoothRep.{0, uG, uW} ℂ G)
      (f : A.representation.IntertwiningMap B.representation),
        f.comp (P c A) = (P c B).comp f) ∧
    (∀ c d, c ≠ d → ∀ A, (P c A).comp (P d A) = 0) ∧
    (∀ c A, HasCompactSmoothDualCoefficients (P c A).range.toRepresentation) ∧
    (∀ c (A : SmoothRep.{0, uG, uW} ℂ G) (K : OpenSubgroup G),
      IsCompact (K : Set G) →
      ¬ CompactCoefficientClass.HasFixedVector K.toSubgroup c →
        ∀ v : A, v ∈ fixedVectors A.representation K.toSubgroup → P c A v = 0)

end Langlands
