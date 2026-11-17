import Langlands.Geometry.FormalGroup.DrinfeldFramedClasses
import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonJoin

/-! # Collapse finite framed comparison chains to actual comparisons -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}
variable {X Y Z : DrinfeldFramedAtlas Φ A}

/-- Actual framed identity comparisons give direct reflexivity. -/
theorem directlyComparable_refl (X : DrinfeldFramedAtlas Φ A) : DirectlyComparable X X :=
  ⟨Comparison.refl X⟩

/-- Direct comparison reverses the same actual target maps and framing square. -/
theorem DirectlyComparable.symm (h : DirectlyComparable X Y) : DirectlyComparable Y X :=
  h.map Comparison.symm

/-- Product-cover composition gives transitivity of actual direct comparison. -/
theorem DirectlyComparable.trans (h : DirectlyComparable X Y) (k : DirectlyComparable Y Z) :
    DirectlyComparable X Z := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := k
  exact ⟨f.trans g⟩

/-- Every finite chain collapses to one actual comparison of the original targets. -/
theorem ChainEquivalent.directlyComparable (h : ChainEquivalent X Y) :
    DirectlyComparable X Y := by
  induction h with
  | refl => exact directlyComparable_refl _
  | tail _ hg ih => exact ih.trans hg

/-- The existing finite-chain relation is precisely existence of an actual comparison. -/
theorem chainEquivalent_iff_directlyComparable (X Y : DrinfeldFramedAtlas Φ A) :
    ChainEquivalent X Y ↔ DirectlyComparable X Y :=
  ⟨ChainEquivalent.directlyComparable, fun ⟨f⟩ => chainEquivalent_of_comparison f⟩

/-- Equality in the existing quotient is precisely one actual framed comparison. -/
theorem comparisonClassOf_eq_iff_directlyComparable (X Y : DrinfeldFramedAtlas Φ A) :
    comparisonClassOf X = comparisonClassOf Y ↔ DirectlyComparable X Y :=
  (comparisonClassOf_eq_iff X Y).trans (chainEquivalent_iff_directlyComparable X Y)

namespace Comparison

/-- Choose an actual framed comparison from the proved exact quotient equality criterion. -/
def ofClassEq (h : comparisonClassOf X = comparisonClassOf Y) : Comparison X Y :=
  Classical.choice ((comparisonClassOf_eq_iff_directlyComparable X Y).mp h)

end Comparison

namespace ComparisonClass

/-- Any representative of the class compares directly with the stored chosen representative. -/
def comparisonToRepresentative (q : ComparisonClass Φ A) (X : DrinfeldFramedAtlas Φ A)
    (h : comparisonClassOf X = q) : Comparison X q.representative :=
  Comparison.ofClassEq (h.trans (comparisonClassOf_representative q).symm)

/-- The reverse comparison is the actual inverse of the chosen comparison. -/
def comparisonFromRepresentative (q : ComparisonClass Φ A) (X : DrinfeldFramedAtlas Φ A)
    (h : comparisonClassOf X = q) : Comparison q.representative X :=
  (comparisonToRepresentative q X h).symm

end ComparisonClass

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
