import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonRefinement
import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonSourceSquare

/-! # Further refinement of specified framed comparisons -/

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
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual quotient-reduced framing square survives refinement of the original
specified target comparison. -/
theorem FramingSquare.refine (e : X.residueMap = Y.residueMap)
    (g : SpecialAtlas.Comparison X.target.val Y.target.val)
    (h : FramingSquare e g) (q : BasicAtlas.CoverRefinement g.left.atlas) :
    FramingSquare e (g.refine q) := by
  have hr := ReducedFramingSquare.refine e (SpecialAtlas.reductionComparison g) h
    (SpecialAtlas.reductionComparisonRefinement g q)
  obtain ⟨hL, hR, hs⟩ :=
    (SpecialAtlas.reductionComparison_refine_source_square g q).symm
  exact ReducedFramingSquare.of_source_square e _ _ hL hR hs hr

namespace Comparison

/-- Refine the specified target comparison, retaining its residue equality and
the proved actual framing square. -/
def refine (f : Comparison X Y)
    (q : BasicAtlas.CoverRefinement f.targetComparison.left.atlas) : Comparison X Y where
  targetComparison := f.targetComparison.refine q
  residue_eq := f.residue_eq
  square := FramingSquare.refine f.residue_eq f.targetComparison f.square q

@[simp]
theorem refine_targetComparison (f : Comparison X Y)
    (q : BasicAtlas.CoverRefinement f.targetComparison.left.atlas) :
    (f.refine q).targetComparison = f.targetComparison.refine q := rfl

@[simp]
theorem refine_residue_eq (f : Comparison X Y)
    (q : BasicAtlas.CoverRefinement f.targetComparison.left.atlas) :
    (f.refine q).residue_eq = f.residue_eq := rfl

end Comparison

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
