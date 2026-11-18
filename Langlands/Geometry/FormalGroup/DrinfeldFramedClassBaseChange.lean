import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonBaseChange
import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonCollapse

/-! # Nilp-base extension on actual framed comparison classes -/

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
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Base extension retains existence of an actual original framed comparison. -/
theorem DirectlyComparable.baseChange (h : DirectlyComparable X Y) (f : A ⟶ B) :
    DirectlyComparable (X.baseChange f) (Y.baseChange f) :=
  h.map (fun c => c.baseChange f)

/-- Collapse a finite original comparison chain and extend its actual framed comparison. -/
theorem ChainEquivalent.baseChange (h : ChainEquivalent X Y) (f : A ⟶ B) :
    ChainEquivalent (X.baseChange f) (Y.baseChange f) := by
  obtain ⟨c⟩ := h.directlyComparable
  exact chainEquivalent_of_comparison (c.baseChange f)

namespace ComparisonClass

/-- Descend actual representative extension through the exact original framed comparison relation. -/
def baseChange (q : ComparisonClass Φ A) (f : A ⟶ B) : ComparisonClass Φ B :=
  lift (fun X => comparisonClassOf (X.baseChange f))
    (fun c => comparisonClassOf_eq_of_comparison (c.baseChange f)) q

@[simp]
theorem baseChange_comparisonClassOf (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (comparisonClassOf X).baseChange f = comparisonClassOf (X.baseChange f) := rfl

/-- The descended residue map is extended by the actual induced quotient scalar map. -/
@[simp]
theorem residueMap_baseChange (q : ComparisonClass Φ A) (f : A ⟶ B) :
    (q.baseChange f).residueMap = (Nilp.reducedScalarMap 𝒪[K] f).comp q.residueMap := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

/-- Forgetting framing commutes with actual extension of the height-certified target class. -/
@[simp]
theorem targetClass_baseChange (q : ComparisonClass Φ A) (f : A ⟶ B) :
    (q.baseChange f).targetClass = q.targetClass.baseChangeAlong (Nilp.scalarMap 𝒪[K] f) := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

/-- The descended reduced target class follows the same canonical quotient/base-change square. -/
theorem reducedTargetClass_baseChange (q : ComparisonClass Φ A) (f : A ⟶ B) :
    (q.baseChange f).reducedTargetClass =
      q.reducedTargetClass.baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f) := by
  rw [reducedTargetClass, targetClass_baseChange]
  exact SpecialAtlas.HeightSquaredAtlas.IsoClass.reduction_baseChangeAlong q.targetClass f

/-- The extended chosen representative compares by actual framed maps with the new chosen representative. -/
def baseChangeRepresentativeComparison (q : ComparisonClass Φ A) (f : A ⟶ B) :
    Comparison (q.representative.baseChange f) (q.baseChange f).representative :=
  comparisonToRepresentative (q.baseChange f) (q.representative.baseChange f)
    (congrArg (fun z : ComparisonClass Φ A => z.baseChange f) (comparisonClassOf_representative q))

/-- The reverse comparison retains the inverse of the same actual framed formal maps. -/
def baseChangeFromRepresentativeComparison (q : ComparisonClass Φ A) (f : A ⟶ B) :
    Comparison (q.baseChange f).representative (q.representative.baseChange f) :=
  (q.baseChangeRepresentativeComparison f).symm

end ComparisonClass

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
