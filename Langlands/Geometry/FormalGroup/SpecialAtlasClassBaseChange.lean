import Langlands.Geometry.FormalGroup.HeightSquaredAtlasClasses
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChange

/-! # Coefficient extension of special and height-certified atlas classes -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extend a supplied actual division-order-linear formal comparison. -/
def baseChangeComparison {X Y : SpecialAtlas K D ι R} (f : Comparison X Y)
    (S : CommAlgCat.{v} R) : Comparison (X.baseChange S) (Y.baseChange S) :=
  f.baseChange S

/-- Existence of actual formal comparison is preserved by coefficient extension. -/
theorem equivalent_baseChange {X Y : SpecialAtlas K D ι R} (h : Equivalent X Y)
    (S : CommAlgCat.{v} R) : Equivalent (X.baseChange S) (Y.baseChange S) :=
  h.map (fun f => baseChangeComparison f S)

namespace IsoClass

/-- Coefficient extension descends through the actual formal comparison relation. -/
def baseChange (q : IsoClass (K := K) (D := D) (ι := ι) (R := R))
    (S : CommAlgCat.{v} R) : IsoClass (K := K) (D := D) (ι := ι) (R := S) :=
  Quotient.map (fun X => X.baseChange S) (fun _ _ h => equivalent_baseChange h S) q

@[simp]
theorem baseChange_classOf (X : SpecialAtlas K D ι R) (S : CommAlgCat.{v} R) :
    (classOf X).baseChange S = classOf (X.baseChange S) := rfl

end IsoClass

namespace HeightSquaredAtlas

variable {π : 𝒪[K]}

/-- Extend the actual atlas together with its own chart heights and base nilpotence. -/
def baseChange (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := S) π :=
  ⟨X.val.baseChange S, X.val.baseChange_height S X.property⟩

@[simp]
theorem val_baseChange
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) : (X.baseChange S).val = X.val.baseChange S := rfl

/-- Both extended inputs retain their certificates and the extended formal comparison. -/
theorem equivalent_baseChange
    {X Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π}
    (h : Equivalent X Y) (S : CommAlgCat.{v} R) :
    Equivalent (X.baseChange S) (Y.baseChange S) :=
  SpecialAtlas.equivalent_baseChange h S

namespace IsoClass

/-- Descend coefficient extension within the subtype carrying actual height d². -/
def baseChange (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) : IsoClass (K := K) (D := D) (ι := ι) (R := S) π :=
  Quotient.map (fun X => X.baseChange S) (fun _ _ h => equivalent_baseChange h S) q

@[simp]
theorem baseChange_classOf
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) : (classOf X).baseChange S = classOf (X.baseChange S) := rfl

/-- Forgetting the supplied height certificates commutes with coefficient extension. -/
@[simp]
theorem forgetHeight_baseChange
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π)
    (S : CommAlgCat.{v} R) :
    (q.baseChange S).forgetHeight = q.forgetHeight.baseChange S := by
  refine Quotient.inductionOn q ?_
  intro X
  rfl

end IsoClass

end HeightSquaredAtlas

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
