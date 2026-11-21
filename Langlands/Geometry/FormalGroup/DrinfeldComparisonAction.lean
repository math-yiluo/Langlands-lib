import Langlands.Geometry.FormalGroup.DrinfeldActionComparison
import Langlands.Geometry.FormalGroup.DrinfeldFramedActionLaws

/-! # Drinfeld's group action on the classes of height-zero framed triples -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.ComparisonClass

open ValuativeRel CentralSimple ModuleLaw

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {π : 𝒪[K]} {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (f * j))
variable (c : Φ.val.MatrixCoordinates)
variable (g h : GL (Fin (reducedDegree K D)) K × Dˣ)

/-- Drinfeld's transformation descends through each actual framed comparison. -/
def act : ComparisonClass Φ A → ComparisonClass Φ A :=
  lift (fun X => comparisonClassOf (X.act g p hcard hFrob hRank c))
    (fun d => comparisonClassOf_eq_of_comparison (d.act g p hcard hFrob c hRank))

@[simp]
theorem act_comparisonClassOf (X : DrinfeldFramedAtlas Φ A) :
    act p hcard hFrob hRank c g (comparisonClassOf X) =
      comparisonClassOf (X.act g p hcard hFrob hRank c) := rfl

@[simp]
theorem act_one (q : ComparisonClass Φ A) : act p hcard hFrob hRank c 1 q = q := by
  refine Quotient.inductionOn q (fun X => ?_)
  exact congrArg comparisonClassOf (DrinfeldFramedAtlas.act_one X p hcard hFrob hRank c)

theorem act_mul (q : ComparisonClass Φ A) :
    act p hcard hFrob hRank c (g * h) q =
      act p hcard hFrob hRank c g (act p hcard hFrob hRank c h q) := by
  refine Quotient.inductionOn q (fun X => ?_)
  exact congrArg comparisonClassOf (DrinfeldFramedAtlas.act_mul X p hcard hFrob hRank c g h)

/-- The matrix and division groups act on the original comparison classes. -/
@[instance_reducible]
def groupAction : MulAction (GL (Fin (reducedDegree K D)) K × Dˣ) (ComparisonClass Φ A) where
  smul := act p hcard hFrob hRank c
  one_smul := act_one p hcard hFrob hRank c
  mul_smul := act_mul p hcard hFrob hRank c

/-- The residue map of the transformed class is shifted by the negative exponent. -/
theorem act_residueMap (q : ComparisonClass Φ A) :
    (act p hcard hFrob hRank c g q).residueMap =
      DrinfeldResidue.shift (DrinfeldAction.exponent K D g) q.residueMap := by
  refine Quotient.inductionOn q (fun X => ?_)
  rfl

/-- The class of the target transforms by inverse conjugation of its order action. -/
theorem act_targetClass (q : ComparisonClass Φ A) :
    (act p hcard hFrob hRank c g q).targetClass = q.targetClass.twistDivisionUnit g.2 := by
  refine Quotient.inductionOn q (fun X => ?_)
  rfl

/-- The same conjugation describes the class of the quotient-reduced target. -/
theorem act_reducedTargetClass (q : ComparisonClass Φ A) :
    (act p hcard hFrob hRank c g q).reducedTargetClass = q.reducedTargetClass.twistDivisionUnit g.2 := by
  refine Quotient.inductionOn q (fun X => ?_)
  exact congrArg SpecialAtlas.HeightSquaredAtlas.classOf (Subtype.ext (X.actionTarget_reduction g))

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas.ComparisonClass
