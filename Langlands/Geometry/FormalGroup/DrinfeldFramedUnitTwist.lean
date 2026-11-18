import Langlands.Geometry.FormalGroup.DrinfeldFramedTargetTransport
import Langlands.Geometry.FormalGroup.SpecialAtlasUnitTwist
import Langlands.Geometry.FormalGroup.DrinfeldFramedClassFunctor

/-! # Actual integer-unit target conjugation of framed triples -/

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

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Conjugate the actual target action by an integer unit, with the specified actual inverse-unit framing. -/
def twistIntegerUnit (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) : DrinfeldFramedAtlas Φ A :=
  X.transportTarget (X.target.twistIntegerUnit u) (X.target.val.twistIntegerUnitIso u)

@[simp]
theorem twistIntegerUnit_residueMap (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) :
    (X.twistIntegerUnit u).residueMap = X.residueMap := rfl

@[simp]
theorem twistIntegerUnit_target (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) :
    (X.twistIntegerUnit u).target = X.target.twistIntegerUnit u := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole actual framing is postcomposed with the reduced actual inverse-unit target isomorphism. -/
theorem twistIntegerUnit_rho (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) :
    (X.twistIntegerUnit u).rho = X.rho.trans
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.target.val.twistIntegerUnitIso u).reduction) := by
  change ((BasicAtlas.OrderAction.QuasiIsogeny.refl _).trans X.rho).trans _ = _
  rw [BasicAtlas.OrderAction.QuasiIsogeny.refl_trans]

/-- The actual integral inverse-unit maps give an original framed comparison to the conjugated triple. -/
def twistIntegerUnitComparison (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) :
    Comparison X (X.twistIntegerUnit u) :=
  X.targetTransportComparison (X.target.twistIntegerUnit u) (X.target.val.twistIntegerUnitIso u)

/-- The exact original target unit-conjugation comparison is retained. -/
@[simp]
theorem twistIntegerUnitComparison_targetComparison (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) :
    (X.twistIntegerUnitComparison u).targetComparison = X.target.val.twistIntegerUnitComparison u := rfl

/-- The actual unit-conjugated triple has the SAME original framed comparison class. -/
theorem comparisonClassOf_twistIntegerUnit (X : DrinfeldFramedAtlas Φ A) (u : (IntegerRing K D)ˣ) :
    comparisonClassOf (X.twistIntegerUnit u) = comparisonClassOf X :=
  (comparisonClassOf_eq_of_comparison (X.twistIntegerUnitComparison u)).symm

/-- Actual integer-unit conjugation preserves original framed comparisons. -/
def Comparison.twistIntegerUnit {X Y : DrinfeldFramedAtlas Φ A} (c : Comparison X Y)
    (u : (IntegerRing K D)ˣ) : Comparison (X.twistIntegerUnit u) (Y.twistIntegerUnit u) :=
  (X.twistIntegerUnitComparison u).symm.trans (c.trans (Y.twistIntegerUnitComparison u))

namespace ComparisonClass

/-- Descend the actual unit-conjugation construction through the SAME original framed quotient. -/
def twistIntegerUnit (u : (IntegerRing K D)ˣ) : ComparisonClass Φ A → ComparisonClass Φ A :=
  lift (fun X => comparisonClassOf (X.twistIntegerUnit u))
    (fun c => comparisonClassOf_eq_of_comparison (c.twistIntegerUnit u))

@[simp]
theorem twistIntegerUnit_comparisonClassOf (u : (IntegerRing K D)ˣ) (X : DrinfeldFramedAtlas Φ A) :
    twistIntegerUnit u (comparisonClassOf X) = comparisonClassOf (X.twistIntegerUnit u) := rfl

/-- Integer-order units fix every actual original framed comparison class. -/
@[simp]
theorem twistIntegerUnit_eq (u : (IntegerRing K D)ˣ) (q : ComparisonClass Φ A) :
    twistIntegerUnit u q = q := by
  refine Quotient.inductionOn q ?_
  intro X
  exact comparisonClassOf_twistIntegerUnit X u

/-- Actual coefficient extension commutes with the descended actual unit-conjugation map. -/
theorem twistIntegerUnit_baseChange (u : (IntegerRing K D)ˣ) (q : ComparisonClass Φ A) (f : A ⟶ B) :
    (twistIntegerUnit u q).baseChange f = twistIntegerUnit u (q.baseChange f) := by
  simp only [twistIntegerUnit_eq]

end ComparisonClass

/-- The descended actual integer-unit conjugation is a natural map of the original framed Nilp functor. -/
def integerUnitTwistNatTrans (u : (IntegerRing K D)ˣ) :
    comparisonClassFunctor (R := R) Φ ⟶ comparisonClassFunctor Φ where
  app A := ↾(ComparisonClass.twistIntegerUnit u)
  naturality A B f := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (ComparisonClass.twistIntegerUnit_baseChange u q f).symm

/-- Every natural unit-conjugation map is the identity on the actual original framed Nilp functor. -/
theorem integerUnitTwistNatTrans_eq_id (u : (IntegerRing K D)ˣ) :
    integerUnitTwistNatTrans (R := R) (Φ := Φ) u = 𝟙 (comparisonClassFunctor Φ) := by
  apply NatTrans.ext
  funext A
  apply ConcreteCategory.hom_ext
  intro q
  exact ComparisonClass.twistIntegerUnit_eq u q

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
