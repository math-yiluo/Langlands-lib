import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.GroupScheme.Rational.Characters
import Langlands.Representation.Exponents.Central
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Mathlib.NumberTheory.LocalField.Basic

/-! # Strict normalized Jacquet exponents on actual rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Evaluate the actual character underlying a simple-root label on an actual
point of the specified torus. -/
def simpleRootPointValue (α : SimpleRoot i ν) :
    RationalPoint k T.X →* kˣ :=
  rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm α.val)

variable [ValuativeRel k]

/-- The closed negative chamber with its central valuation directions removed:
every simple-root value has valuation at most one and some has valuation below one. -/
def IsNoncentralNegativeTorusPoint (t : RationalPoint k T.X) : Prop :=
  (∀ α : SimpleRoot i ν,
    ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) ≤ 1) ∧
  ∃ α : SimpleRoot i ν,
    ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1

variable [TopologicalSpace k]

local instance rationalSquareIntegrabilityStatementPointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Strict bounds for the actual normalized standard Jacquet modules. Exponents
are characters of the full center of the actual Levi; they are tested on its
points coming from negative, noncentral valuation directions in the given split torus. -/
def HasStrictNormalizedJacquetExponents
    (h : ∀ J : Finset (SimpleRoot i ν),
      IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (hU : ∀ J : Finset (SimpleRoot i ν),
      IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
    (A : SmoothRep.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X)) : Prop :=
  ∀ (J : Finset (SimpleRoot i ν)) (χ : Subgroup.center (levi i ν J) →* ℂˣ),
    IsCentralExponent ((jacquetFunctor (h J) (hU J)).obj A).representation χ →
    ∀ (t : RationalPoint k T.X) (z : Subgroup.center (levi i ν J)),
      ((z : levi i ν J) : RationalPoint k G.X) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t →
      ‖(χ z : ℂ)‖ < 1

/-- Sufficiency of the strict normalized Jacquet exponent condition for square
integrability modulo the full actual center. This is a separate analytic proof
obligation, at general connected-reductive rational-point scope. -/
def RationalStrictJacquetSquareIntegrabilityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hU : ∀ J : Finset (SimpleRoot i ν),
        IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
      (A : SmoothRep.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X)),
      A.IsAdmissible →
      Nonempty (UnitaryCentralCharacter A.representation) →
      HasStrictNormalizedJacquetExponents i ν
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) hU A →
      ∀ [MeasurableSpace
          (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X))]
        [BorelSpace
          (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X))]
        (measure : MeasureTheory.Measure
          (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X)))
        [MeasureTheory.Measure.IsHaarMeasure measure],
        IsSquareIntegrableModCenter A.representation measure

end Langlands.Aubert.General.RationalPointFamily
