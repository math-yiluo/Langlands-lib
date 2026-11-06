import Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesStatement
import Langlands.Representation.Exponents.TemperedIrreducibleUnitarizableStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Aubert.General.NormalizedInductionUnitarity
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Representation.Unitary.Restriction

/-! # Unitarity adapters for actual rational parabolics

These constructions expose the geometric modular-character inputs to the
VII.2.6 corollary. They do not discharge those inputs.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section RationalPoints

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- Square-integrability modulo the full center gives a positive invariant form
on the original carrier once ambient unimodularity is supplied. -/
def rationalSquareIntegrableUnimodularForm :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (_hmod : ∀ g : rationalPoints G, Measure.modularCharacter g = 1)
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsIrreducible →
      (∀ [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
        [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
        (haar : Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
        [haar.IsHaarMeasure], IsSquareIntegrableModCenter π.representation haar) →
      InvariantPositiveForm π.representation := by
  haveI := hG.isAffineHom
  letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ hmod π hirr hsq
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  haveI : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  haveI : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  letI : MeasurableSpace (rationalPoints G) := borel _
  letI : BorelSpace (rationalPoints G) := ⟨rfl⟩
  letI : MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := borel _
  letI : BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := ⟨rfl⟩
  let quotientHaar : Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) :=
    MeasureTheory.Measure.haar
  haveI : quotientHaar.IsMulRightInvariant :=
    Haar.centralQuotient_isMulRightInvariant hmod quotientHaar
  exact Classical.choice
    (squareIntegrableUnimodularUnitarity (rationalPoints G)
      (compactOpenCofinal_of_nonarchimedean _) π π.representation quotientHaar hirr
      (hsq quotientHaar))

end RationalPoints

section Induction

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitarityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
  (hmul : IsIso (subgroupMultiplication l r))

/-- The published compact-quotient integral form on the actual induction from
`M(k)`, with its canonical Levi-point topology. -/
def leviInductionUnimodularForm
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hmod : ∀ g : rationalPoints G, Measure.modularCharacter g = 1)
    (hδ :
      letI : LocallyCompactSpace (pointImage p) :=
        (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
      ∀ q : pointImage p, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter (pointImage (r ≫ p))
        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
        (pointImage p)
        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).le_normalizer q :
          ℝ≥0))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (b : letI := leviPointTopology l hl; InvariantPositiveForm σ.representation) :
    letI := leviPointTopology l hl
    InvariantPositiveForm
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation := by
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  haveI : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  letI : MeasurableSpace (rationalPoints G) := borel _
  letI : BorelSpace (rationalPoints G) := ⟨rfl⟩
  letI : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  letI := leviPointTopology l hl
  exact compactQuotientNormalizedInductionForm
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (isClosed_pointImage p hp.isClosedSubgroup) hmod hδ
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)
    (b.comp (leviPointsEquiv p l hp hl).symm.toMonoidHom)

end Induction

end Langlands.Aubert.General.RepresentedParabolic
