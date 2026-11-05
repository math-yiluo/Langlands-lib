import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Plancherel.SplitTorusRealPart
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Reductive.Basic

/-! # Casselman's criterion for actual rational parabolics

Renard 2026, VII.1.2 (printed pp.221–224/PDF pp.227–230), for an admissible
representation with a unitary central character. The cone is the strictly positive
cone of restricted simple roots that the source proof establishes, and the real part
is the explicitly normalized `q^(-s)` parameter; both choices and their comparison
with the printed statement are documented in the paired Markdown.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.2: an admissible representation with a unitary central character is
square-integrable modulo the center for a Haar measure on `G(F) ⧸ Z(G(F))` if and
only if, for every actual rational parabolic with Levi, matching radical and split
component, every compatible root presentation and every normalized Jacquet exponent,
the normalized real part of the exponent lies in the strictly positive root cone. -/
def ArbitraryParabolicCasselmanCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsAdmissible → Nonempty (UnitaryCentralCharacter π.representation) →
        (IsSquareIntegrableModCenter π.representation haar ↔
          ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
            (pres : ParabolicRootPresentation p l a) (χ : rationalPoints A.toGrp →* ℂˣ),
            IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
              Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
                pres.positiveCone)

end Langlands.Aubert.General.RepresentedParabolic
