import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.GroupScheme.Reductive.Basic

/-! # Square-integrable representations are normalized-exponent tempered

Renard 2026, VII.2.1, Remark 2 (printed p.227/PDF p.233): by Casselman's criterion
VII.1.2, a representation that is square-integrable modulo the center is tempered.
The published square-integrability predicate already contains admissibility and a
unitary central character; the paired Markdown explains why the source's
irreducibility hypothesis is omitted.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.1, Remark 2: a representation of `G(F)` that is square-integrable
modulo the center for a Haar measure on `G(F) ⧸ Z(G(F))` satisfies the
normalized-exponent temperedness condition for every actual rational parabolic. -/
def SquareIntegrableNormalizedTemperedStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      [BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G))]
      (haar : MeasureTheory.Measure (rationalPoints G ⧸ Subgroup.center (rationalPoints G)))
      [haar.IsHaarMeasure] (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsSquareIntegrableModCenter π.representation haar →
        IsNormalizedExponentTempered hG π

end Langlands.Aubert.General.RepresentedParabolic
