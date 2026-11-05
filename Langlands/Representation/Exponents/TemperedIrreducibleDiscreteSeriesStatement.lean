import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Irreducible tempered representations as subrepresentations of induced discrete series

Renard 2026, VII.2.6, Theorem, first assertion (printed p.231/PDF p.237): an
irreducible smooth representation is tempered if and only if it is a subrepresentation
of the normalized parabolic induction of an irreducible representation of a Levi
subgroup that is square-integrable modulo the center. The uniqueness assertion is the
separate module `TemperedIrreducibleDiscreteSeriesUniquenessStatement`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.6, Theorem, existence: an irreducible smooth representation `π` of
`G(F)` is normalized-exponent tempered if and only if, for some actual rational
parabolic with rational Levi `M` and matching radical, some irreducible smooth
representation `σ` of `M(F)` that is square-integrable modulo the center of `M(F)` for
every Haar measure admits an injective intertwiner from `π` into the normalized
induction of `σ`. -/
def TemperedIrreducibleDiscreteSeriesStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)), π.IsIrreducible →
        (IsNormalizedExponentTempered hG π ↔
          ∃ (P M U : GroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
            (hmul : IsIso (subgroupMultiplication l r)),
            haveI := hl.isConnectedReductive.isAffineHom
            letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
            haveI : LocallyCompactSpace (rationalPoints M) :=
              leviPoints_locallyCompactSpace p l hp hl
            haveI : NonarchimedeanGroup (rationalPoints M) :=
              leviPoints_nonarchimedeanGroup p l hp hl
            ∃ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
              σ.IsIrreducible ∧
                (∀ [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
                  [BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
                  (haar : MeasureTheory.Measure
                    (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
                  [haar.IsHaarMeasure],
                  IsSquareIntegrableModCenter σ.representation haar) ∧
                ∃ f : π.representation.IntertwiningMap
                    ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation,
                  Function.Injective f)

end Langlands.Aubert.General.RepresentedParabolic
