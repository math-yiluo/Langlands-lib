import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Standard parabolic witnesses for discrete-series embeddings -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For the existence assertion in Renard VII.2.6, an irreducible smooth
representation embeds into an induction of a discrete-series representation
from a rational parabolic if and only if it does so from the parabolic and
Levi at some index of a fixed standard family. -/
def DiscreteSeriesEmbeddingStandardReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T),
      IsMaximalSplitTorus i → IsGenericCocharacter i ν →
      ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)), π.IsIrreducible →
        ((∃ (P M U : GroupScheme (Spec (CommRingCat.of k)))
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
                  Function.Injective f) ↔
          ∃ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν ∧
            ∃ (P M U : GroupScheme (Spec (CommRingCat.of k)))
              (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
              (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
              (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
              (hmul : IsIso (subgroupMultiplication l r)),
              SubgroupFunctor.range p = standardParabolic i ν J ∧
              SubgroupFunctor.range (l ≫ p) = standardLevi i ν J ∧
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
