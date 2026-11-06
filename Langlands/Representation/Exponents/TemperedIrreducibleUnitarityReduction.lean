import Langlands.Representation.Exponents.ArbitraryParabolicUnitarity
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement

/-! # A conditional form construction for the VII.2.6 corollary

This isolates the remaining geometric premises without changing either exact
VII.2.6 statement. In particular, it does not prove ambient unimodularity or
the modular-character identity for arbitrary represented parabolics.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- From the exact discrete-series embedding assertion, compactness, and the
displayed modular inputs, construct a form on the original tempered carrier.
The explicit standard-cocharacter premise is retained by the existing
ambient-unimodularity statement. -/
def temperedIrreducibleUnimodularForm
    (hDiscrete : TemperedIrreducibleDiscreteSeriesStatement.{u, v})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hCompact : ArbitraryParabolicQuotientCompactStatement.{u})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (_hδ : ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (_hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)),
        letI : LocallyCompactSpace (pointImage p) :=
          (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
        ∀ q : pointImage p, Measure.modularCharacter q =
          (HaarModulus.closedRestrictCharacter (pointImage (r ≫ p))
            (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
            (pointImage p)
            (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).le_normalizer
            q : ℝ≥0))
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      π.IsIrreducible → IsNormalizedExponentTempered hG π →
        InvariantPositiveForm π.representation := by
  haveI := hG.isAffineHom
  letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ hδ π hirr htemp
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  haveI : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  apply Classical.choice
  obtain ⟨P, M, U, p, l, r, hp, hl, hr, hmul, σ, hσirr, hσsq, f, hf⟩ :=
    (hDiscrete k G hG π hirr).mp htemp
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  have : LocallyCompactSpace (rationalPoints M) :=
    leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  let bσ := rationalSquareIntegrableUnimodularForm M hl.isConnectedReductive
    (hUnimod k M hl.isConnectedReductive hStandard) σ hσirr hσsq
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    hCompact k G hG P p hp
  let bind := leviInductionUnimodularForm p l r hp hr hl hmul
    (hUnimod k G hG hStandard) (hδ P M U p l r hp hr hl hmul) σ bσ
  exact ⟨bind.comap f hf⟩

end Langlands.Aubert.General.RepresentedParabolic
