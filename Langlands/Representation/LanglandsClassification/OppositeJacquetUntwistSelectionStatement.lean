import Langlands.Representation.LanglandsClassification.OppositeJacquetUntwist
import Langlands.Representation.LanglandsClassification.LanglandsTriplet

/-! # Selecting a tempered untwist of an actual opposite Jacquet exponent

This internal proposition isolates the remaining exponent-selection obligation
in Langlands exhaustion. No existence theorem is asserted here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Internal selection obligation in the opposite-Jacquet proof of exhaustion.
It requires a genuine opposite exponent and its actual irreducible unitary
untwist, tempered on its original standard Levi, with its original real part
in the open chamber. No quotient map or classification assertion is assumed. -/
def OppositeJacquetUntwistSelectionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν),
      IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) →
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G), π.IsIrreducible →
        ∃ (x : OppositeStandardJacquetFamily.exponents i ν hG hi hν π)
          (W : OppositeStandardJacquetFamily.UnitaryUntwist i ν hG hi hν π x),
          (let S := StandardJacquetFamily.datum i ν hG hi hν x.1
           haveI := S.hl.isConnectedReductive.isAffineHom
           letI := leviPointTopology S.l S.hl
           haveI := leviPoints_locallyCompactSpace S.p S.l S.hp S.hl
           haveI := leviPoints_nonarchimedeanGroup S.p S.l S.hp S.hl
           IsNormalizedExponentTempered S.hl.isConnectedReductive W.untwist) ∧
          OppositeStandardJacquetFamily.realPart i ν hG hi hν π x ∈
            restrictedCorootChamber i ν x.1.val
              (Additive.ofMul (OppositeStandardJacquetFamily.component i ν hG hi hν x.1).g) D


end Langlands.Aubert.General.RepresentedParabolic
