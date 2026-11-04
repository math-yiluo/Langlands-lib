import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.CompactCoefficient.AmbientProjector

/-! # Detection through the actual rational points of a standard Levi -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands

open GroupScheme Aubert.General.RationalPointFamily

universe u uV

/-- An actual irreducible normalized Jacquet subquotient detects fixed vectors
after its intrinsic Levi restriction has compact coefficients. -/
def RationalLeviJacquetFixedVectorDetectionStatement : Prop :=
  CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, uV} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν)),
      let L := Standard.leviScheme i ν (rootSet i ν I)
      ∀ (hL : IsConnectedReductive L),
        haveI := hL.isAffineHom
        haveI : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
        letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
        letI : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
        ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
          [T2Space (rationalPoints G)]
          [LocallyCompactSpace (rationalPoints L)] [NonarchimedeanGroup (rationalPoints L)]
          [T2Space (rationalPoints L)]
          (Nbar : Subgroup (rationalPoints G))
          (hN : IsClosed (unipotent i ν I : Set (rationalPoints G)))
          (hMN : levi i ν I ≤ Subgroup.normalizer (unipotent i ν I)),
          IsClosed (levi i ν I : Set (rationalPoints G)) →
          (∀ s : Finset (unipotent i ν I), ∃ J : OpenSubgroup (unipotent i ν I),
            IsCompact (J : Set (unipotent i ν I)) ∧ ∀ n ∈ s, n ∈ J) →
          ∀ (K : OpenSubgroup (rationalPoints G)) (K0 : Subgroup (rationalPoints G)),
            IsCompact (K : Set (rationalPoints G)) →
            K0 ≤ Subgroup.normalizer K.toSubgroup →
            (∀ x : rationalPoints G, ∃ m ∈ levi i ν I, ∃ n ∈ unipotent i ν I,
              ∃ k ∈ K0, x = m * n * k) →
            ∀ (g : rationalPoints G),
              Jacquet.IsIwahoriContraction K (unipotent i ν I) (levi i ν I) Nbar g →
              ∀ (A D : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
                FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) →
                (∀ S : Subrepresentation A.representation,
                  fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) →
                SmoothRep.IsSubquotient D A →
                ∀ E : SmoothRep.{0, u, uV} ℂ (levi i ν I),
                  E.IsIrreducible →
                  SmoothRep.IsSubquotient E
                    ((Aubert.General.normalizedJacquetFunctor
                      (unipotent i ν I) (levi i ν I) hN hMN).obj D) →
                  HasCompactSmoothDualCoefficients
                    (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel L)
                      (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) E)).representation →
                  ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0

end Langlands
