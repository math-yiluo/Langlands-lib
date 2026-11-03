import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel

/-! # Strict normalized exponents on actual uniformizer rays -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The literal strict exponent hypothesis applies to every noncentral
nonnegative uniformizer direction orthogonal to the selected Levi roots. -/
def RationalLatticeStrictExponentStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hU : ∀ J : Finset (SimpleRoot i ν),
        IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
      (A : SmoothRep.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X)),
      HasStrictNormalizedJacquetExponents i ν
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) hU A →
      ∀ (J : Finset (SimpleRoot i ν)) (x : cocharacterLattice T),
        (∀ β ∈ J, simpleRootPairing i ν β x = 0) →
        (∀ β, 0 ≤ simpleRootPairing i ν β x) →
        (∃ β, 0 < simpleRootPairing i ν β x) →
        ∃ z : Subgroup.center (levi i ν J),
          ((z : levi i ν J) : RationalPoint k G.X) = uniformizerPowers i (.ofAdd x) ∧
          ∀ χ : Subgroup.center (levi i ν J) →* ℂˣ,
            IsCentralExponent
              ((jacquetFunctor
                (isSemidirectDecomposition_of_standardCocharacterStatement
                  i ν hStandard hG hi hν J) (hU J)).obj A).representation χ →
            ‖(χ z : ℂ)‖ < 1

end Langlands.Aubert.General.RationalPointFamily
