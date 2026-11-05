import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Actual absolute root subgroups are vector groups of dimension one -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a split maximal torus of a connected reductive group over an
algebraically closed field, each intrinsic root functor has an actual closed
representative which is a vector group of dimension one. -/
def AbsoluteRootVectorLineStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsSplitSubtorus t → IsMaximalTorus t →
      ∀ α ∈ relativeRoots t,
        ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
          (RelativeRoot.subgroup t α).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
            RelativeRoot.IsVectorGroupOfDimension U 1

end Langlands.GroupScheme
