import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedStatement
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Actual coroot comparison for derived split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, the coroot lattice of the actual derived
subgroup of a split-torus centralizer maps onto the span of a subset of simple
coroots of the ambient reductive group. All lattices and maps come from actual
compatible maximal tori. Semisimplicity of the supplied derived subgroup is an
explicit premise; no simple-connectedness assertion is made. -/
def SplitTorusCentralizerDerivedCorootComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
    IsSplitSubtorus a →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer a).IsRepresentedBy j →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M),
      IsDerivedSubgroup d → ∀ hD : IsSemisimple D,
        haveI := hG.isAffineHom
        haveI := hD.isConnectedReductive.isAffineHom
        ∃ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
          (i : T.toGrp ⟶ G) (t : S.toGrp ⟶ D) (φ : S ⟶ T),
          IsSplitTorus T.toGrp ∧ IsMaximalTorus i ∧
          IsSplitTorus S.toGrp ∧ IsMaximalTorus t ∧
          IsClosedSubgroup (CommGroupScheme.groupHom φ) ∧
          CommGroupScheme.groupHom φ ≫ i = t ≫ d ≫ j ∧
          ∃ (J K : Type u) (_ : Finite J) (_ : Finite K)
            (P : RootDatum J (characterLattice T) (cocharacterLattice T))
            (Q : RootDatum K (characterLattice S) (cocharacterLattice S)),
            IsRootDatumOf i P ∧ P.IsReduced ∧
            IsRootDatumOf t Q ∧ Q.IsReduced ∧
            ∃ (b : P.Base) (s : Set J), s ⊆ (b.support : Set J) ∧
              (Q.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
                Submodule.span ℤ (P.coroot '' s)

end Langlands.GroupScheme
