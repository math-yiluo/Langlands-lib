import Langlands.GroupScheme.SplitExistence.Reductive
import Langlands.GroupScheme.SplitExistence.RootDatumOf
import Langlands.GroupScheme.SplitExistence.Maximal
import Langlands.GroupScheme.Reductive.SplitClassificationStatement

/-! # The split group attached to Chevalley data

Every Chevalley group `G` built from Chevalley data for `(P, b)` is a connected reductive group
over `k`, the torus `D(X) → G` is a split maximal torus, and its root datum `chevDatum k P` is
isomorphic to `P`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]

/-- **The Chevalley group is connected reductive.** -/
theorem ChevGroup.isConnectedReductive [Finite J] [P.IsReduced] (G : D.ChevGroup k) :
    IsConnectedReductive G.H where
  smooth := G.smooth
  isAffineHom := G.affine
  connectedSpace := G.connected
  hasTrivialGeometricUnipotentRadical := G.hasTrivialUnipotentRadical

variable (k) in
/-- **Existence from Chevalley data.** Chevalley data for a reduced root datum `P` on a lattice
give a connected reductive group over `k` with a split maximal torus whose root datum is
isomorphic to `P`. -/
theorem exists_split_of_chevalleyData [Finite J] [Module.Finite ℤ X] [P.IsReduced]
    (D : ChevalleyData P b) :
    ∃ (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp ∧ IsMaximalTorus i ∧
        haveI := hG.isAffineHom
        ∃ Q : RootDatum J (characterLattice T) (cocharacterLattice T),
          IsRootDatumOf i Q ∧ Nonempty (RootPairing.Equiv P Q) := by
  have := isTorsionFree_weight P
  obtain ⟨G⟩ := D.nonempty_chevGroup k
  have : IsAffineHom G.H.X.hom := G.affine
  have : IsAffine G.H.X.left := isAffine_of_isAffineHom G.H.X.hom
  have : Smooth G.H.X.hom := G.smooth
  exact ⟨G.H, G.isConnectedReductive, Tk k, G.t, isSplitTorus_Tk k P, G.isMaximalTorus,
    chevDatum k P, G.isRootDatumOf, ⟨chevDatumEquiv k P⟩⟩

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
