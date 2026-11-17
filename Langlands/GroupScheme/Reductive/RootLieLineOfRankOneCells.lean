import Langlands.GroupScheme.Reductive.RootLieLineFromRootCell
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement
import Langlands.GroupScheme.Reductive.RootDatumStatement

/-! # Root Lie lines in proportional-root groups from supplied root cells -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootCellLie

/-- A supplied rank-one root cell trivializes the actual root weight space
indexed by a supplied root datum. -/
def lineEquivOfRankOneDatum
    (hcell : SplitRankOneRootCellStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hdep : haveI := hG.isAffineHom
      ∀ mu ∈ roots i, ∀ nu ∈ roots i, ¬ LinearIndependent ℤ ![mu, nu])
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    haveI := hG.isAffineHom
    k ≃ₗ[k] weightSpace i α := by
  apply Classical.choice
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have har : α ∈ Set.range P.root := hP.2.1.symm ▸ hα
  obtain ⟨r, rfl⟩ := har
  obtain ⟨xp, xm, hp, hm, hopen, _, _⟩ :=
    hcell k G hG T hT i hi J P hP hdep r
  exact ⟨lineEquiv hT i hα.1 xp xm hp hm hopen hα.2⟩

/-- Root-datum existence and the supplied rank-one root-cell statement give
a root Lie line when all roots are pairwise dependent. Both structural inputs
remain explicit. -/
def lineEquivOfRankOneCells
    (hdatum : RootDatumExistenceStatement.{u})
    (hcell : SplitRankOneRootCellStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ mu ∈ roots i, ∀ nu ∈ roots i, ¬ LinearIndependent ℤ ![mu, nu])
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    haveI := hG.isAffineHom
    k ≃ₗ[k] weightSpace i α := by
  apply Classical.choice
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨J, _, P, hP, _⟩ := hdatum k G hG T hT i hi
  exact ⟨lineEquivOfRankOneDatum hcell k G hG T hT i hi J P hP hdep α hα⟩

end Langlands.GroupScheme.RootCellLie
