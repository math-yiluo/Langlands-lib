import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviOrbitMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSplitCenterIndependenceProof

/-! # The split center at the full standard semistandard index -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

set_option hygiene false in
local notation "pG" => standardIndex hG hi hν Finset.univ

/-- At the full standard index, every model's split-center point image
maps to the ambient split center under the full-Levi identification. -/
def FullLeviSplitCenterStatement : Prop :=
  ∀ (m : LeviModel pG)
    {A B : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ m.scheme) (s : B.toGrp ⟶ G)
    (_ : IsSplitComponent a) (_ : IsSplitComponent s) (hM : levi pG = ⊤),
    (m.splitCenter a).map (fullLeviGroupEquiv (levi pG) hM).symm.toMonoidHom =
      (rationalPoints.map s).range

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Compare with the factored ambient split component on the standard model. -/
theorem fullLeviSplitCenter_map :
    FullLeviSplitCenterStatement hG hi hν := by
  intro m A B a s ha hs hM
  have hcenter : m.splitCenter a =
      rationalLeviSplitCenter Finset.univ (rationalFullLeviSplitComponent hG hi hν s) :=
    splitCenterChoiceIndependence pG m (standardLeviModel hG hi hν Finset.univ) A B a _
      ha (isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs)
  let e := fullLeviGroupEquiv (levi pG) hM
  have he : e.symm.toMonoidHom = (rationalFullLeviLiteralPointEquiv hG hi hν).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change e.symm x = rationalFullLeviLiteralPointEquiv hG hi hν x
    calc
      e.symm x = (x : rationalPoints G) :=
        (coe_fullLeviGroupEquiv (levi pG) hM (e.symm x)).symm.trans
          (congrArg Subtype.val (e.apply_symm_apply x))
      _ = rationalFullLeviLiteralPointEquiv hG hi hν x :=
        (rationalFullLeviLiteralPointEquiv_apply hG hi hν x).symm
  rw [hcenter, show (fullLeviGroupEquiv (levi pG) hM).symm.toMonoidHom = _ from he]
  exact map_rationalFullLeviSplitCenter hG hi hν s

end Langlands.HarishChandraSchwartz.RationalSemistandard
