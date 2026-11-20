import Langlands.GroupScheme.Rational.RealPointComponentsStatement
import Langlands.GroupScheme.Rational.RealPointComponentsFinite
import Langlands.GroupScheme.Rational.RealMaximalSplitTorusIdentity
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly

/-! # Assembly of the real components theorem from fixed coroot signs -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

open RealPointTopology

local instance (G : GroupScheme (Spec (CommRingCat.of ℝ))) :
    Group (RingPoint ℝ G.X ℝ) := G.ringPointGroup (CommAlgCat.of ℝ ℝ)

set_option linter.defProp false in
/-- The fixed simple coroot criterion and split-torus component coverage
give the two conclusions on real point spaces. -/
def realPointComponents_of_fixedSimpleCorootSigns
    (hcomponents : ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
      IsConnectedReductive G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : S.toGrp ⟶ G),
        IsMaximalSplitTorus i →
        ∀ g : RingPoint ℝ G.X ℝ, ∃ s : RingPoint ℝ S.X ℝ,
          ConnectedComponents.mk (α := RingPoint ℝ G.X ℝ) (s ≫ i.hom.hom) =
            ConnectedComponents.mk g)
    (hfixed : ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]
      (hG : IsSimplyConnected G),
      letI : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
      FixedSimpleCorootSignsInIdentity G) :
    RealPointComponentsStatement := by
  intro G _
  refine ⟨?_, finite_connectedComponents_of_isConnectedReductive G⟩
  intro hG
  let hred := hG.isSemisimple.isConnectedReductive
  let : IsAffineHom G.X.hom := hred.isAffineHom
  let : Smooth G.X.hom := hred.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨S, i, hi⟩ := exists_maximalSplitTorus G
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨1, Set.eq_univ_iff_forall.mpr ?_⟩
  intro g
  obtain ⟨s, hsg⟩ := hcomponents G hred S i hi g
  have hs := maximalSplitTorus_mem_connectedComponent_of_fixedSimpleCorootSigns
    G hG (hfixed G hG) i hi s
  have hs1 : ConnectedComponents.mk (α := RingPoint ℝ G.X ℝ) (s ≫ i.hom.hom) =
      ConnectedComponents.mk (1 : RingPoint ℝ G.X ℝ) := ConnectedComponents.coe_eq_coe'.mpr hs
  exact ConnectedComponents.coe_eq_coe'.mp (hsg.symm.trans hs1)

end Langlands.GroupScheme
