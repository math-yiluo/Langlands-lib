import Langlands.GroupScheme.Absolute.RankOneSolvableReduction
import Langlands.GroupScheme.Absolute.RankOneCentralizerReduction
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionConnected
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Lie.FieldExtension

/-! # Algebraic-closure reduction for opposite Lie-weight exclusion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The Borel case of opposite Lie-weight exclusion over algebraically closed
fields. This definition records a proof obligation, not its solution. -/
def RankOneAlgClosedBorelExclusionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsSplitTorus T.toGrp → IsMaximalTorus j →
    haveI := hG.isAffineHom
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
      (t : T.toGrp ⟶ B), IsBorelSubgroup b → t ≫ b = j →
      ∀ α ∈ roots j,
        ¬ (Lie.MeetsWeightSpace j b α ∧ Lie.MeetsWeightSpace j b (-α))

/-- Solvability persists upon passage to the chosen algebraic closure.
The original solvability hypothesis already supplies its rational-point group. -/
theorem IsSolvableGroupScheme.baseChange_toAlgebraicClosure
    {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
    (hH : IsSolvableGroupScheme H) :
    IsSolvableGroupScheme ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H) :=
  (isSolvableGroupScheme_iff_isSolvable_points _).mpr hH

set_option maxHeartbeats 800000 in
/-- Forward maximal-torus preservation and the algebraically closed Borel
case imply the exact obstruction over every field. Both inputs remain explicit. -/
theorem rankOneSolvableObstruction_of_algClosedBorel
    (hmax : MaximalTorusBaseChangeForwardStatement.{u})
    (hBorel : RankOneAlgClosedBorelExclusionStatement.{u}) :
    RankOneSolvableObstructionStatement.{u} := by
  intro k _ G hG T j hT hj
  have := hG.isAffineHom
  have := hG.smooth
  intro H i f hi hsmooth hconnected hsolvable hf α hα
  have := hsmooth
  have := hconnected
  have : IsAffineHom H.X.hom := hi.isAffineHom
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let jc : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map j
  let Hc := (GroupScheme.baseChange b).obj H
  let ic : Hc ⟶ Gc := (GroupScheme.baseChange b).map i
  let fc : Tc.toGrp ⟶ Hc := (GroupScheme.baseChange b).map f
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have := hGc.smooth
  have hTc : IsSplitTorus Tc.toGrp := hT.baseChange b
  have hjc : IsMaximalTorus jc := hmax k (AlgebraicClosure k) G T j hj
  have hic : IsClosedSubgroup ic := hi.baseChange b
  have hHcs : Smooth Hc.X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have hHcc : ConnectedSpace Hc.X.left :=
    connectedSpace_baseChange_of_smooth_affine H b
  have hHcsol : IsSolvableGroupScheme Hc := hsolvable.baseChange_toAlgebraicClosure
  have hfc : fc ≫ ic = jc := by
    change (GroupScheme.baseChange b).map f ≫ (GroupScheme.baseChange b).map i =
      (GroupScheme.baseChange b).map j
    rw [← Functor.map_comp, hf]
  let αc := characterLattice.baseChange b T α
  have hαc : αc ∈ roots jc :=
    (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT j α).mpr hα
  have hexclude := not_meets_oppositeWeightSpaces_of_borel jc
    (hBorel (AlgebraicClosure k) Gc hGc Tc jc hTc hjc)
    Hc ic fc hic hHcs hHcc hHcsol hfc αc hαc
  rintro ⟨hpos, hneg⟩
  apply hexclude
  refine ⟨weightSpace_lieImage_baseChange (K := AlgebraicClosure k) j α i hpos, ?_⟩
  have hnegc : Lie.MeetsWeightSpace jc ic (characterLattice.baseChange b T (-α)) :=
    weightSpace_lieImage_baseChange (K := AlgebraicClosure k) j (-α) i hneg
  simpa only [map_neg] using hnegc

/-- The three geometric statements imply the algebraically closed Borel
case, using the actual centralizer intersections supplied by the published adapter.
All three statements remain explicit premises. -/
theorem rankOneAlgClosedBorelExclusion_of_geometricStatements
    (hrank : RankOneBorelDynamicStatement.{u})
    (hcent : DynamicCentralizerReductiveStatement.{u})
    (hinter : CentralizerBorelIntersectionStatement.{u}) :
    RankOneAlgClosedBorelExclusionStatement.{u} := by
  intro k _ _ G hG T j hT hj B b t hb ht
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply not_meets_oppositeWeightSpaces_of_borel_centralizers
    hrank hcent G hG T j hT hj B b t hb ht
  intro ζ
  let χ := CommGroupScheme.groupHom ζ ≫ j
  let m := Dynamic.Affine.centralizerHom χ
  have hm := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hmc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hM := hcent k G hG χ _ m hmc hm
  have hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b := by
    change SubgroupFunctor.range (CommGroupScheme.groupHom ζ ≫ j) ≤ _
    rw [← ht, ← Category.assoc]
    intro V x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y ≫ (CommGroupScheme.groupHom ζ ≫ t).hom.hom, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy
  exact hb.centralizer_intersection_isBorel_of_statement hinter χ hχ m hmc hm
    hM.smooth hM.connectedSpace

/-- The four still-required geometric statements imply the exact arbitrary-field
obstruction. This conditional assembly proves none of its premises. -/
theorem rankOneSolvableObstruction_of_geometricStatements
    (hrank : RankOneBorelDynamicStatement.{u})
    (hcent : DynamicCentralizerReductiveStatement.{u})
    (hinter : CentralizerBorelIntersectionStatement.{u})
    (hmax : MaximalTorusBaseChangeForwardStatement.{u}) :
    RankOneSolvableObstructionStatement.{u} :=
  rankOneSolvableObstruction_of_algClosedBorel hmax
    (rankOneAlgClosedBorelExclusion_of_geometricStatements hrank hcent hinter)

end Langlands.GroupScheme
