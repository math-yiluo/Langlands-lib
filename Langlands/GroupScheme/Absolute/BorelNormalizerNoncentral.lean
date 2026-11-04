import Langlands.GroupScheme.Absolute.BorelNormalizerCentralizer
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionConnected
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # The noncentral branch with a canonical centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {B G : GroupScheme (Spec (CommRingCat.of k))}

/-- A point normalizing a Borel and centralizing a noncentral cocharacter in
that Borel belongs to the Borel, conditional on the exact intersection statement
and the smaller-group induction hypothesis. The centralizer is constructed. -/
theorem mem_borelRange_of_noncentral_cocharacter
    (hIntersection : CentralizerBorelIntersectionStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (hnotcentral : ¬ IsCentral χ)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)))
    (hxχ : x ∈ (Dynamic.centralizer χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    x ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let M := Dynamic.Affine.centralizerScheme χ
  let j : M ⟶ G := Dynamic.Affine.centralizerHom χ
  have hj : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hrep : (Dynamic.centralizer χ).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hsm : Smooth M.X.hom := (dynamicSmooth k G χ M j).2.1 hrep
  have hconn : ConnectedSpace M.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G χ hrep
  have hc : IsBorelSubgroup (subgroupIntersectionFst j b) :=
    hb.centralizer_intersection_isBorel_of_statement
      hIntersection χ hχ j hj hrep hsm hconn
  exact mem_borelRange_of_proper_cocharacterCentralizer ih b χ j hj hrep
    (not_isIso_dynamicCentralizer_of_not_isCentral χ j hrep hnotcentral) hc hx hxχ

/-- The actual commutator-kernel specialization, with no supplied representative
or geometric premise on its centralizer or its intersection with the Borel. -/
theorem mem_borelRange_of_noncentral_commutatorKernel_of_intersectionStatement
    (hIntersection : CentralizerBorelIntersectionStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hi : SubgroupFunctor.range i ≤ SubgroupFunctor.range b)
    (n : normalizerPoints i) (ν : cocharacterLattice T)
    (hzero : ν ≫ torusCommutatorEnd i n = 0)
    (hν : ¬ IsCentral (CommGroupScheme.groupHom ν ≫ i))
    (hn : n.val ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    n.val ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  mem_borelRange_of_noncentral_cocharacter hIntersection ih b hb
    (CommGroupScheme.groupHom ν ≫ i)
    ((SubgroupFunctor.range_comp_le _ i).trans hi) hν hn
    ((normalizerPoint_mem_dynamicCentralizer_iff_commutator_eq_zero i n ν).mpr hzero)

/-- An actual Borel point mapping to the given normalizing point in the
noncentral commutator-kernel branch. -/
def borelPointOfNoncentralKernel
    (hIntersection : CentralizerBorelIntersectionStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hi : SubgroupFunctor.range i ≤ SubgroupFunctor.range b)
    (n : normalizerPoints i) (ν : cocharacterLattice T)
    (hzero : ν ≫ torusCommutatorEnd i n = 0)
    (hν : ¬ IsCentral (CommGroupScheme.groupHom ν ≫ i))
    (hn : n.val ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    {p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X //
      p ≫ b.hom.hom = n.val} := by
  let h := SubgroupFunctor.mem_range.mp
    (mem_borelRange_of_noncentral_commutatorKernel_of_intersectionStatement
      hIntersection ih b hb i hi n ν hzero hν hn)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.GroupScheme
