import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # The proper-centralizer step of Borel normalizer induction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The exact Borel normalizer conclusion for one group over the ground field. -/
def BorelNormalizerProperty (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
    Subgroup.normalizer
        ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

/-- The local predicate adds no hypothesis to the exact published target. -/
theorem borelNormalizerStatement_iff :
    BorelNormalizerStatement.{u} ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (G : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
        BorelNormalizerProperty G :=
  Iff.rfl

/-- Strong Lie-dimension induction with exactly the local Borel normalizer
conclusion as its predicate. Smaller groups need not embed in the current group. -/
theorem borelNormalizer_lieDimension_induction
    (step : ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      (∀ (M : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left],
        Lie.dimension M < Lie.dimension G → BorelNormalizerProperty M) →
      BorelNormalizerProperty G)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    BorelNormalizerProperty G :=
  smoothConnectedAffineGroup_lieDimension_induction BorelNormalizerProperty step G

variable {B C M G : GroupScheme (Spec (CommRingCat.of k))}

/-- If the actual intersection inside a monic subgroup is Borel and that
subgroup satisfies the local normalizer theorem, a normalizing ambient point
lying in the subgroup already lies in the given ambient Borel. -/
theorem mem_borelRange_of_normalizes_intersection
    (hM : BorelNormalizerProperty M)
    (b : B ⟶ G) (j : M ⟶ G) [Mono j.hom.hom] (c : C ⟶ M)
    (hc : IsBorelSubgroup c)
    (hrange : SubgroupFunctor.range (c ≫ j) =
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range b)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)))
    (hxM : x ∈ (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    x ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hxM
  have hmN :=
    SubgroupFunctor.mem_pointNormalizer_of_range_comp_eq_inf c j
      (SubgroupFunctor.range b) hrange (by rwa [hm])
  rw [hM C c hc] at hmN
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hmN
  have hzc : x ∈ (SubgroupFunctor.range (c ≫ j)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, hm]
  rw [hrange] at hzc
  exact hzc.2

/-- The induction hypothesis applies to any proper smooth connected closed
subgroup whose actual intersection with the ambient Borel is Borel. -/
theorem mem_borelRange_of_proper_intersection
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth M.X.hom] [ConnectedSpace M.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hproper : ¬ IsIso j) (c : C ⟶ M) (hc : IsBorelSubgroup c)
    (hrange : SubgroupFunctor.range (c ≫ j) =
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range b)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)))
    (hxM : x ∈ (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    x ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom M.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact mem_borelRange_of_normalizes_intersection
    (ih M (Lie.dimension_lt_of_proper_closedSubgroup j hj hproper))
    b j c hc hrange hx hxM

/-- In particular, the canonical pullback intersection can be used directly. -/
theorem mem_borelRange_of_proper_subgroupIntersection
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth M.X.hom] [ConnectedSpace M.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hproper : ¬ IsIso j) (hc : IsBorelSubgroup (subgroupIntersectionFst j b))
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)))
    (hxM : x ∈ (SubgroupFunctor.range j).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    x ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  mem_borelRange_of_proper_intersection ih b j hj hproper
    (subgroupIntersectionFst j b) hc (range_subgroupIntersectionHom j b) hx hxM

/-- The proper represented cocharacter-centralizer branch. Smoothness of the
centralizer is discharged by the published dynamic smoothness theorem. -/
theorem mem_borelRange_of_proper_cocharacterCentralizer
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [ConnectedSpace M.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (b : B ⟶ G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j)
    (hproper : ¬ IsIso j) (hc : IsBorelSubgroup (subgroupIntersectionFst j b))
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)))
    (hxχ : x ∈ (Dynamic.centralizer χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    x ∈ (SubgroupFunctor.range b).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : Smooth M.X.hom := (dynamicSmooth k G χ M j).2.1 hrep
  apply mem_borelRange_of_proper_subgroupIntersection ih b j hj hproper hc hx
  rwa [hrep.2]

end Langlands.GroupScheme
