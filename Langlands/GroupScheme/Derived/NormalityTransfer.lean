import Langlands.GroupScheme.Derived.EpiProductDetection
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.SubgroupRangeTransport

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- Every point normalizes a normal subgroup functor, after every refinement. -/
theorem normalizer_eq_top_of_isNormal {S : Scheme.{u}} {G : GroupScheme S}
    {F : SubgroupFunctor G} (hF : F.IsNormal) : F.normalizer = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · intro _
    exact Subgroup.mem_top _
  · intro _ V a x hx
    refine ⟨hF V (a ≫ g) x (Subgroup.mem_top _) hx, ?_⟩
    simpa only [inv_inv] using hF V (a ≫ g)⁻¹ x (Subgroup.mem_top _) hx

/-- For a normal subgroup functor, normalizer points are all ambient points. -/
def normalizerPointsEquivOfIsNormal {S : Scheme.{u}} {G : GroupScheme S}
    {F : SubgroupFunctor G} (hF : F.IsNormal) (T : Over S) :
    F.normalizer.carrier T ≃* (T ⟶ G.X) :=
  (MulEquiv.subgroupCongr
    (congrArg (fun K : SubgroupFunctor G => K.carrier T)
      (normalizer_eq_top_of_isNormal hF))).trans Subgroup.topEquiv

@[simp] theorem normalizerPointsEquivOfIsNormal_apply {S : Scheme.{u}} {G : GroupScheme S}
    {F : SubgroupFunctor G} (hF : F.IsNormal) (T : Over S) (x : F.normalizer.carrier T) :
    normalizerPointsEquivOfIsNormal hF T x = (x : T ⟶ G.X) :=
  rfl

/-- A full normalizer makes a subgroup functor normal. -/
theorem isNormal_of_normalizer_eq_top {S : Scheme.{u}} {G : GroupScheme S}
    {F : SubgroupFunctor G} (hF : F.normalizer = ⊤) : F.IsNormal := by
  have h := F.isNormalizedBy_normalizer
  rwa [hF] at h

/-- Central generation transfers normality of closed subgroups to the ambient group. -/
theorem IsNormal.range_comp_of_isCentral_of_epi_subgroupProductMap
    {k : Type u} [Field k] {G Z D H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] (i : Z ⟶ G) (d : D ⟶ G)
    (hi : IsCentral i) (hd : IsClosedSubgroup d) [Epi (subgroupProductMap i d)]
    {j : H ⟶ D} (hj : IsClosedSubgroup j) (hN : (range j).IsNormal) :
    (range (j ≫ d)).IsNormal := by
  have hclosed : IsClosedSubgroup (j ≫ d) := hj.comp hd
  apply isNormal_of_normalizer_eq_top
  apply eq_top_of_hasClosedRepresentative_of_epi_subgroupProductMap
    (hasClosedRepresentative_normalizer_centralizer_range (j ≫ d) hclosed).1 i d
  · intro T x hx
    apply (range (j ≫ d)).centralizer_le_normalizer T
    obtain ⟨z, rfl⟩ := mem_range.mp hx
    intro V a y _
    exact hi T z V a y
  · intro T x hx
    obtain ⟨t, rfl⟩ := mem_range.mp hx
    have ht := ((normalizerPointsEquivOfIsNormal hN T).symm t).2
    have heq : ((normalizerPointsEquivOfIsNormal hN T).symm t : T ⟶ D.X) = t :=
      (normalizerPointsEquivOfIsNormal hN T).apply_symm_apply t
    apply normalizer_range_le_comap j d T
    rwa [heq] at ht

end SubgroupFunctor

/-- Triviality of the unipotent radical descends to a closed factor of a central product. -/
theorem HasTrivialUnipotentRadical.of_isCentral_of_epi_subgroupProductMap
    {k : Type u} [Field k] {G Z D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] (i : Z ⟶ G) (d : D ⟶ G)
    (hi : IsCentral i) (hd : IsClosedSubgroup d) [Epi (subgroupProductMap i d)]
    (hG : HasTrivialUnipotentRadical G) : HasTrivialUnipotentRadical D := by
  intro H j hj hs hc hu hn
  have hn' := SubgroupFunctor.IsNormal.range_comp_of_isCentral_of_epi_subgroupProductMap
    i d hi hd hj hn
  have hclosed := hj.comp hd
  have htrivial := hG H (j ≫ d) hclosed hs hc hu hn'
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  exact (SubgroupFunctor.range_comp_eq_bot_iff j d).mp htrivial

end Langlands.GroupScheme
