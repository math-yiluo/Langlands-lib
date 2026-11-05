import Langlands.GroupScheme.Absolute.BorelNormalizerTorus
import Langlands.GroupScheme.Absolute.BorelNormalizerNoncentral
import Langlands.GroupScheme.Absolute.BorelNormalizerSmoothSurjective
import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Absolute.PrescribedBorelQuotient
import Langlands.GroupScheme.SolvableProperFixedPointProof

/-! # The Borel normalizer theorem on algebraically closed points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The normalizer of the rational points of a Borel subgroup is that subgroup,
over every algebraically closed field and in arbitrary universe. -/
theorem borelNormalizer : BorelNormalizerStatement.{u} := by
  apply borelNormalizerStatement_iff.mpr
  intro k _ _ G _ _ _
  apply borelNormalizer_lieDimension_induction ?_ G
  intro G _ _ _ ih B b hb
  have : Smooth B.X.hom := hb.smooth
  have : ConnectedSpace B.X.left := hb.connectedSpace
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  obtain ⟨T, t, ht⟩ := exists_isMaximalTorus B
  apply hb.pointNormalizer_eq_of_torusNormalizer t ht
    (solvableMaximalTorusConjugacy k B hb.isSolvableGroupScheme)
  intro n hn
  have hti : IsClosedSubgroup (t ≫ b) := ht.2.1.comp hb.isClosedSubgroup
  have : IsClosedImmersion (t ≫ b).hom.hom.left := hti
  have : Mono (t ≫ b).hom.hom.left := inferInstance
  rcases torusEndomorphismDichotomy k T ht.1 (torusCommutatorEnd (t ≫ b) n) with
    hsurj | ⟨ν, hν, hzero⟩
  · have : Smooth T.X.hom := ht.1.smooth
    have : IsReduced T.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k T.X.left T.X.hom
    let φ : T.toGrp ⟶ T.toGrp :=
      CommGroupScheme.groupHom (torusCommutatorEnd (t ≫ b) n)
    have : Surjective φ.hom.hom.left := hsurj
    have : LocallyOfFiniteType (φ.hom.hom.left ≫ T.X.hom) := by
      rw [Over.w φ.hom.hom]
      infer_instance
    have : LocallyOfFiniteType φ.hom.hom.left :=
      locallyOfFiniteType_of_comp φ.hom.hom.left T.X.hom
    obtain ⟨U, a, _, _, _, hU, _, hfactor⟩ :=
      solvableUnipotentFactorization k B hb.isSolvableGroupScheme T t ht
    have hprod : Function.Surjective (rationalPointProductMap a t) := by
      intro y
      obtain ⟨v, s, he⟩ := hfactor y
      exact ⟨⟨v, s⟩, he⟩
    have hcomm : ∀ s : rationalPoints T.toGrp,
        (s ≫ φ.hom.hom) ≫ (t ≫ b).hom.hom =
          n.val * (s ≫ (t ≫ b).hom.hom) * n.val⁻¹ *
            (s ≫ (t ≫ b).hom.hom)⁻¹ := by
      intro s
      simpa only [Category.assoc, GroupScheme.constantPoint_self] using
        comp_torusCommutatorEnd (t ≫ b) n s
    have : IsReduced B.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k B.X.left B.X.hom
    have : IsReduced G.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k G.X.left G.X.hom
    let R := hb.homogeneousQuotient
    have : Smooth R.projection.left := R.smooth_projection
    have : Surjective R.projection.left := R.surjective_projection
    have : QuasiCompact R.projection.left := R.quasiCompact_projection
    have : IsProper R.scheme.hom :=
      hb.quotient_isProper_of_solvableProperFixedPoint solvableProperFixedPoint
        R.scheme R.projection R.separated R.locallyOfFiniteType R.quasiCompact
        R.smooth_projection R.surjective_projection R.quasiCompact_projection R.fibers
    have hq : ∀ (S : Over (Spec (CommRingCat.of k))) (g h : S ⟶ G.X),
        g ≫ R.projection = h ≫ R.projection →
          g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier S :=
      fun S g h he => (R.fibers S g h).mp he
    have hn' : n.val ∈ (SubgroupFunctor.range b).normalizer.carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      rw [SubgroupFunctor.normalizer_range_carrier_base_eq_algClosed_points
        hb.isClosedSubgroup]
      exact hn
    have hnormal :=
      SubgroupFunctor.isNormal_range_of_surjective_commutator_of_proper_homogeneousQuotient
        b hb.isClosedSubgroup a t hU φ n.val hn' hcomm hprod R.projection hq
    have : IsIso b := isIso_of_smooth_normal_of_proper_homogeneousQuotient
      b hb.isClosedSubgroup hb.smooth hnormal R.projection hq
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨n.val ≫ (inv b).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  · let zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B :=
      CommGroupScheme.groupHom ν ≫ t
    let z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G := zB ≫ b
    have hz : IsClosedSubgroup z := (hν.comp ht.2.1).comp hb.isClosedSubgroup
    by_cases hcentral : IsCentral z
    · have heq := normalizer_borelRange_eq_of_smooth_central_gm
        ih b hb z hz hcentral zB rfl
      rw [← heq]
      exact hn
    · apply mem_borelRange_of_noncentral_commutatorKernel_of_intersectionStatement
        centralizerBorelIntersection ih b hb (t ≫ b) (SubgroupFunctor.range_comp_le t b)
        n ν hzero ?_ hn
      simpa only [z, zB, Category.assoc] using hcentral

end Langlands.GroupScheme
