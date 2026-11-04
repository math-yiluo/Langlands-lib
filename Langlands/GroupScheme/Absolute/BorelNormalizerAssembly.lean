import Langlands.GroupScheme.Absolute.BorelNormalizerTorus
import Langlands.GroupScheme.Absolute.BorelNormalizerNoncentral
import Langlands.GroupScheme.Absolute.BorelNormalizerSmoothSurjective
import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationStatement
import Langlands.GroupScheme.Rational.SolvableMaximalTorusStatement
import Langlands.GroupScheme.Torus.EndomorphismDichotomyStatement
import Langlands.GroupScheme.Torus.HeightExistence

/-! # Assembly of the Borel normalizer induction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The existing commutator branches give the exact Borel normalizer conclusion
from the five explicitly retained structural statements. -/
theorem borelNormalizer_of_structuralInputs
    (hdichotomy : TorusEndomorphismDichotomyStatement.{u})
    (hintersection : CentralizerBorelIntersectionStatement.{u})
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    (hfactorization : SolvableUnipotentFactorizationStatement.{u})
    (hconjugacy : SolvableMaximalTorusConjugacyStatement.{u}) :
    BorelNormalizerStatement.{u} := by
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
    (hconjugacy k B hb.isSolvableGroupScheme)
  intro n hn
  have hti : IsClosedSubgroup (t ≫ b) := ht.2.1.comp hb.isClosedSubgroup
  have : IsClosedImmersion (t ≫ b).hom.hom.left := hti
  have : Mono (t ≫ b).hom.hom.left := inferInstance
  rcases hdichotomy k T ht.1 (torusCommutatorEnd (t ≫ b) n) with
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
      hfactorization k B hb.isSolvableGroupScheme T t ht
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
    have : IsIso b := hb.isIso_of_surjective_commutator_of_parabolicQuotient
      hproper a t hU φ n.val hn hcomm hprod
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
        hintersection ih b hb (t ≫ b) (SubgroupFunctor.range_comp_le t b)
        n ν hzero ?_ hn
      simpa only [z, zB, Category.assoc] using hcentral

/-- Given the structural statements used by the assembly, choose an actual
Borel point above any rational point normalizing that Borel. -/
def borelPointOfStructuralInputs
    (hdichotomy : TorusEndomorphismDichotomyStatement.{u})
    (hintersection : CentralizerBorelIntersectionStatement.{u})
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    (hfactorization : SolvableUnipotentFactorizationStatement.{u})
    (hconjugacy : SolvableMaximalTorusConjugacyStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (x : rationalPoints G)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (rationalPoints G))) :
    {p : rationalPoints B // p ≫ b.hom.hom = x} := by
  have heq := borelNormalizer_of_structuralInputs
    hdichotomy hintersection hproper hfactorization hconjugacy k G B b hb
  rw [heq] at hx
  let h := SubgroupFunctor.mem_range.mp hx
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.GroupScheme
