import Langlands.GroupScheme.Absolute.BorelQuotientDescent
import Langlands.GroupScheme.Absolute.BorelNormalizerCentralQuotient
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding
import Langlands.GroupScheme.KernelRepresentativeTransport

/-! # Borel images in two supplied multiplicative quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SubgroupFunctor

variable {S : Scheme.{u}} {Z B G BQ Q : GroupScheme S}

/-- A factorization through a monomorphism identifies the inverse image of
the represented subgroup on every scheme test. -/
theorem comap_range_of_factor (i : B ⟶ G) [Mono i.hom.hom]
    (z : Z ⟶ G) (zB : Z ⟶ B) (hf : zB ≫ i = z) :
    (range z).comap i = range zB := by
  apply ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_comap]
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := mem_range.mp hx
    refine mem_range.mpr ⟨a, ?_⟩
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact ha
  · intro hx
    obtain ⟨a, rfl⟩ := mem_range.mp hx
    exact mem_range.mpr ⟨a, by rw [Category.assoc, ← Grp.comp_hom_hom, hf]⟩

/-- The homomorphism on supplied fppf quotients by a subgroup and its
factorization through the original monomorphic subgroup. -/
def quotientHomOfKernelFactor (i : B ⟶ G) [Mono i.hom.hom]
    (z : Z ⟶ G) (zB : Z ⟶ B) (hf : zB ≫ i = z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (range z) q)
    (p : B ⟶ BQ) (hp : RelativeRoot.IsFppfQuotient (range zB) p)
    [QuasiCompact p.hom.hom.left] : BQ ⟶ Q := by
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  apply quotientSubgroupHom i q p
  rw [hp.2.2.2, hq.2.2.2, comap_range_of_factor i z zB hf]

end SubgroupFunctor

section Field

variable {k : Type u} [Field k] [IsAlgClosed k]
    {B G BQ Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom BQ.X.hom] [IsAffineHom Q.X.hom]

/-- Two supplied affine fppf quotients by the same closed copy of Gm give
an actual quotient Borel with exactly the original all-test inverse image. -/
theorem exists_borel_of_fppf_gm_quotients
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hz : IsClosedSubgroup z)
    (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B) (hf : zB ≫ i = z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (p : B ⟶ BQ) (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zB) p) :
    ∃ j : BQ ⟶ Q,
      IsBorelSubgroup j ∧ i ≫ q = p ≫ j ∧
      Smooth q.hom.hom.left ∧ Smooth p.hom.hom.left ∧
      GeometricallyConnected q.hom.hom.left ∧
      IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsClosedImmersion z.hom.hom.left := hz
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have hcomp : IsClosedImmersion (zB.hom.hom.left ≫ i.hom.hom.left) := by
    change IsClosedImmersion (zB ≫ i).hom.hom.left
    rw [hf]
    infer_instance
  have : IsClosedImmersion (zB.hom.hom.left ≫ i.hom.hom.left) := hcomp
  have : IsClosedImmersion zB.hom.hom.left :=
    IsClosedImmersion.of_comp_isClosedImmersion zB.hom.hom.left i.hom.hom.left
  have : Mono zB.hom.hom := Over.mono_of_mono_left _
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : Flat p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2.1
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  have hpc : QuasiCompact (p.hom.hom.left ≫ BQ.X.hom) := by
    rw [Over.w p.hom.hom]
    infer_instance
  have : QuasiCompact (p.hom.hom.left ≫ BQ.X.hom) := hpc
  have : QuasiCompact p.hom.hom.left := QuasiCompact.of_comp _ BQ.X.hom
  have : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ (smooth_gm _)
  have : Smooth p.hom.hom.left :=
    hp.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ (smooth_gm _)
  have : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
    isSplitTorus_gm.isAffineHom
  have : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _
  have : ConnectedSpace (Gm (Spec (CommRingCat.of k))).X.left :=
    isSplitTorus_gm.connectedSpace
  have : GeometricallyConnected (Gm (Spec (CommRingCat.of k))).X.hom :=
    geometricallyConnected_of_connected _
  have : GeometricallyConnected (kernel q).X.hom :=
    KernelRepresentative.geometricallyConnected q z hq.2.2.2
  have : GeometricallyConnected q.hom.hom.left :=
    geometricallyConnected_of_geometricallyConnected_kernel q
  have hk : (SubgroupFunctor.range (kernelι q)).comap i =
      SubgroupFunctor.range (kernelι p) := by
    rw [hq.2.2.2, hp.2.2.2, SubgroupFunctor.comap_range_of_factor i z zB hf]
  have hc : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i := by
    rw [hq.2.2.2]
    intro T x hx
    obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨a ≫ zB.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact ha
  let j := SubgroupFunctor.quotientHomOfKernelFactor i z zB hf q hq p hp
  have hjdef : j = SubgroupFunctor.quotientSubgroupHom i q p hk.ge := rfl
  have hjclosed : IsClosedSubgroup j := by
    rw [hjdef]
    exact SubgroupFunctor.quotientSubgroupHom_isClosedSubgroup i q p hk.ge hk.le hc
      hi.isClosedSubgroup
  have hpb : IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom := by
    rw [hjdef]
    exact SubgroupFunctor.quotientSubgroupHom_isPullback i q p hk.ge hk.le hc
  refine ⟨j, isBorelSubgroup_of_quotient_square i hi q p j hjclosed hpb, ?_,
    inferInstance, inferInstance, inferInstance, hpb, ?_⟩
  · rw [hjdef]
    exact SubgroupFunctor.quotientSubgroupHom_square i q p hk.ge
  · rw [hjdef]
    exact SubgroupFunctor.quotientSubgroupHom_comap_range i q p hk.ge hc

/-- Once the two affine Gm quotients are supplied, the smaller-group induction
hypothesis proves rational self-normalization of the original Borel. -/
theorem normalizer_borelRange_eq_of_supplied_fppf_gm_quotients
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hz : IsClosedSubgroup z)
    (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B) (hf : zB ≫ i = z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (p : B ⟶ BQ) (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zB) p) :
    Subgroup.normalizer
        ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  obtain ⟨j, hj, _, _, _, _, _, hpre⟩ :=
    exists_borel_of_fppf_gm_quotients i hi z hz zB hf q hq p hp
  exact normalizer_borelRange_eq_of_fppf_gm_quotient ih i z hz q hq j hj hpre

end Field

end Langlands.GroupScheme
