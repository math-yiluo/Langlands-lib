import Langlands.GroupScheme.Absolute.BorelNormalizerInduction
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Lie.QuotientDimension
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # The central multiplicative quotient step of Borel normalizer induction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {S : Scheme.{u}} {Z G Q : GroupScheme S}
    {z : Z ⟶ G} {q : G ⟶ Q}

/-- An fppf quotient with the specified kernel kills its actual inclusion. -/
theorem IsFppfQuotient.inclusion_comp_eq_one
    (hq : IsFppfQuotient (SubgroupFunctor.range z) q) :
    z.hom.hom ≫ q.hom.hom = 1 := by
  apply (mem_range_kernelι_iff q z.hom.hom).mp
  rw [hq.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 Z.X, Category.id_comp _⟩

section Field

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A supplied affine fppf quotient by a closed copy of Gm has the geometric
and strict Lie-dimension properties needed by normalizer induction. -/
theorem IsFppfQuotient.gm_induction_properties
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom Q.X.hom]
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (q : G ⟶ Q)
    (hq : IsFppfQuotient (SubgroupFunctor.range z) q) :
    Smooth q.hom.hom.left ∧ Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      Lie.dimension Q < Lie.dimension G := by
  have : IsClosedImmersion z.hom.hom.left := hz
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have : Surjective q.hom.hom.left := hq.2.1
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  have : QuasiCompact q.hom.hom.left :=
    QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  have hs : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ (smooth_gm _)
  have : Smooth q.hom.hom.left := hs
  have hcomp : Smooth (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : Smooth (q.hom.hom.left ≫ Q.X.hom) := hcomp
  have hQ : Smooth Q.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.hom.hom.left Q.X.hom
  have : Smooth Q.X.hom := hQ
  exact ⟨hs, hQ, hq.connectedSpace,
    Lie.dimension_lt_of_smooth_kills_gm q hs z hq.inclusion_comp_eq_one⟩

end Field

end RelativeRoot

section Normalizer

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B Q BQ : GroupScheme (Spec (CommRingCat.of k))}

/-- Exact Borel inverse images under affine fppf quotients by closed Gm
subgroups satisfy rational self-normalization by the smaller-group induction
hypothesis. Existence of this quotient and of its Borel inverse image is
retained as input. -/
theorem normalizer_borelRange_eq_of_fppf_gm_quotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom Q.X.hom]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (iQ : BQ ⟶ Q) (hiQ : IsBorelSubgroup iQ)
    (hpre : (SubgroupFunctor.range iQ).comap q = SubgroupFunctor.range i) :
    Subgroup.normalizer
        ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  obtain ⟨hs, hQ, hc, hd⟩ := hq.gm_induction_properties z hz q
  let : Smooth q.hom.hom.left := hs
  let : Smooth Q.X.hom := hQ
  let : ConnectedSpace Q.X.left := hc
  let : Surjective q.hom.hom.left := hq.2.1
  exact SubgroupFunctor.normalizer_carrier_base_eq_of_quotient q
    (SubgroupFunctor.range i) (SubgroupFunctor.range iQ) hpre
    (ih Q hd BQ iQ hiQ)

/-- An actual Borel point lifting an ambient normalizing point in the
multiplicative quotient branch. -/
def borelPointOfFppfGmQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom Q.X.hom]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (iQ : BQ ⟶ Q) (hiQ : IsBorelSubgroup iQ)
    (hpre : (SubgroupFunctor.range iQ).comap q = SubgroupFunctor.range i)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp
    ((normalizer_borelRange_eq_of_fppf_gm_quotient ih i z hz q hq iQ hiQ hpre) ▸ hx))

/-- The chosen Borel point has precisely the original ambient image. -/
theorem borelPointOfFppfGmQuotient_comp
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom Q.X.hom]
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (iQ : BQ ⟶ Q) (hiQ : IsBorelSubgroup iQ)
    (hpre : (SubgroupFunctor.range iQ).comap q = SubgroupFunctor.range i)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    borelPointOfFppfGmQuotient ih i z hz q hq iQ hiQ hpre x hx ≫ i.hom.hom = x :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp
    ((normalizer_borelRange_eq_of_fppf_gm_quotient ih i z hz q hq iQ hiQ hpre) ▸ hx))

end Normalizer

end Langlands.GroupScheme
