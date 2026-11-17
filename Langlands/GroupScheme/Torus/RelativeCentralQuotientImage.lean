import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotientStatement
import Langlands.GroupScheme.Torus.CentralSurjectionMaximalImage
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent
import Langlands.GroupScheme.Torus.RelativeQuotient
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding

/-! # Maximal torus images in relative central quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Assuming affine quotients by central multiplicative-type subgroups exist,
every relative maximal torus has a relative maximal image under a supplied
central quotient of reductive groups. The whole inverse image is the original torus. -/
theorem exists_relativeMaximalTorus_image_of_centralMultiplicativeTypeQuotients
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Q Z : GroupScheme S}
    (hG : IsReductive G) (hQ : IsReductive Q)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) :
    ∃ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ Q) (p : T ⟶ T'),
      RelativeTorus.IsTorus T'.toGrp ∧ IsClosedSubgroup t' ∧
      IsFibrewiseMaximalTorus t' ∧
      Flat (CommGroupScheme.groupHom p).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom p).hom.hom.left ∧
      LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left ∧
      CommGroupScheme.groupHom p ≫ t' = t ≫ q ∧
      (SubgroupFunctor.range t').comap q = SubgroupFunctor.range t := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : QuasiCompact q.hom.hom.left := by
    have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ Q.X.hom
  let zT := relativeMaximalTorusCentralFactor hG hT t ht hmax z hc
  have hzt : zT ≫ t = z := relativeMaximalTorusCentralFactor_comp hG hT t ht hmax z hc
  have hzTclosed : IsClosedSubgroup zT := by
    let : IsClosedImmersion (zT.hom.hom.left ≫ t.hom.hom.left) := by
      change IsClosedImmersion (zT ≫ t).hom.hom.left
      rw [hzt]
      exact hz
    exact IsClosedImmersion.of_comp_isClosedImmersion zT.hom.hom.left t.hom.hom.left
  have hzTcentral : IsCentral zT := by
    intro U x V a y
    change _ * _ = _ * _
    exact mul_comm _ _
  obtain ⟨R, p, hR, hp⟩ := hquotient S T.toGrp hT.smooth hT.isAffineHom
    (fun s => (hT.isReductive.geometricFiber s).connectedSpace)
    Z zT hzTclosed hzTcentral hZ
  let : IsAffineHom R.X.hom := hR
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  let : LocallyOfFinitePresentation p.hom.hom.left := hp.2.2.1
  let : QuasiCompact p.hom.hom.left := by
    have : QuasiCompact (p.hom.hom.left ≫ R.X.hom) := by
      rw [Over.w p.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ R.X.hom
  have hrz : (SubgroupFunctor.range z).comap t = SubgroupFunctor.range zT := by
    ext U x
    rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    have hs : zT.hom.hom ≫ t.hom.hom = z.hom.hom := congrArg (fun f => f.hom.hom) hzt
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (cancel_mono t.hom.hom).mp ?_⟩
      rw [Category.assoc, hs]
      exact hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [← hs, ← Category.assoc, hy]
  have hk : SubgroupFunctor.range (kernelι p) =
      (SubgroupFunctor.range (kernelι q)).comap t := by
    rw [hp.2.2.2, hq.2.2.2, hrz]
  have hcontain : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range t := by
    rw [hq.2.2.2]
    exact ((isCentral_iff_range_le_center z).mp hc).trans
      (center_le_range_relativeMaximalTorus hG hT t ht hmax)
  let j := SubgroupFunctor.quotientSubgroupHom t q p hk.le
  have hj : IsClosedSubgroup j :=
    SubgroupFunctor.quotientSubgroupHom_isClosedSubgroup t q p hk.le hk.ge hcontain ht
  let T' := commGroupSchemeTargetOfFppfHom p
  let : IsAffineHom T'.toGrp.X.hom := hR
  let p' : T ⟶ T' := Additive.ofMul p
  let : Flat (CommGroupScheme.groupHom p').hom.hom.left := hp.1
  let : Surjective (CommGroupScheme.groupHom p').hom.hom.left := hp.2.1
  let : LocallyOfFinitePresentation (CommGroupScheme.groupHom p').hom.hom.left := hp.2.2.1
  have hs : CommGroupScheme.groupHom p' ≫ j = t ≫ q :=
    (SubgroupFunctor.quotientSubgroupHom_square t q p hk.le).symm
  have hT' : RelativeTorus.IsTorus T'.toGrp := hT.of_fppfHom p
  have hqcentral : IsCentral (kernelι q) := by
    rw [isCentral_iff_range_le_center, hq.2.2.2]
    exact (isCentral_iff_range_le_center z).mp hc
  refine ⟨T', j, p', hT', hj, ?_, hp.1, hp.2.1, hp.2.2.1, hs, ?_⟩
  · exact IsFibrewiseMaximalTorus.image_of_centralFppfHom
      (S := S) (G := G) (H := Q) (T := T) (T' := T') (i := t)
      hmax q hG hQ hqcentral j hj hT' p' hs
  · exact SubgroupFunctor.quotientSubgroupHom_comap_range t q p hk.le hcontain


/-- The complete proposition proved by the supplied helper, with every hypothesis explicit. -/
def RelativeCentralQuotientImageReductionStatement : Prop :=
  ∀
    (_hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Q Z : GroupScheme S}
    (_hG : IsReductive G) (_hQ : IsReductive Q)
    (z : Z ⟶ G) (_hz : IsClosedSubgroup z) (_hc : IsCentral z)
    (_hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (_hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (_hT : RelativeTorus.IsTorus T.toGrp) (_ht : IsClosedSubgroup t)
    (_hmax : IsFibrewiseMaximalTorus t),
    ∃ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ Q) (p : T ⟶ T'),
      RelativeTorus.IsTorus T'.toGrp ∧ IsClosedSubgroup t' ∧
      IsFibrewiseMaximalTorus t' ∧
      Flat (CommGroupScheme.groupHom p).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom p).hom.hom.left ∧
      LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left ∧
      CommGroupScheme.groupHom p ≫ t' = t ≫ q ∧
      (SubgroupFunctor.range t').comap q = SubgroupFunctor.range t

/-- The retained helper proof establishes the named proposition. -/
theorem relativeCentralQuotientImageReduction : RelativeCentralQuotientImageReductionStatement.{u} := by
  unfold RelativeCentralQuotientImageReductionStatement
  exact @exists_relativeMaximalTorus_image_of_centralMultiplicativeTypeQuotients.{u}

end Langlands.GroupScheme
