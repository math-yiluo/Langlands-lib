import Langlands.GroupScheme.Torus.RelativePreimageConjugacy
import Langlands.GroupScheme.Torus.RelativeCentralQuotientImage
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.SimplyConnected.CoverPreimageToolkit
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Maximal torus preimages in relative central quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

private theorem preimage_range_baseChange {S U : Scheme.{u}} (b : U ⟶ S)
    {G Q H A : GroupScheme S} (q : G ⟶ Q) (t : H ⟶ G) (j : A ⟶ Q)
    (h : (SubgroupFunctor.range j).comap q = SubgroupFunctor.range t) :
    (SubgroupFunctor.range ((baseChange b).map j)).comap ((baseChange b).map q) =
      SubgroupFunctor.range ((baseChange b).map t) := by
  rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.comap_baseChange,
    h, ← SubgroupFunctor.range_baseChangeHom]

namespace SubgroupPreimage

/-- Once one relative maximal target torus has a relative-torus preimage,
every relative maximal target torus has a relative-torus preimage. -/
theorem isRelativeTorus_of_maximalImage {S : Scheme.{u}} {G Q H : GroupScheme S}
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom]
    (t : H ⟶ G) (hT : RelativeTorus.IsTorus H) (ht : IsClosedSubgroup t)
    (A B : CommGroupScheme S) (j : A.toGrp ⟶ Q) (j' : B.toGrp ⟶ Q)
    (hA : RelativeTorus.IsTorus A.toGrp) (hj : IsClosedSubgroup j)
    (hmj : IsFibrewiseMaximalTorus j)
    (hB : RelativeTorus.IsTorus B.toGrp) (hj' : IsClosedSubgroup j')
    (hmj' : IsFibrewiseMaximalTorus j')
    (hpre : (SubgroupFunctor.range j).comap q = SubgroupFunctor.range t) :
    RelativeTorus.IsTorus (groupScheme q j') := by
  obtain ⟨𝒰, h𝒰⟩ := etaleLocalMaximalTorusConjugacy S Q A B j j' hA hj hmj hB hj' hmj'
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply isRelativeTorus_of_fppfCover q j' 𝒱
  intro a
  let b := 𝒰.f a
  let F := baseChange b
  let : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  let : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b q.hom.hom inferInstance
  obtain ⟨g, hg⟩ := h𝒰 a
  obtain ⟨V, c, hcf, hcs, hcl, x, hx⟩ := exists_fppf_baseChange_section_lift (F.map q) g
  let : Flat c := hcf
  let : Surjective c := hcs
  let : LocallyOfFinitePresentation c := hcl
  let C := baseChange c
  let 𝒲 : Scheme.Cover Scheme.fppfPrecoverage (𝒰.X a) :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) PUnit
      (fun _ => V) (fun _ => c)
      (fun s => by obtain ⟨v, hv⟩ := hcs.surj s; exact ⟨PUnit.unit, v, hv⟩)
      (fun _ => ⟨hcf, hcl⟩)
  apply isRelativeTorus_of_fppfCover (F.map q) (F.map j') 𝒲
  intro _
  change RelativeTorus.IsTorus (groupScheme (C.map (F.map q)) (C.map (F.map j')))
  apply isRelativeTorus_of_conjugate_image (C.map (F.map q))
    (C.map (F.map t)) (C.map (F.map j)) (C.map (F.map j'))
    ((hT.baseChange b).baseChange c) ((ht.baseChange b).baseChange c)
    ((hj.baseChange b).baseChange c) ((hj'.baseChange b).baseChange c)
    (preimage_range_baseChange c (F.map q) (F.map t) (F.map j)
      (preimage_range_baseChange b q t j hpre))
    ((C.obj (F.obj G)).innerIso x) (C.mapIso ((F.obj Q).innerIso g))
  · rw [Functor.mapIso_hom, baseChange_innerIso_hom, ← hx]
    exact innerIso_hom_comp (C.map (F.map q)) x
  · change SubgroupFunctor.range
        (C.map (F.map j) ≫ C.map ((F.obj Q).innerIso g).hom) =
      SubgroupFunctor.range (C.map (F.map j'))
    rw [← C.map_comp, SubgroupFunctor.range_baseChangeHom, hg,
      ← SubgroupFunctor.range_baseChangeHom]

/-- The actual preimage of any relative maximal torus is a relative torus,
assuming affine central multiplicative-type quotients exist. -/
theorem isRelativeTorus_of_centralMultiplicativeTypeQuotients
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Q Z : GroupScheme S}
    (hG : IsReductive G) (hQ : IsReductive Q)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (B : CommGroupScheme S) (j' : B.toGrp ⟶ Q)
    (hB : RelativeTorus.IsTorus B.toGrp) (hj' : IsClosedSubgroup j')
    (hmj' : IsFibrewiseMaximalTorus j') :
    RelativeTorus.IsTorus (groupScheme q j') := by
  let : Smooth Q.X.hom := hQ.smooth
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := etaleLocalMaximalTorusExistence S G hG
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply isRelativeTorus_of_fppfCover q j' 𝒱
  intro a
  let b := 𝒰.f a
  let F := baseChange b
  let Fc := CommGroupScheme.baseChange b
  have hGb : IsReductive (F.obj G) := hG.baseChange b
  have hQb : IsReductive (F.obj Q) := hQ.baseChange b
  let : Smooth (F.obj Q).X.hom := hQb.smooth
  let : IsAffineHom (F.obj Q).X.hom := hQb.isAffineHom
  have hqb : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map z)) (F.map q) := by
    change RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange b).map z)) ((baseChange b).map q)
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  let : Flat (F.map q).hom.hom.left := hqb.1
  let : Surjective (F.map q).hom.hom.left := hqb.2.1
  let : LocallyOfFinitePresentation (F.map q).hom.hom.left := hqb.2.2.1
  obtain ⟨T, t, hT, ht, hmt⟩ := h𝒰 a
  obtain ⟨A, j, p, hA, hj, hmj, _, _, _, _, hpre⟩ :=
    exists_relativeMaximalTorus_image_of_centralMultiplicativeTypeQuotients
      hquotient hGb hQb (F.map z) (hz.baseChange b) (hc.baseChange b) (hZ.baseChange b)
      (F.map q) hqb T t hT ht hmt
  exact isRelativeTorus_of_maximalImage (F.map q) t hT ht A (Fc.obj B) j (F.map j')
    hA hj hmj (hB.baseChange b) (hj'.baseChange b) (hmj'.baseChange b) hpre

/-- If a maximal torus has a relative-torus preimage, that preimage is
maximal on every residue fibre. -/
theorem isFibrewiseMaximalTorus_of_isRelativeTorus
    {S : Scheme.{u}} {G Q : GroupScheme S} (hQ : IsReductive Q)
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (B : CommGroupScheme S) (j : B.toGrp ⟶ Q)
    (hB : RelativeTorus.IsTorus B.toGrp) (hj : IsClosedSubgroup j)
    (hmj : IsFibrewiseMaximalTorus j)
    (hP : RelativeTorus.IsTorus (groupScheme q j)) :
    IsFibrewiseMaximalTorus (T := hP.commGroupScheme) (inclusion q j) := by
  let A := hP.commGroupScheme
  let i : A.toGrp ⟶ G := inclusion q j
  let p : A.toGrp ⟶ B.toGrp := projection q j
  let : IsAffineHom A.toGrp.X.hom := hP.isAffineHom
  let : IsAffineHom B.toGrp.X.hom := hB.isAffineHom
  let : Flat p.hom.hom.left := flat_projection q j
  let : Surjective p.hom.hom.left := surjective_projection q j
  let : QuasiCompact p.hom.hom.left := by
    have : QuasiCompact (p.hom.hom.left ≫ B.toGrp.X.hom) := by
      rw [Over.w p.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ B.toGrp.X.hom
  have hsq : i ≫ q = p ≫ j := subgroupIntersection_condition q j
  have hmap : torusCentralizer (T := A) i ≤
      (torusCentralizer (T := A) (i ≫ q)).comap q := by
    intro U x hx
    change x ≫ q.hom.hom ∈ (torusCentralizer (T := A) (i ≫ q)).carrier U
    intro V a y
    have hh := (hx V a y).map ((yonedaGrp.map q).app (Opposite.op V)).hom
    change Commute ((a ≫ x) ≫ q.hom.hom) ((y ≫ i.hom.hom) ≫ q.hom.hom) at hh
    simpa only [Grp.comp_hom_hom, Category.assoc] using hh
  have hself : torusCentralizer (T := A) i = SubgroupFunctor.range i := by
    apply le_antisymm
    · rw [hsq, torusCentralizer_comp_of_fpqc p j,
        relativeTorusCentralizer_eq_range_of_fibrewiseMaximal hQ hB j hj hmj] at hmap
      rw [range_inclusion]
      exact hmap
    · exact range_le_torusCentralizer (T := A) i
  intro s
  let b := S.fromSpecResidueField s
  apply isMaximalTorus_of_torusCentralizer_eq
    (T := (CommGroupScheme.baseChange b).obj A)
    ((hP.baseChange b).isTorus) ((isClosedSubgroup q j hj).baseChange b)
  exact (torusCentralizer_baseChange b (T := A) i).trans
    ((congrArg (fun F : SubgroupFunctor G => F.baseChange b) hself).trans
      (SubgroupFunctor.range_baseChangeHom b i).symm)

end SubgroupPreimage

/-- The reverse maximal-torus correspondence for central quotients reduces
to affine central multiplicative-type quotient existence. -/
theorem exists_relativeMaximalTorus_preimage_of_centralMultiplicativeTypeQuotients
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Q Z : GroupScheme S}
    (hG : IsReductive G) (hQ : IsReductive Q)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (B : CommGroupScheme S) (j : B.toGrp ⟶ Q)
    (hB : RelativeTorus.IsTorus B.toGrp) (hj : IsClosedSubgroup j)
    (hmj : IsFibrewiseMaximalTorus j) :
    ∃ (A : CommGroupScheme S) (i : A.toGrp ⟶ G),
      RelativeTorus.IsTorus A.toGrp ∧ IsClosedSubgroup i ∧
      IsFibrewiseMaximalTorus i ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  have hP := SubgroupPreimage.isRelativeTorus_of_centralMultiplicativeTypeQuotients
    hquotient hG hQ z hz hc hZ q hq B j hB hj hmj
  exact ⟨hP.commGroupScheme, SubgroupPreimage.inclusion q j, hP,
    SubgroupPreimage.isClosedSubgroup q j hj,
    SubgroupPreimage.isFibrewiseMaximalTorus_of_isRelativeTorus hQ q B j hB hj hmj hP,
    (SubgroupPreimage.range_inclusion q j).symm⟩


/-- The complete proposition proved by the supplied helper, with every hypothesis explicit. -/
def RelativeCentralQuotientPreimageReductionStatement : Prop :=
  ∀
    (_hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Q Z : GroupScheme S}
    (_hG : IsReductive G) (_hQ : IsReductive Q)
    (z : Z ⟶ G) (_hz : IsClosedSubgroup z) (_hc : IsCentral z)
    (_hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (_hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    (B : CommGroupScheme S) (j : B.toGrp ⟶ Q)
    (_hB : RelativeTorus.IsTorus B.toGrp) (_hj : IsClosedSubgroup j)
    (_hmj : IsFibrewiseMaximalTorus j),
    ∃ (A : CommGroupScheme S) (i : A.toGrp ⟶ G),
      RelativeTorus.IsTorus A.toGrp ∧ IsClosedSubgroup i ∧
      IsFibrewiseMaximalTorus i ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i

/-- The retained helper proof establishes the named proposition. -/
theorem relativeCentralQuotientPreimageReduction : RelativeCentralQuotientPreimageReductionStatement.{u} := by
  unfold RelativeCentralQuotientPreimageReductionStatement
  exact @exists_relativeMaximalTorus_preimage_of_centralMultiplicativeTypeQuotients.{u}

end Langlands.GroupScheme
