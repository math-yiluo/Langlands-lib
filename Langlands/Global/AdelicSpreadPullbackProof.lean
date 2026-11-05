import Langlands.Global.AdelicSpreadPullbackStatement
import Langlands.Global.AdelicSpreadProductProof
import Langlands.Global.AdelicSpreadClosedImmersionProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Field-level adelic pullbacks from independent spreads -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The map from a pullback cone to any specified limiting product cone. -/
private def pullbackToProduct {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) :
    c.pt ⟶ q.pt :=
  hq.lift (BinaryFan.mk c.fst c.snd)

@[reassoc (attr := simp)]
private lemma pullbackToProduct_fst {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) :
    pullbackToProduct q hq c ≫ q.fst = c.fst :=
  hq.fac (BinaryFan.mk c.fst c.snd) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
private lemma pullbackToProduct_snd {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) :
    pullbackToProduct q hq c ≫ q.snd = c.snd :=
  hq.fac (BinaryFan.mk c.fst c.snd) ⟨WalkingPair.right⟩

/-- A limiting pullback is the equalizer inside any specified field product. -/
private def pullbackToProductFork {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) :
    Fork (q.fst ≫ f) (q.snd ≫ g) :=
  Fork.ofι (pullbackToProduct q hq c) (by
    simp only [← Category.assoc, pullbackToProduct_fst, pullbackToProduct_snd]
    exact c.condition)

private def pullbackToProductForkIsLimit {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) (hc : IsLimit c) :
    IsLimit (pullbackToProductFork q hq c) := by
  refine Fork.IsLimit.mk _
    (fun s => PullbackCone.IsLimit.lift hc (s.ι ≫ q.fst) (s.ι ≫ q.snd)
      (by simpa only [Category.assoc] using s.condition)) ?_ ?_
  · intro s
    apply BinaryFan.IsLimit.hom_ext hq <;>
      simp [pullbackToProductFork, Category.assoc]
  · intro s m hm
    apply PullbackCone.IsLimit.hom_ext hc
    · have h := congrArg (fun r => r ≫ q.fst) hm
      simpa [pullbackToProductFork, Category.assoc] using h
    · have h := congrArg (fun r => r ≫ q.snd) hm
      simpa [pullbackToProductFork, Category.assoc] using h

/-- Separatedness of the field base makes this equalizer inclusion closed. -/
private lemma isClosedImmersion_pullbackToProduct {B : Scheme.{u}}
    {X Y Z : Over B} [IsSeparated Z.hom] {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) (hc : IsLimit c) :
    IsClosedImmersion (pullbackToProduct q hq c).left := by
  let e := (pullbackToProductForkIsLimit q hq c hc).conePointUniqueUpToIso
    (equalizerIsEqualizer (q.fst ≫ f) (q.snd ≫ g))
  have he : e.hom ≫ equalizer.ι (q.fst ≫ f) (q.snd ≫ g) =
      pullbackToProduct q hq c :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  rw [← he, Over.comp_left]
  infer_instance

/-- The point equivalence is a homeomorphism as soon as its inclusion into the
product is an embedding. -/
private lemma isHomeomorph_pullbackPoint_of_product
    (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
    {X Y Z : Over (Spec (CommRingCat.of C))} {f : X ⟶ Z} {g : Y ⟶ Z}
    (q : BinaryFan X Y) (hq : IsLimit q) (c : PullbackCone f g) (hc : IsLimit c)
    (τQ : TopologicalSpace (RingPoint C q.pt A))
    (τP : TopologicalSpace (RingPoint C c.pt A))
    (τX : TopologicalSpace (RingPoint C X A))
    (τY : TopologicalSpace (RingPoint C Y A))
    (hQ : @IsHomeomorph (RingPoint C q.pt A) (RingPoint C X A × RingPoint C Y A)
      τQ (@instTopologicalSpaceProd _ _ τX τY)
      (fun p => (p ≫ q.fst, p ≫ q.snd)))
    (hi : @IsEmbedding (RingPoint C c.pt A) (RingPoint C q.pt A) τP τQ
      (fun p => p ≫ pullbackToProduct q hq c)) :
    letI := τX
    letI := τY
    @IsHomeomorph (RingPoint C c.pt A)
      {r : RingPoint C X A × RingPoint C Y A // r.1 ≫ f = r.2 ≫ g}
      τP inferInstance (affineSchemePullbackPointComparison C A c) := by
  let := τQ
  let := τP
  let := τX
  let := τY
  apply isHomeomorph_iff_isEmbedding_surjective.mpr
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.mp ?_,
    (affineSchemePullbackPointEquiv C A c hc).surjective⟩
  convert hQ.isEmbedding.comp hi using 1
  funext p
  apply Prod.ext <;>
    simp [affineSchemePullbackPointComparison]

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Independent function-field spreads preserve field pullbacks over separated
bases, by their closed inclusion into an independently spread product. -/
theorem curvePlaceSpreadPullback : CurvePlaceSpreadPullbackStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S T U MX MY MP _ _ _ _ _ _ X Y Z _ eX eY f g c eP hc
  classical
  let V := S ∪ T
  have hSV : S ⊆ V := Finset.subset_union_left
  have hTV : T ⊆ V := Finset.subset_union_right
  let MXV := curvePlaceLevelModelBaseChange k F hSV MX
  let MYV := curvePlaceLevelModelBaseChange k F hTV MY
  let : LocallyOfFiniteType MXV.hom := by
    dsimp [MXV, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact MXV.hom := by
    dsimp [MXV, curvePlaceLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType MYV.hom := by
    dsimp [MYV, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact MYV.hom := by
    dsimp [MYV, curvePlaceLevelModelBaseChange]
    infer_instance
  let MQ := MXV ⨯ MYV
  have hfinite := finiteType_overProd MXV MYV
  let : LocallyOfFiniteType MQ.hom := hfinite.1
  let : QuasiCompact MQ.hom := hfinite.2
  let G := Over.pullback
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F V).subtype))
  let eXV := curveProductGenericFiberCompIso k F S MX hSV ≪≫ eX
  let eYV := curveProductGenericFiberCompIso k F T MY hTV ≪≫ eY
  let q : BinaryFan X Y :=
    BinaryFan.mk (G.map (prod.fst : MQ ⟶ MXV) ≫ eXV.hom)
      (G.map (prod.snd : MQ ⟶ MYV) ≫ eYV.hom)
  let hq : IsLimit q :=
    BinaryFan.isLimitCompRightIso _ eYV.hom
      (BinaryFan.isLimitCompLeftIso _ eXV.hom
        (isLimitOfHasBinaryProductOfPreservesLimit G MXV MYV))
  let eQ : curvePlaceModelGenericFiber k F V MQ ≅ q.pt := Iso.refl _
  have hQ := adelicSpreadProduct.1 k F S T V MX MY MQ X Y eX eY q eQ hq
  let i := pullbackToProduct q hq c
  let : IsClosedImmersion i.left :=
    isClosedImmersion_pullbackToProduct q hq c hc
  have hi := adelicSpreadClosedImmersion.1 k F U V MP MQ c.pt q.pt eP eQ i
  let : TopologicalSpace (CurvePlaceAdelePoints k F c.pt) :=
    curvePlaceSpreadAdelePointTopology k F U MP c.pt eP
  let : TopologicalSpace (CurvePlaceAdelePoints k F q.pt) :=
    curvePlaceSpreadAdelePointTopology k F V MQ q.pt eQ
  exact isHomeomorph_pullbackPoint_of_product F (CurvePlaceAdeleRing k F) q hq c hc
    (curvePlaceSpreadAdelePointTopology k F V MQ q.pt eQ)
    (curvePlaceSpreadAdelePointTopology k F U MP c.pt eP)
    (curvePlaceSpreadAdelePointTopology k F S MX X eX)
    (curvePlaceSpreadAdelePointTopology k F T MY Y eY) hQ hi.isEmbedding

/-- Independent number-field spreads preserve field pullbacks over separated
bases, with all infinite adelic factors included. -/
theorem numberFieldSpreadPullback : NumberFieldSpreadPullbackStatement.{u} := by
  intro K _ _ S T U MX MY MP _ _ _ _ _ _ X Y Z _ eX eY f g c eP hc
  classical
  let V := S ∪ T
  have hSV : S ⊆ V := Finset.subset_union_left
  have hTV : T ⊆ V := Finset.subset_union_right
  let MXV := numberFieldLevelModelBaseChange K hSV MX
  let MYV := numberFieldLevelModelBaseChange K hTV MY
  let : LocallyOfFiniteType MXV.hom := by
    dsimp [MXV, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact MXV.hom := by
    dsimp [MXV, numberFieldLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType MYV.hom := by
    dsimp [MYV, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact MYV.hom := by
    dsimp [MYV, numberFieldLevelModelBaseChange]
    infer_instance
  let MQ := MXV ⨯ MYV
  have hfinite := finiteType_overProd MXV MYV
  let : LocallyOfFiniteType MQ.hom := hfinite.1
  let : QuasiCompact MQ.hom := hfinite.2
  let G := Over.pullback
    (Spec.map (CommRingCat.ofHom ((V : Set (FinitePlace K)).integer K).toSubring.subtype))
  let eXV := numberProductGenericFiberCompIso K S MX hSV ≪≫ eX
  let eYV := numberProductGenericFiberCompIso K T MY hTV ≪≫ eY
  let q : BinaryFan X Y :=
    BinaryFan.mk (G.map (prod.fst : MQ ⟶ MXV) ≫ eXV.hom)
      (G.map (prod.snd : MQ ⟶ MYV) ≫ eYV.hom)
  let hq : IsLimit q :=
    BinaryFan.isLimitCompRightIso _ eYV.hom
      (BinaryFan.isLimitCompLeftIso _ eXV.hom
        (isLimitOfHasBinaryProductOfPreservesLimit G MXV MYV))
  let eQ : numberFieldModelGenericFiber K V MQ ≅ q.pt := Iso.refl _
  have hQ := adelicSpreadProduct.2 K S T V MX MY MQ X Y eX eY q eQ hq
  let i := pullbackToProduct q hq c
  let : IsClosedImmersion i.left :=
    isClosedImmersion_pullbackToProduct q hq c hc
  have hi := adelicSpreadClosedImmersion.2 K U V MP MQ c.pt q.pt eP eQ i
  let : TopologicalSpace (NumberFieldAdelePoints K c.pt) :=
    numberFieldSpreadAdelePointTopology K U MP c.pt eP
  let : TopologicalSpace (NumberFieldAdelePoints K q.pt) :=
    numberFieldSpreadAdelePointTopology K V MQ q.pt eQ
  exact isHomeomorph_pullbackPoint_of_product K (Adeles K) q hq c hc
    (numberFieldSpreadAdelePointTopology K V MQ q.pt eQ)
    (numberFieldSpreadAdelePointTopology K U MP c.pt eP)
    (numberFieldSpreadAdelePointTopology K S MX X eX)
    (numberFieldSpreadAdelePointTopology K T MY Y eY) hQ hi.isEmbedding

/-- Both arithmetic cases of the independent-spread separated-base pullback
comparison on actual adelic points. -/
theorem adelicSpreadPullback : AdelicSpreadPullbackStatement.{u} :=
  ⟨curvePlaceSpreadPullback, numberFieldSpreadPullback⟩

end Langlands.Global
