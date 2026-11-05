import Langlands.Global.AdelicSpreadProductStatement
import Langlands.Global.AdelicFixedModelPullbackProof
import Langlands.Global.AdelicSpreadTopologyIndependenceProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Products on adelic points for independent arithmetic spreads -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A finite-type model product is finite type without a separatedness premise. -/
lemma finiteType_overProd {B : Scheme.{u}} (X Y : Over B)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    LocallyOfFiniteType (X ⨯ Y).hom ∧ QuasiCompact (X ⨯ Y).hom := by
  have h := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X Y)
  have : LocallyOfFiniteType (prod.fst : X ⨯ Y ⟶ X).left :=
    MorphismProperty.of_isPullback h.flip inferInstance
  have : QuasiCompact (prod.fst : X ⨯ Y ⟶ X).left :=
    MorphismProperty.of_isPullback h.flip inferInstance
  rw [← Over.w (prod.fst : X ⨯ Y ⟶ X)]
  exact ⟨inferInstance, inferInstance⟩

/-- A terminal-base pullback comparison is the ordinary product comparison. -/
private lemma isHomeomorph_product_of_terminal
    (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
    (τ : ∀ W : Over (Spec (CommRingCat.of C)), TopologicalSpace (RingPoint C W A))
    (X Y : Over (Spec (CommRingCat.of C)))
    (h : letI := τ X
      letI := τ Y
      @IsHomeomorph (RingPoint C (X ⨯ Y) A)
        {q : RingPoint C X A × RingPoint C Y A //
          q.1 ≫ Over.mkIdTerminal.from X = q.2 ≫ Over.mkIdTerminal.from Y}
        (τ (X ⨯ Y)) inferInstance
        (affineSchemePullbackPointComparison C A
          (IsPullback.of_is_product (prodIsProd X Y) Over.mkIdTerminal).cone)) :
    @IsHomeomorph (RingPoint C (X ⨯ Y) A) (RingPoint C X A × RingPoint C Y A)
      (τ (X ⨯ Y)) (@instTopologicalSpaceProd _ _ (τ X) (τ Y))
      (fun p => (p ≫ prod.fst, p ≫ prod.snd)) := by
  let := τ X
  let := τ Y
  let := τ (X ⨯ Y)
  let E :
      {q : RingPoint C X A × RingPoint C Y A //
        q.1 ≫ Over.mkIdTerminal.from X = q.2 ≫ Over.mkIdTerminal.from Y} ≃ₜ
        RingPoint C X A × RingPoint C Y A :=
    { toEquiv :=
        { toFun := Subtype.val
          invFun := fun q => ⟨q, Over.mkIdTerminal.hom_ext _ _⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  exact E.isHomeomorph.comp h

/-- Compatible product legs identify the transported comparison pointwise. -/
private lemma isHomeomorph_pointProduct_transport
    (C B A : Type u) [CommRing C] [CommRing B] [CommRing A]
    [Algebra C A] [Algebra B A]
    (MX MY : Over (Spec (CommRingCat.of C)))
    (X Y : Over (Spec (CommRingCat.of B))) (c : BinaryFan X Y)
    (τP : TopologicalSpace (RingPoint C (MX ⨯ MY) A))
    (τX : TopologicalSpace (RingPoint C MX A))
    (τY : TopologicalSpace (RingPoint C MY A))
    (σP : TopologicalSpace (RingPoint B c.pt A))
    (σX : TopologicalSpace (RingPoint B X A))
    (σY : TopologicalSpace (RingPoint B Y A))
    (EP : @Homeomorph (RingPoint C (MX ⨯ MY) A) (RingPoint B c.pt A) τP σP)
    (EX : @Homeomorph (RingPoint C MX A) (RingPoint B X A) τX σX)
    (EY : @Homeomorph (RingPoint C MY A) (RingPoint B Y A) τY σY)
    (hX : ∀ p, EP p ≫ c.fst = EX (p ≫ prod.fst))
    (hY : ∀ p, EP p ≫ c.snd = EY (p ≫ prod.snd))
    (h : @IsHomeomorph (RingPoint C (MX ⨯ MY) A)
      (RingPoint C MX A × RingPoint C MY A) τP
      (@instTopologicalSpaceProd _ _ τX τY)
      (fun p => (p ≫ prod.fst, p ≫ prod.snd))) :
    @IsHomeomorph (RingPoint B c.pt A) (RingPoint B X A × RingPoint B Y A)
      σP (@instTopologicalSpaceProd _ _ σX σY)
      (fun p => (p ≫ c.fst, p ≫ c.snd)) := by
  let := τP
  let := τX
  let := τY
  let := σP
  let := σX
  let := σY
  let H := IsHomeomorph.homeomorph _ h
  have heq : ⇑((EP.symm.trans H).trans (EX.prodCongr EY)) =
      fun p => (p ≫ c.fst, p ≫ c.snd) := by
    funext p
    apply Prod.ext
    · exact (hX (EP.symm p)).symm.trans (by rw [EP.apply_symm_apply])
    · exact (hY (EP.symm p)).symm.trans (by rw [EP.apply_symm_apply])
  exact heq ▸ ((EP.symm.trans H).trans (EX.prodCongr EY)).isHomeomorph

/-- The product universal property supplies the required generic-fiber iso. -/
def productModelIso {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) (MX MY : C) [HasBinaryProduct MX MY]
    [PreservesLimit (pair MX MY) G] {X Y : D}
    (eX : G.obj MX ≅ X) (eY : G.obj MY ≅ Y)
    (c : BinaryFan X Y) (hc : IsLimit c) : G.obj (MX ⨯ MY) ≅ c.pt :=
  let h := isLimitOfHasBinaryProductOfPreservesLimit G MX MY
  let hX := BinaryFan.isLimitCompLeftIso _ eX.hom h
  let hY := BinaryFan.isLimitCompRightIso _ eY.hom hX
  hY.conePointUniqueUpToIso hc

@[reassoc (attr := simp)]
private lemma productModelIso_hom_fst {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) (MX MY : C) [HasBinaryProduct MX MY]
    [PreservesLimit (pair MX MY) G] {X Y : D}
    (eX : G.obj MX ≅ X) (eY : G.obj MY ≅ Y)
    (c : BinaryFan X Y) (hc : IsLimit c) :
    (productModelIso G MX MY eX eY c hc).hom ≫ c.fst =
      G.map prod.fst ≫ eX.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ hc ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
private lemma productModelIso_hom_snd {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) (MX MY : C) [HasBinaryProduct MX MY]
    [PreservesLimit (pair MX MY) G] {X Y : D}
    (eX : G.obj MX ≅ X) (eY : G.obj MY ≅ Y)
    (c : BinaryFan X Y) (hc : IsLimit c) :
    (productModelIso G MX MY eX eY c hc).hom ≫ c.snd =
      G.map prod.snd ≫ eY.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ hc ⟨WalkingPair.right⟩

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- At a common factor base, use the actual model product and then change the
independently specified spread of its generic fiber. -/
private lemma curve_spread_product_sameBase
    (S U : Finset (AlgebraicCurve.Place k F))
    (MX MY : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (MP : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType MX.hom] [QuasiCompact MX.hom]
    [LocallyOfFiniteType MY.hom] [QuasiCompact MY.hom]
    [LocallyOfFiniteType MP.hom] [QuasiCompact MP.hom]
    (X Y : Over (Spec (CommRingCat.of F)))
    (eX : curvePlaceModelGenericFiber k F S MX ≅ X)
    (eY : curvePlaceModelGenericFiber k F S MY ≅ Y)
    (c : BinaryFan X Y)
    (eP : curvePlaceModelGenericFiber k F U MP ≅ c.pt) (hc : IsLimit c) :
    @IsHomeomorph (CurvePlaceAdelePoints k F c.pt)
      (CurvePlaceAdelePoints k F X × CurvePlaceAdelePoints k F Y)
      (curvePlaceSpreadAdelePointTopology k F U MP c.pt eP)
      (@instTopologicalSpaceProd _ _
        (curvePlaceSpreadAdelePointTopology k F S MX X eX)
        (curvePlaceSpreadAdelePointTopology k F S MY Y eY))
      (fun p => (p ≫ c.fst, p ≫ c.snd)) := by
  let G := Over.pullback
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
  let eQ : curvePlaceModelGenericFiber k F S (MX ⨯ MY) ≅ c.pt :=
    productModelIso G MX MY eX eY c hc
  have hfinite := finiteType_overProd MX MY
  let : LocallyOfFiniteType (MX ⨯ MY).hom := hfinite.1
  let : QuasiCompact (MX ⨯ MY).hom := hfinite.2
  rw [curvePlaceSpreadTopologyIndependence k F U S MP (MX ⨯ MY) c.pt eP eQ]
  let : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  refine isHomeomorph_pointProduct_transport
    (curvePlaceSIntegers k F S) F (curvePlaceAdeleOver k F S) MX MY X Y c
    _ _ _ _ _ _
    (curvePlaceSpreadAdelePointHomeomorph k F S (MX ⨯ MY) c.pt eQ)
    (curvePlaceSpreadAdelePointHomeomorph k F S MX X eX)
    (curvePlaceSpreadAdelePointHomeomorph k F S MY Y eY) ?_ ?_ ?_
  · intro p
    change (curvePlaceGenericFiberAdelePointEquiv k F S (MX ⨯ MY) p ≫ eQ.hom) ≫
      c.fst = curvePlaceGenericFiberAdelePointEquiv k F S MX (p ≫ prod.fst) ≫ eX.hom
    rw [curvePlaceGenericFiberAdelePointEquiv_natural, Category.assoc]
    exact congrArg (fun q => curvePlaceGenericFiberAdelePointEquiv k F S (MX ⨯ MY) p ≫ q)
      (productModelIso_hom_fst G MX MY eX eY c hc)
  · intro p
    change (curvePlaceGenericFiberAdelePointEquiv k F S (MX ⨯ MY) p ≫ eQ.hom) ≫
      c.snd = curvePlaceGenericFiberAdelePointEquiv k F S MY (p ≫ prod.snd) ≫ eY.hom
    rw [curvePlaceGenericFiberAdelePointEquiv_natural, Category.assoc]
    exact congrArg (fun q => curvePlaceGenericFiberAdelePointEquiv k F S (MX ⨯ MY) p ≫ q)
      (productModelIso_hom_snd G MX MY eX eY c hc)
  · let Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))) := Over.mk (𝟙 _)
    let : LocallyOfFiniteType Z.hom := by change LocallyOfFiniteType (𝟙 _); infer_instance
    let : QuasiCompact Z.hom := by change QuasiCompact (𝟙 _); infer_instance
    let : IsSeparated Z.hom := by change IsSeparated (𝟙 _); infer_instance
    exact isHomeomorph_product_of_terminal (curvePlaceSIntegers k F S)
      (curvePlaceAdeleOver k F S) (curvePlaceFixedModelAdelePointTopology k F S) MX MY
      (adelicFixedModelPullback.1 k F S MX MY Z
        (Over.mkIdTerminal.from MX) (Over.mkIdTerminal.from MY)
        (IsPullback.of_is_product (prodIsProd MX MY) Over.mkIdTerminal).cone
        (IsPullback.of_is_product (prodIsProd MX MY) Over.mkIdTerminal).isLimit)


def curveProductGenericFiberCompIso
    (S : Finset (AlgebraicCurve.Place k F))
    (MX : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    {V : Finset (AlgebraicCurve.Place k F)} (hSV : S ⊆ V) :
    curvePlaceModelGenericFiber k F V (curvePlaceLevelModelBaseChange k F hSV MX) ≅
      curvePlaceModelGenericFiber k F S MX :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSV)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F V).subtype))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    (by rw [← Spec.map_comp]; rfl) MX

end Curve

/-- The ordinary product comparison for independent function-field spreads. -/
theorem curvePlaceSpreadProduct : CurvePlaceSpreadProductStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S T U MX MY MP _ _ _ _ _ _ X Y eX eY c eP hc
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
  let eXV := curveProductGenericFiberCompIso k F S MX hSV ≪≫ eX
  let eYV := curveProductGenericFiberCompIso k F T MY hTV ≪≫ eY
  rw [curvePlaceSpreadTopologyIndependence k F S V MX MXV X eX eXV,
    curvePlaceSpreadTopologyIndependence k F T V MY MYV Y eY eYV]
  exact curve_spread_product_sameBase k F V U MXV MYV MP X Y eXV eYV c eP hc

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- At a common factor base, use the actual model product and then change the
independently specified spread of its generic fiber. -/
private lemma number_spread_product_sameBase
    (S U : Finset (FinitePlace K))
    (MX MY : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (MP : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType MX.hom] [QuasiCompact MX.hom]
    [LocallyOfFiniteType MY.hom] [QuasiCompact MY.hom]
    [LocallyOfFiniteType MP.hom] [QuasiCompact MP.hom]
    (X Y : Over (Spec (CommRingCat.of K)))
    (eX : numberFieldModelGenericFiber K S MX ≅ X)
    (eY : numberFieldModelGenericFiber K S MY ≅ Y)
    (c : BinaryFan X Y)
    (eP : numberFieldModelGenericFiber K U MP ≅ c.pt) (hc : IsLimit c) :
    @IsHomeomorph (NumberFieldAdelePoints K c.pt)
      (NumberFieldAdelePoints K X × NumberFieldAdelePoints K Y)
      (numberFieldSpreadAdelePointTopology K U MP c.pt eP)
      (@instTopologicalSpaceProd _ _
        (numberFieldSpreadAdelePointTopology K S MX X eX)
        (numberFieldSpreadAdelePointTopology K S MY Y eY))
      (fun p => (p ≫ c.fst, p ≫ c.snd)) := by
  let G := Over.pullback
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
  let eQ : numberFieldModelGenericFiber K S (MX ⨯ MY) ≅ c.pt :=
    productModelIso G MX MY eX eY c hc
  have hfinite := finiteType_overProd MX MY
  let : LocallyOfFiniteType (MX ⨯ MY).hom := hfinite.1
  let : QuasiCompact (MX ⨯ MY).hom := hfinite.2
  rw [numberFieldSpreadTopologyIndependence K U S MP (MX ⨯ MY) c.pt eP eQ]
  let : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  refine isHomeomorph_pointProduct_transport
    ((S : Set (FinitePlace K)).integer K) K (numberFieldAdeleOver K S) MX MY X Y c
    _ _ _ _ _ _
    (numberFieldSpreadAdelePointHomeomorph K S (MX ⨯ MY) c.pt eQ)
    (numberFieldSpreadAdelePointHomeomorph K S MX X eX)
    (numberFieldSpreadAdelePointHomeomorph K S MY Y eY) ?_ ?_ ?_
  · intro p
    change (numberFieldGenericFiberAdelePointEquiv K S (MX ⨯ MY) p ≫ eQ.hom) ≫
      c.fst = numberFieldGenericFiberAdelePointEquiv K S MX (p ≫ prod.fst) ≫ eX.hom
    rw [numberFieldGenericFiberAdelePointEquiv_natural, Category.assoc]
    exact congrArg (fun q => numberFieldGenericFiberAdelePointEquiv K S (MX ⨯ MY) p ≫ q)
      (productModelIso_hom_fst G MX MY eX eY c hc)
  · intro p
    change (numberFieldGenericFiberAdelePointEquiv K S (MX ⨯ MY) p ≫ eQ.hom) ≫
      c.snd = numberFieldGenericFiberAdelePointEquiv K S MY (p ≫ prod.snd) ≫ eY.hom
    rw [numberFieldGenericFiberAdelePointEquiv_natural, Category.assoc]
    exact congrArg (fun q => numberFieldGenericFiberAdelePointEquiv K S (MX ⨯ MY) p ≫ q)
      (productModelIso_hom_snd G MX MY eX eY c hc)
  · let Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))) := Over.mk (𝟙 _)
    let : LocallyOfFiniteType Z.hom := by change LocallyOfFiniteType (𝟙 _); infer_instance
    let : QuasiCompact Z.hom := by change QuasiCompact (𝟙 _); infer_instance
    let : IsSeparated Z.hom := by change IsSeparated (𝟙 _); infer_instance
    exact isHomeomorph_product_of_terminal ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleOver K S) (numberFieldFixedModelAdelePointTopology K S) MX MY
      (adelicFixedModelPullback.2 K S MX MY Z
        (Over.mkIdTerminal.from MX) (Over.mkIdTerminal.from MY)
        (IsPullback.of_is_product (prodIsProd MX MY) Over.mkIdTerminal).cone
        (IsPullback.of_is_product (prodIsProd MX MY) Over.mkIdTerminal).isLimit)


def numberProductGenericFiberCompIso
    (S : Finset (FinitePlace K))
    (MX : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    {V : Finset (FinitePlace K)} (hSV : S ⊆ V) :
    numberFieldModelGenericFiber K V (numberFieldLevelModelBaseChange K hSV MX) ≅
      numberFieldModelGenericFiber K S MX :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSV)))
    (Spec.map (CommRingCat.ofHom ((V : Set (FinitePlace K)).integer K).toSubring.subtype))
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    (by rw [← Spec.map_comp]; rfl) MX


end NumberField

/-- The ordinary product comparison for independent number-field spreads. -/
theorem numberFieldSpreadProduct : NumberFieldSpreadProductStatement.{u} := by
  intro K _ _ S T U MX MY MP _ _ _ _ _ _ X Y eX eY c eP hc
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
  let eXV := numberProductGenericFiberCompIso K S MX hSV ≪≫ eX
  let eYV := numberProductGenericFiberCompIso K T MY hTV ≪≫ eY
  rw [numberFieldSpreadTopologyIndependence K S V MX MXV X eX eXV,
    numberFieldSpreadTopologyIndependence K T V MY MYV Y eY eYV]
  exact number_spread_product_sameBase K V U MXV MYV MP X Y eXV eYV c eP hc


/-- The exact product comparison in both arithmetic cases. -/
theorem adelicSpreadProduct : AdelicSpreadProductStatement.{u} :=
  ⟨curvePlaceSpreadProduct, numberFieldSpreadProduct⟩

end Langlands.Global
