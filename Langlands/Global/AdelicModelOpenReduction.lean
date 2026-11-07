import Langlands.Global.AdelicModelOpenReductionStatement
import Langlands.Global.AdelicFixedModelLocalProductTopology
import Langlands.Global.AdelicFixedModelColimitOpenProof
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPointComparisonProof

/-! # From local openness and eventual surjectivity to actual adelic openness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Local open point maps, surjective at all but finitely many factors, induce
an open map on the actual product-ring points with their local product topology. -/
theorem isOpenMap_localProduct_postcomp
    (A : Type u) [CommRing A] {ι : Type u} (R : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, IsLocalRing (R i)] [∀ i, IsOpenUnits (R i)]
    {X Y : Over (Spec (CommRingCat.of A))}
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] (f : X ⟶ Y)
    (ho : ∀ i, @IsOpenMap _ _ (schemePointTopology A X (R i))
      (schemePointTopology A Y (R i))
      (fun p : RingPoint A X (R i) => p ≫ f))
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (fun p : RingPoint A X (R i) => p ≫ f)) :
    @IsOpenMap _ _ (localProductPointTopology A R X)
      (localProductPointTopology A R Y)
      (fun p : RingPoint A X (∀ i, R i) => p ≫ f) := by
  let := localProductPointTopology A R X
  let := localProductPointTopology A R Y
  let : ∀ i, TopologicalSpace (RingPoint A X (R i)) :=
    fun i => schemePointTopology A X (R i)
  let : ∀ i, TopologicalSpace (RingPoint A Y (R i)) :=
    fun i => schemePointTopology A Y (R i)
  have hX : IsHomeomorph (productPointMap A R X) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨⟨productPointMap_isInducing_localProductPointTopology A R X,
        productPointMap_injective A R X⟩, productPointMap_surjective A R X⟩
  have hY : IsHomeomorph (productPointMap A R Y) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨⟨productPointMap_isInducing_localProductPointTopology A R Y,
        productPointMap_injective A R Y⟩, productPointMap_surjective A R Y⟩
  have hprod : @IsOpenMap (∀ i, RingPoint A X (R i)) (∀ i, RingPoint A Y (R i))
      inferInstance inferInstance (fun p i => p i ≫ f) :=
    IsOpenMap.piMap (A := fun i => RingPoint A X (R i))
      (B := fun i => RingPoint A Y (R i)) ho hs
  apply (hY.homeomorph (productPointMap A R Y)).comp_isOpenMap_iff.mp
  change IsOpenMap (productPointMap A R Y ∘ fun p : RingPoint A X (∀ i, R i) =>
    (p ≫ f : RingPoint A Y (∀ i, R i)))
  have hn : productPointMap A R Y ∘ (fun p : RingPoint A X (∀ i, R i) =>
        (p ≫ f : RingPoint A Y (∀ i, R i))) =
      (fun p : ∀ i, RingPoint A X (R i) =>
        fun i => (p i ≫ f : RingPoint A Y (R i))) ∘
        productPointMap A R X := by
    funext p i
    exact productPointMap_natural A R f p i
  rw [hn]
  exact hprod.comp hX.isOpenMap

/-- Continuous source stage maps covering the actual cocone points, open target
stage maps, and open stagewise postcomposition imply openness on cocone points. -/
theorem isOpenMap_ringPointCocone_postcomp
    (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
    (D : J ⥤ CommAlgCat.{u} A) (c : Cocone D)
    {X Y : Over (Spec (CommRingCat.of A))} (f : X ⟶ Y)
    (τX : ∀ j, TopologicalSpace (RingPoint A X (D.obj j)))
    (τY : ∀ j, TopologicalSpace (RingPoint A Y (D.obj j)))
    (hcover : ∀ p : RingPoint A X c.pt,
      ∃ (j : J) (q : RingPoint A X (D.obj j)),
        q.changeRing (c.ι.app j).hom = p)
    (hstage : ∀ j, @IsOpenMap _ _ (τX j) (τY j)
      (fun p : RingPoint A X (D.obj j) => p ≫ f))
    (hι : ∀ j, @IsOpenMap _ _ (τY j) (ringPointCoconeTopology A D Y τY c)
      (fun p : RingPoint A Y (D.obj j) => p.changeRing (c.ι.app j).hom)) :
    @IsOpenMap _ _ (ringPointCoconeTopology A D X τX c)
      (ringPointCoconeTopology A D Y τY c)
      (fun p : RingPoint A X c.pt => p ≫ f) := by
  let : ∀ j, TopologicalSpace (RingPoint A X (D.obj j)) := τX
  let : ∀ j, TopologicalSpace (RingPoint A Y (D.obj j)) := τY
  let := ringPointCoconeTopology A D X τX c
  let := ringPointCoconeTopology A D Y τY c
  let ιX : (Σ j, RingPoint A X (D.obj j)) → RingPoint A X c.pt :=
    fun p => p.2.changeRing (c.ι.app p.1).hom
  have hc : Continuous ιX :=
    continuous_sigma (fun j => ringPointCoconeTopology_continuous_ι A D X τX c j)
  have hs : Function.Surjective ιX := by
    intro p
    obtain ⟨j, q, hq⟩ := hcover p
    exact ⟨⟨j, q⟩, hq⟩
  apply IsOpenMap.of_comp hc hs
  apply isOpenMap_sigma.mpr
  intro j
  change @IsOpenMap (RingPoint A X (D.obj j)) (RingPoint A Y c.pt)
    (τX j) (ringPointCoconeTopology A D Y τY c) (fun p =>
    (p.changeRing (c.ι.app j).hom ≫ f : RingPoint A Y c.pt))
  have hn : (fun p : RingPoint A X (D.obj j) =>
      (p.changeRing (c.ι.app j).hom ≫ f : RingPoint A Y c.pt)) =
      (fun p : RingPoint A Y (D.obj j) => p.changeRing (c.ι.app j).hom) ∘
        (fun p : RingPoint A X (D.obj j) =>
          (p ≫ f : RingPoint A Y (D.obj j))) := by
    funext p
    exact Category.assoc _ _ _
  rw [hn]
  exact (hι j).comp (hstage j)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open scoped Langlands.Global.FixedModelLocalProduct

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (AlgebraicCurve.Place k F))
  {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
  [QuasiCompact X.hom] [IsSeparated X.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- An original fixed-base function-field stage map is open under the actual
local openness and cofinite-surjectivity hypotheses at that enlarged level. -/
theorem curvePlaceFixedModelStage_isOpenMap
    (T : AdelicLevelIndexAbove S)
    (ho : ∀ i, @IsOpenMap _ _
      (schemePointTopology (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i))
      (schemePointTopology (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f))
    (hs : ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f)) :
    @IsOpenMap _ _ (curvePlaceFixedModelStageTopology k F S X T)
      (curvePlaceFixedModelStageTopology k F S Y T)
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
        p ≫ f) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceFixedModelStageTopology k F S Y T
  let := localProductPointTopology (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F T.val) X
  let := localProductPointTopology (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F T.val) Y
  let hX := FixedModelLocalProduct.curveStageHomeomorph k F S T X
  let hY := FixedModelLocalProduct.curveStageHomeomorph k F S T Y
  have hp := isOpenMap_localProduct_postcomp (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F T.val) f ho hs
  apply hY.comp_isOpenMap_iff.mp
  have hn : hY ∘ (fun p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S T) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y
          (curvePlaceAdeleLevelOver k F S T))) =
      (fun p : RingPoint (curvePlaceSIntegers k F S) X
        (∀ i, CurvePlaceLevelFactor k F T.val i) =>
          (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y
            (∀ i, CurvePlaceLevelFactor k F T.val i))) ∘ hX := by
    funext p
    exact FixedModelLocalProduct.curveStageHomeomorph_natural k F S T X f p
  change IsOpenMap (hY ∘ fun p : RingPoint (curvePlaceSIntegers k F S) X
    (curvePlaceAdeleLevelOver k F S T) =>
      (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y
        (curvePlaceAdeleLevelOver k F S T)))
  rw [hn]
  exact hp.comp hX.isOpenMap

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

/-- Local open maps and cofinite surjectivity at each actual arithmetic stage
give openness on the full function-field adelic model-point space. -/
theorem curvePlaceFixedModelAdele_isOpenMap_of_local
    (ho : ∀ (T : AdelicLevelIndexAbove S) i, @IsOpenMap _ _
      (schemePointTopology (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i))
      (schemePointTopology (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f))
    (hs : ∀ T : AdelicLevelIndexAbove S, ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f)) :
    @IsOpenMap _ _ (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S Y)
      (fun p : CurvePlaceFixedModelAdelePoints k F S X => p ≫ f) :=
  isOpenMap_ringPointCocone_postcomp (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S) f
    (curvePlaceFixedModelStageTopology k F S X)
    (curvePlaceFixedModelStageTopology k F S Y)
    (adelicFixedModelFiniteType.1 k F S X).1
    (fun T => curvePlaceFixedModelStage_isOpenMap k F S f T (ho T) (hs T))
    (fun T => ((adelicFixedModelColimitOpen.1 k F S Y).1 T).2)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K))
  {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
  [QuasiCompact X.hom] [IsSeparated X.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The corresponding fixed-base number-field stage map includes all original
infinite factors as well as the finite local and integral factors. -/
theorem numberFieldFixedModelStage_isOpenMap
    (T : AdelicLevelIndexAbove S)
    (ho : ∀ i, @IsOpenMap _ _
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i))
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) Y
        (NumberFieldLevelFactor K T.val i))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f))
    (hs : ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f)) :
    @IsOpenMap _ _ (numberFieldFixedModelStageTopology K S X T)
      (numberFieldFixedModelStageTopology K S Y T)
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevelOver K S T) => p ≫ f) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldFixedModelStageTopology K S Y T
  let := localProductPointTopology ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K T.val) X
  let := localProductPointTopology ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K T.val) Y
  let hX := FixedModelLocalProduct.numberFieldStageHomeomorph K S T X
  let hY := FixedModelLocalProduct.numberFieldStageHomeomorph K S T Y
  have hp := isOpenMap_localProduct_postcomp ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K T.val) f ho hs
  apply hY.comp_isOpenMap_iff.mp
  have hn : hY ∘ (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevelOver K S T) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevelOver K S T))) =
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (∀ i, NumberFieldLevelFactor K T.val i) =>
          (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
            (∀ i, NumberFieldLevelFactor K T.val i))) ∘ hX := by
    funext p
    exact FixedModelLocalProduct.numberFieldStageHomeomorph_natural K S T X f p
  change IsOpenMap (hY ∘ fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
    (numberFieldAdeleLevelOver K S T) =>
      (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
        (numberFieldAdeleLevelOver K S T)))
  rw [hn]
  exact hp.comp hX.isOpenMap

variable [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

/-- Actual local openness and cofinite surjectivity give openness on the full
number-field adelic model-point space, retaining every infinite factor. -/
theorem numberFieldFixedModelAdele_isOpenMap_of_local
    (ho : ∀ (T : AdelicLevelIndexAbove S) i, @IsOpenMap _ _
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i))
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) Y
        (NumberFieldLevelFactor K T.val i))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f))
    (hs : ∀ T : AdelicLevelIndexAbove S, ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f)) :
    @IsOpenMap _ _ (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldFixedModelAdelePointTopology K S Y)
      (fun p : NumberFieldFixedModelAdelePoints K S X => p ≫ f) :=
  isOpenMap_ringPointCocone_postcomp ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S) f
    (numberFieldFixedModelStageTopology K S X)
    (numberFieldFixedModelStageTopology K S Y)
    (adelicFixedModelFiniteType.2 K S X).1
    (fun T => numberFieldFixedModelStage_isOpenMap K S f T (ho T) (hs T))
    (fun T => ((adelicFixedModelColimitOpen.2 K S Y).1 T).2)

end NumberField

/-- The exact conjunction of the actual function-field and full number-field
local-to-adelic openness reductions. -/
theorem adelicModelOpenReduction : AdelicModelOpenReductionStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S X Y _ _ _ _ _ _ f ho hs
    exact curvePlaceFixedModelAdele_isOpenMap_of_local k F S f ho hs
  · intro K _ _ S X Y _ _ _ _ _ _ f ho hs
    exact numberFieldFixedModelAdele_isOpenMap_of_local K S f ho hs

end Langlands.Global
