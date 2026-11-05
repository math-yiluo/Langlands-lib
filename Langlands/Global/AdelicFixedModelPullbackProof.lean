import Langlands.Global.AdelicFixedModelPullbackStatement
import Langlands.Global.AdelicLevelModelPullbackProof
import Langlands.Global.AdelicFixedModelColimitOpenProof
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Constructions.SumProd

/-! # Pullbacks of full-adele fixed-model point spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Continuity can be tested along a jointly surjective family of open maps. -/
private theorem continuous_of_open_covering_maps
    {J B W : Type u} {V : J → Type u}
    [TopologicalSpace B] [TopologicalSpace W] [∀ j, TopologicalSpace (V j)]
    (q : ∀ j, V j → B) (hq : ∀ j, IsOpenMap (q j))
    (hcover : ∀ b, ∃ j v, q j v = b) (h : B → W)
    (hh : ∀ j, Continuous (h ∘ q j)) : Continuous h := by
  apply continuous_def.mpr
  intro U hU
  have heq : h ⁻¹' U = ⋃ j, q j '' ((h ∘ q j) ⁻¹' U) := by
    ext b
    constructor
    · intro hb
      obtain ⟨j, v, rfl⟩ := hcover b
      exact Set.mem_iUnion.mpr ⟨j, ⟨v, hb, rfl⟩⟩
    · intro hb
      obtain ⟨j, v, hv, rfl⟩ := Set.mem_iUnion.mp hb
      exact hv
  rw [heq]
  exact isOpen_iUnion fun j => hq j _ (hU.preimage (hh j))

/-- A natural family of point homeomorphisms transports pullback comparisons. -/
private theorem isHomeomorph_pullback_transport
    (C B A : Type u) [CommRing C] [CommRing B] [CommRing A]
    [Algebra C A] [Algebra B A]
    (G : Over (Spec (CommRingCat.of C)) ⥤ Over (Spec (CommRingCat.of B)))
    (τ : ∀ W : Over (Spec (CommRingCat.of C)), TopologicalSpace (RingPoint C W A))
    (σ : ∀ W : Over (Spec (CommRingCat.of B)), TopologicalSpace (RingPoint B W A))
    (e : ∀ W, @Homeomorph (RingPoint C W A) (RingPoint B (G.obj W) A)
      (τ W) (σ (G.obj W)))
    (he : ∀ {V W} (h : V ⟶ W) (p : RingPoint C V A),
      e W (p ≫ h) = e V p ≫ G.map h)
    {X Y Z : Over (Spec (CommRingCat.of C))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
    (hl : letI := σ (G.obj X)
      letI := σ (G.obj Y)
      @IsHomeomorph (RingPoint B (G.obj c.pt) A)
        {q : RingPoint B (G.obj X) A × RingPoint B (G.obj Y) A //
          q.1 ≫ G.map f = q.2 ≫ G.map g}
        (σ (G.obj c.pt)) inferInstance
        (affineSchemePullbackPointComparison B A (c.map G))) :
    letI := τ X
    letI := τ Y
    @IsHomeomorph (RingPoint C c.pt A)
      {q : RingPoint C X A × RingPoint C Y A // q.1 ≫ f = q.2 ≫ g}
      (τ c.pt) inferInstance (affineSchemePullbackPointComparison C A c) := by
  let := τ X
  let := τ Y
  let := τ c.pt
  let := σ (G.obj X)
  let := σ (G.obj Y)
  let := σ (G.obj c.pt)
  let E := ((e X).prodCongr (e Y)).subtype
    (p := fun q : RingPoint C X A × RingPoint C Y A => q.1 ≫ f = q.2 ≫ g)
    (q := fun q : RingPoint B (G.obj X) A × RingPoint B (G.obj Y) A =>
      q.1 ≫ G.map f = q.2 ≫ G.map g)
    (fun q => by
      change q.1 ≫ f = q.2 ≫ g ↔ e X q.1 ≫ G.map f = e Y q.2 ≫ G.map g
      rw [← he, ← he]
      exact (e Z).injective.eq_iff.symm)
  let H := IsHomeomorph.homeomorph _ hl
  have hfun : (⇑(((e c.pt).trans H).trans E.symm)) =
      affineSchemePullbackPointComparison C A c := by
    funext p
    apply E.injective
    change E (E.symm (H (e c.pt p))) = E (affineSchemePullbackPointComparison C A c p)
    rw [E.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact (he c.fst p).symm
    · exact (he c.snd p).symm
  rw [← hfun]
  exact (((e c.pt).trans H).trans E.symm).isHomeomorph

/-- Open arithmetic stages and equality reflection in the base pass pullbacks
to independently defined final point topologies. -/
private theorem isHomeomorph_finalRingPointPullback
    (C : Type u) [CommRing C]
    {J : Type u} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommAlgCat.{u} C)
    (d : Cocone D)
    (τ : ∀ W : Over (Spec (CommRingCat.of C)),
      ∀ j : J, TopologicalSpace (RingPoint C W (D.obj j)))
    {X Y Z : Over (Spec (CommRingCat.of C))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c)
    (hstage : ∀ j, letI := τ X j
      letI := τ Y j
      @IsHomeomorph (RingPoint C c.pt (D.obj j))
        {q : RingPoint C X (D.obj j) × RingPoint C Y (D.obj j) //
          q.1 ≫ f = q.2 ≫ g}
        (τ c.pt j) inferInstance (affineSchemePullbackPointComparison C (D.obj j) c))
    (hopen : ∀ j,
      @IsOpenMap _ _ (τ X j) (ringPointCoconeTopology C D X (τ X) d)
        (fun p : RingPoint C X (D.obj j) => p.changeRing (d.ι.app j).hom) ∧
      @IsOpenMap _ _ (τ Y j) (ringPointCoconeTopology C D Y (τ Y) d)
        (fun p : RingPoint C Y (D.obj j) => p.changeRing (d.ι.app j).hom))
    (hinj : ∀ j, Function.Injective
      (fun p : RingPoint C Z (D.obj j) => p.changeRing (d.ι.app j).hom))
    (hcoverX : ∀ x : RingPoint C X d.pt, ∃ (j : J) (p : RingPoint C X (D.obj j)),
      p.changeRing (d.ι.app j).hom = x)
    (hcoverY : ∀ y : RingPoint C Y d.pt, ∃ (j : J) (p : RingPoint C Y (D.obj j)),
      p.changeRing (d.ι.app j).hom = y) :
    letI := ringPointCoconeTopology C D X (τ X) d
    letI := ringPointCoconeTopology C D Y (τ Y) d
    @IsHomeomorph (RingPoint C c.pt d.pt)
      {q : RingPoint C X d.pt × RingPoint C Y d.pt // q.1 ≫ f = q.2 ≫ g}
      (ringPointCoconeTopology C D c.pt (τ c.pt) d) inferInstance
      (affineSchemePullbackPointComparison C d.pt c) := by
  let := ringPointCoconeTopology C D X (τ X) d
  let := ringPointCoconeTopology C D Y (τ Y) d
  let := ringPointCoconeTopology C D c.pt (τ c.pt) d
  let (j : J) := τ X j
  let (j : J) := τ Y j
  let (j : J) := τ c.pt j
  let B := {q : RingPoint C X d.pt × RingPoint C Y d.pt // q.1 ≫ f = q.2 ≫ g}
  let V := fun j => {q : RingPoint C X (D.obj j) × RingPoint C Y (D.obj j) //
    q.1 ≫ f = q.2 ≫ g}
  let Q : ∀ j, V j → B := fun j q =>
    ⟨(q.val.1.changeRing (d.ι.app j).hom, q.val.2.changeRing (d.ι.app j).hom), by
      change (ringTestMap C _ ≫ q.val.1) ≫ f = (ringTestMap C _ ≫ q.val.2) ≫ g
      rw [Category.assoc, Category.assoc, q.property]⟩
  have hQcont : ∀ j, Continuous (Q j) := by
    intro j
    exact (((ringPointCoconeTopology_continuous_ι C D X (τ X) d j).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
      ((ringPointCoconeTopology_continuous_ι C D Y (τ Y) d j).comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  have hQopen : ∀ j, IsOpenMap (Q j) := by
    intro j
    let P : RingPoint C X (D.obj j) × RingPoint C Y (D.obj j) →
        RingPoint C X d.pt × RingPoint C Y d.pt :=
      Prod.map (fun p => p.changeRing (d.ι.app j).hom)
        (fun p => p.changeRing (d.ι.app j).hom)
    let W : Set (RingPoint C X d.pt × RingPoint C Y d.pt) :=
      {q | q.1 ≫ f = q.2 ≫ g}
    have hs : {q : RingPoint C X (D.obj j) × RingPoint C Y (D.obj j) |
        q.1 ≫ f = q.2 ≫ g} = P ⁻¹' W := by
      ext q
      change q.1 ≫ f = q.2 ≫ g ↔
        q.1.changeRing (d.ι.app j).hom ≫ f =
          q.2.changeRing (d.ι.app j).hom ≫ g
      change q.1 ≫ f = q.2 ≫ g ↔
        ringTestMap C _ ≫ q.1 ≫ f = ringTestMap C _ ≫ q.2 ≫ g
      exact (hinj j).eq_iff.symm
    let E := Homeomorph.setCongr hs
    change IsOpenMap (W.restrictPreimage P ∘ E)
    exact (((hopen j).1.prodMap (hopen j).2).restrictPreimage W).comp E.isOpenMap
  have hcompat : ∀ j (x : RingPoint C X (D.obj j)) (y : RingPoint C Y (D.obj j)),
      x.changeRing (d.ι.app j).hom ≫ f = y.changeRing (d.ι.app j).hom ≫ g →
      x ≫ f = y ≫ g := by
    intro j x y h
    apply hinj j
    exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
  have hnat : ∀ (W : Over (Spec (CommRingCat.of C))) {i j : J}
      (a : i ⟶ j) (p : RingPoint C W (D.obj i)),
      (p.changeRing (D.map a).hom).changeRing (d.ι.app j).hom =
        p.changeRing (d.ι.app i).hom := by
    intro W i j a p
    exact ConcreteCategory.congr_hom ((ringPointCocone C D W d).w a) p
  have hQcover : ∀ q : B, ∃ j v, Q j v = q := by
    intro q
    obtain ⟨i, x, hx⟩ := hcoverX q.val.1
    obtain ⟨j, y, hy⟩ := hcoverY q.val.2
    obtain ⟨l, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs i j
    let xl := x.changeRing (D.map a).hom
    let yl := y.changeRing (D.map b).hom
    have hxl : xl.changeRing (d.ι.app l).hom = q.val.1 := (hnat X a x).trans hx
    have hyl : yl.changeRing (d.ι.app l).hom = q.val.2 := (hnat Y b y).trans hy
    refine ⟨l, ⟨(xl, yl), hcompat l xl yl ?_⟩, ?_⟩
    · rw [hxl, hyl]
      exact q.property
    · apply Subtype.ext
      exact Prod.ext hxl hyl
  let E := affineSchemePullbackPointEquiv C d.pt c hc
  have hto : Continuous E := by
    apply (ringPointCoconeTopology_continuous_iff C D c.pt (τ c.pt) d E).2
    intro j
    refine ((hQcont j).comp (hstage j).continuous).congr ?_
    intro p
    apply Subtype.ext
    exact Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  have hinv : Continuous E.symm := by
    apply continuous_of_open_covering_maps Q hQopen hQcover E.symm
    intro j
    let H := IsHomeomorph.homeomorph _ (hstage j)
    have heq : E.symm ∘ Q j =
        (fun p : RingPoint C c.pt (D.obj j) => p.changeRing (d.ι.app j).hom) ∘ H.symm := by
      funext q
      apply E.injective
      dsimp only [Function.comp_apply]
      rw [E.apply_symm_apply]
      apply Subtype.ext
      apply Prod.ext
      · change q.val.1.changeRing (d.ι.app j).hom =
          (H.symm q).changeRing (d.ι.app j).hom ≫ c.fst
        have h := congrArg (fun z => z.val.1) (H.apply_symm_apply q)
        exact (congrArg (fun p => p.changeRing (d.ι.app j).hom) h).symm.trans
          (Category.assoc _ _ _).symm
      · change q.val.2.changeRing (d.ι.app j).hom =
          (H.symm q).changeRing (d.ι.app j).hom ≫ c.snd
        have h := congrArg (fun z => z.val.2) (H.apply_symm_apply q)
        exact (congrArg (fun p => p.changeRing (d.ι.app j).hom) h).symm.trans
          (Category.assoc _ _ _).symm
    rw [heq]
    exact (ringPointCoconeTopology_continuous_ι C D c.pt (τ c.pt) d j).comp H.symm.continuous
  exact ({ toEquiv := E, continuous_toFun := hto, continuous_invFun := hinv } :
    RingPoint C c.pt d.pt ≃ₜ B).isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The existing curve-place level comparison transports to the fixed scalar base. -/
private theorem curvePlaceFixedModelStage_pullback
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    {X Y Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c)
    (T : AdelicLevelIndexAbove S) :
    letI := curvePlaceFixedModelStageTopology k F S X T
    letI := curvePlaceFixedModelStageTopology k F S Y T
    @IsHomeomorph
      (RingPoint (curvePlaceSIntegers k F S) c.pt (curvePlaceAdeleLevelOver k F S T))
      {q : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) ×
        RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T) //
          q.1 ≫ f = q.2 ≫ g}
      (curvePlaceFixedModelStageTopology k F S c.pt T) inferInstance
      (affineSchemePullbackPointComparison
        (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F S T) c) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let G := Over.pullback
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))
  have hcT : IsLimit (c.map G) :=
    (c.isLimitMapConeEquiv G) (isLimitOfPreserves G hc)
  apply isHomeomorph_pullback_transport
    (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
    (curvePlaceAdeleLevelOver k F S T) G
    (fun W => curvePlaceFixedModelStageTopology k F S W T)
    (curvePlaceLevelModelPointTopology k F T.val)
    (fun W => curvePlaceFixedModelPointHomeomorph k F S W T)
    (fun h p => ringPointBaseChangeEquiv_natural
      (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) h p) c
  exact adelicLevelModelPullback.1 k F T.val
    (G.obj X) (G.obj Y) (G.obj Z) (G.map f) (G.map g) (c.map G) hcT

/-- The existing full number-field level comparison transports to the fixed scalar base. -/
private theorem numberFieldFixedModelStage_pullback
    (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    {X Y Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c)
    (T : AdelicLevelIndexAbove S) :
    letI := numberFieldFixedModelStageTopology K S X T
    letI := numberFieldFixedModelStageTopology K S Y T
    @IsHomeomorph
      (RingPoint ((S : Set (FinitePlace K)).integer K) c.pt (numberFieldAdeleLevelOver K S T))
      {q : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) ×
        RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T) //
          q.1 ≫ f = q.2 ≫ g}
      (numberFieldFixedModelStageTopology K S c.pt T) inferInstance
      (affineSchemePullbackPointComparison
        ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) c) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let G := Over.pullback
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))
  have hcT : IsLimit (c.map G) :=
    (c.isLimitMapConeEquiv G) (isLimitOfPreserves G hc)
  apply isHomeomorph_pullback_transport
    ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOver K S T) G
    (fun W => numberFieldFixedModelStageTopology K S W T)
    (numberFieldLevelModelPointTopology K T.val)
    (fun W => numberFieldFixedModelPointHomeomorph K S W T)
    (fun h p => ringPointBaseChangeEquiv_natural
      ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) h p) c
  exact adelicLevelModelPullback.2 K T.val
    (G.obj X) (G.obj Y) (G.obj Z) (G.map f) (G.map g) (c.map G) hcT

/-- The exact pullback target for full-adele fixed-model point spaces. -/
theorem adelicFixedModelPullback : AdelicFixedModelPullbackStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S X Y Z _ _ _ _ _ _ _ f g c hc
    have hx := adelicFixedModelColimitOpen.1 k F S X
    have hy := adelicFixedModelColimitOpen.1 k F S Y
    have hz := adelicFixedModelColimitOpen.1 k F S Z
    exact isHomeomorph_finalRingPointPullback (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S)
      (fun W T => curvePlaceFixedModelStageTopology k F S W T) c hc
      (curvePlaceFixedModelStage_pullback k F S c hc)
      (fun T => ⟨(hx.1 T).2, (hy.1 T).2⟩)
      (fun T => by
        let := curvePlaceFixedModelStageTopology k F S Z T
        let := curvePlaceFixedModelAdelePointTopology k F S Z
        exact (hz.2.2 T).injective)
      (adelicFixedModelFiniteType.1 k F S X).1
      (adelicFixedModelFiniteType.1 k F S Y).1
  · intro K _ _ S X Y Z _ _ _ _ _ _ _ f g c hc
    have hx := adelicFixedModelColimitOpen.2 K S X
    have hy := adelicFixedModelColimitOpen.2 K S Y
    have hz := adelicFixedModelColimitOpen.2 K S Z
    exact isHomeomorph_finalRingPointPullback ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S)
      (fun W T => numberFieldFixedModelStageTopology K S W T) c hc
      (numberFieldFixedModelStage_pullback K S c hc)
      (fun T => ⟨(hx.1 T).2, (hy.1 T).2⟩)
      (fun T => by
        let := numberFieldFixedModelStageTopology K S Z T
        let := numberFieldFixedModelAdelePointTopology K S Z
        exact (hz.2.2 T).injective)
      (adelicFixedModelFiniteType.2 K S X).1
      (adelicFixedModelFiniteType.2 K S Y).1

end Langlands.Global
