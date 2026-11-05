import Langlands.Global.AdelicSpreadStabilizationStatement
import Langlands.Global.AdelicSpreadCompactnessProof
import Langlands.Global.AdelicSpreadStageOpenProof
import Langlands.Global.AdelicSpreadEventualSeparationProof
import Langlands.Global.AdelicFixedModelInitialSetTopologyProof

/-! # Eventual stabilization of the actual arithmetic adelic stages -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Compactness bounds the open stage cover, and eventual separatedness makes
all stages beyond a second bound injective. -/
theorem curvePlaceSpreadStabilization : CurvePlaceSpreadStabilizationStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S X _ _ Y e _
  classical
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let : CompactSpace (CurvePlaceAdelePoints k F Y) :=
    curvePlaceSpreadCompactness k F S X Y e
  let i := fun (T : AdelicLevelIndexAbove S)
      (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) =>
    curvePlaceSpreadAdelePointEquiv k F S X Y e
      (p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom)
  have hmono : Monotone (fun T => Set.range (i T)) := by
    intro T U hTU p hp
    obtain ⟨q, rfl⟩ := hp
    refine ⟨q.changeRing (curvePlaceAdeleLevelOverMap k F S hTU).hom, ?_⟩
    apply congrArg (curvePlaceSpreadAdelePointEquiv k F S X Y e)
    exact ConcreteCategory.congr_hom
      ((ringPointCocone (curvePlaceSIntegers k F S)
        (curvePlaceAdeleLevelOverDiagram k F S) X
        (curvePlaceAdeleOverCocone k F S)).w (homOfLE hTU)) q
  have hopen : ∀ T, IsOpen (Set.range (i T)) := by
    intro T
    let := curvePlaceFixedModelStageTopology k F S X T
    have h := curvePlaceSpreadStageOpen k F S S X X Y e e T
    simpa only [Set.image_univ] using h.2.1 Set.univ isOpen_univ
  have hcover : Set.univ ⊆ ⋃ T, Set.range (i T) := by
    intro p _
    obtain ⟨T, q, hq⟩ := (adelicFixedModelFiniteType.1 k F S X).1
      ((curvePlaceSpreadAdelePointEquiv k F S X Y e).symm p)
    refine Set.mem_iUnion.mpr ⟨T, q, ?_⟩
    change curvePlaceSpreadAdelePointEquiv k F S X Y e
      (q.changeRing (curvePlaceAdeleLevelOverι k F S T).hom) = p
    rw [hq, Equiv.apply_symm_apply]
  obtain ⟨P, hP⟩ := isCompact_univ.elim_directed_cover
    (fun T => Set.range (i T)) hopen hcover (by
      intro T U
      let V : AdelicLevelIndexAbove S :=
        ⟨T.val ∪ U.val, T.property.trans Finset.subset_union_left⟩
      exact ⟨V, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩)
  have hsep : IsSeparated (curvePlaceModelGenericFiber k F S X).hom := by
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨Q, hQ⟩ := (curvePlaceSpreadEventualSeparation k F S X).mp hsep
  let XQ := curvePlaceLevelModelBaseChange k F Q.property X
  let : LocallyOfFiniteType XQ.hom := by
    dsimp [XQ, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XQ.hom := by
    dsimp [XQ, curvePlaceLevelModelBaseChange]
    infer_instance
  let : IsSeparated XQ.hom := hQ
  let T : AdelicLevelIndexAbove S :=
    ⟨P.val ∪ Q.val, P.property.trans Finset.subset_union_left⟩
  refine ⟨T, ?_⟩
  intro U hTU
  let := curvePlaceFixedModelStageTopology k F S X U
  have hPU : P ≤ U := Finset.subset_union_left.trans hTU
  have hQU : Q ≤ U := Finset.subset_union_right.trans hTU
  let V : AdelicLevelIndexAbove Q.val := ⟨U.val, hQU⟩
  let := curvePlaceFixedModelStageTopology k F Q.val XQ V
  let := curvePlaceFixedModelAdelePointTopology k F Q.val XQ
  let h := curvePlaceFixedModelInitialSetStageHomeomorph k F Q.property X V
  have hj := (adelicFixedModelColimitOpen.1 k F Q.val XQ).2.2 V
  have hinj : Function.Injective (i U) := by
    intro p q hpq
    apply h.injective
    apply hj.injective
    have hpq' := (curvePlaceSpreadAdelePointEquiv k F S X Y e).injective hpq
    have heq := congrArg (curvePlaceFixedModelInitialSetEquiv k F Q.property X) hpq'
    exact (curvePlaceFixedModelInitialSetStageHomeomorph_natural k F Q.property X V p).symm.trans
      (heq.trans (curvePlaceFixedModelInitialSetStageHomeomorph_natural k F Q.property X V q))
  have hsurj : Function.Surjective (i U) := by
    intro p
    exact hmono hPU (hP (Set.mem_univ p))
  have ho := curvePlaceSpreadStageOpen k F S S X X Y e e U
  exact ⟨ho.1, ho.2.1, hinj, hsurj⟩

/-- The full number-field proof uses the same directed cover and rebasing
argument, with all infinite completions retained in each stage. -/
theorem numberFieldSpreadStabilization : NumberFieldSpreadStabilizationStatement.{u} := by
  intro K _ _ S X _ _ Y e _
  classical
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let : CompactSpace (NumberFieldAdelePoints K Y) :=
    numberFieldSpreadCompactness K S X Y e
  let i := fun (T : AdelicLevelIndexAbove S)
      (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) =>
    numberFieldSpreadAdelePointEquiv K S X Y e
      (p.changeRing (numberFieldAdeleLevelOverι K S T).hom)
  have hmono : Monotone (fun T => Set.range (i T)) := by
    intro T U hTU p hp
    obtain ⟨q, rfl⟩ := hp
    refine ⟨q.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom, ?_⟩
    apply congrArg (numberFieldSpreadAdelePointEquiv K S X Y e)
    exact ConcreteCategory.congr_hom
      ((ringPointCocone ((S : Set (FinitePlace K)).integer K)
        (numberFieldAdeleLevelOverDiagram K S) X
        (numberFieldAdeleOverCocone K S)).w (homOfLE hTU)) q
  have hopen : ∀ T, IsOpen (Set.range (i T)) := by
    intro T
    let := numberFieldFixedModelStageTopology K S X T
    have h := numberFieldSpreadStageOpen K S S X X Y e e T
    simpa only [Set.image_univ] using h.2.1 Set.univ isOpen_univ
  have hcover : Set.univ ⊆ ⋃ T, Set.range (i T) := by
    intro p _
    obtain ⟨T, q, hq⟩ := (adelicFixedModelFiniteType.2 K S X).1
      ((numberFieldSpreadAdelePointEquiv K S X Y e).symm p)
    refine Set.mem_iUnion.mpr ⟨T, q, ?_⟩
    change numberFieldSpreadAdelePointEquiv K S X Y e
      (q.changeRing (numberFieldAdeleLevelOverι K S T).hom) = p
    rw [hq, Equiv.apply_symm_apply]
  obtain ⟨P, hP⟩ := isCompact_univ.elim_directed_cover
    (fun T => Set.range (i T)) hopen hcover (by
      intro T U
      let V : AdelicLevelIndexAbove S :=
        ⟨T.val ∪ U.val, T.property.trans Finset.subset_union_left⟩
      exact ⟨V, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩)
  have hsep : IsSeparated (numberFieldModelGenericFiber K S X).hom := by
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨Q, hQ⟩ := (numberFieldSpreadEventualSeparation K S X).mp hsep
  let XQ := numberFieldLevelModelBaseChange K Q.property X
  let : LocallyOfFiniteType XQ.hom := by
    dsimp [XQ, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XQ.hom := by
    dsimp [XQ, numberFieldLevelModelBaseChange]
    infer_instance
  let : IsSeparated XQ.hom := hQ
  let T : AdelicLevelIndexAbove S :=
    ⟨P.val ∪ Q.val, P.property.trans Finset.subset_union_left⟩
  refine ⟨T, ?_⟩
  intro U hTU
  let := numberFieldFixedModelStageTopology K S X U
  have hPU : P ≤ U := Finset.subset_union_left.trans hTU
  have hQU : Q ≤ U := Finset.subset_union_right.trans hTU
  let V : AdelicLevelIndexAbove Q.val := ⟨U.val, hQU⟩
  let := numberFieldFixedModelStageTopology K Q.val XQ V
  let := numberFieldFixedModelAdelePointTopology K Q.val XQ
  let h := numberFieldFixedModelInitialSetStageHomeomorph K Q.property X V
  have hj := (adelicFixedModelColimitOpen.2 K Q.val XQ).2.2 V
  have hinj : Function.Injective (i U) := by
    intro p q hpq
    apply h.injective
    apply hj.injective
    have hpq' := (numberFieldSpreadAdelePointEquiv K S X Y e).injective hpq
    have heq := congrArg (numberFieldFixedModelInitialSetEquiv K Q.property X) hpq'
    exact (numberFieldFixedModelInitialSetStageHomeomorph_natural K Q.property X V p).symm.trans
      (heq.trans (numberFieldFixedModelInitialSetStageHomeomorph_natural K Q.property X V q))
  have hsurj : Function.Surjective (i U) := by
    intro p
    exact hmono hPU (hP (Set.mem_univ p))
  have ho := numberFieldSpreadStageOpen K S S X X Y e e U
  exact ⟨ho.1, ho.2.1, hinj, hsurj⟩

/-- The exact eventual-stage assertion in both global-field characteristics. -/
theorem adelicSpreadStabilization : AdelicSpreadStabilizationStatement.{u} :=
  ⟨curvePlaceSpreadStabilization, numberFieldSpreadStabilization⟩

end Langlands.Global
