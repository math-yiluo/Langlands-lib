import Langlands.Global.AdelicSpreadGeometricallyConnectedProof
import Langlands.Global.AdelicSpreadSeparatedExistenceProof
import Langlands.Global.AdelicLevelComponentSurjectivityProof
import Langlands.Global.AdelicSpreadSmoothOpenAssemblyProof
import Langlands.AlgebraicGeometry.UniformLangWeilProof
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange

/-! # Local points of smooth geometrically connected number-field schemes -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

private lemma property_pullback_structureMap_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {B C : Scheme.{u}} (b : C ⟶ B) (M : Over B) :
    P (((Over.pullback b).map
      (Over.homMk M.hom (by simp) : M ⟶ Over.mk (𝟙 B))).left) ↔
        P (((Over.pullback b).obj M).hom) := by
  let f : M ⟶ Over.mk (𝟙 B) := Over.homMk M.hom (by simp)
  let fb := (Over.pullback b).map f
  have : IsIso (((Over.pullback b).obj (Over.mk (𝟙 B))).hom) := by
    change IsIso (pullback.snd (𝟙 B) b)
    infer_instance
  change P fb.left ↔ P (((Over.pullback b).obj M).hom)
  rw [← Over.w fb]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).symm

/-- A smooth geometrically connected separated finite-type scheme admits
an actual smooth geometrically connected model over a finite-type ring of
S-integers. -/
theorem exists_numberFieldSmoothConnectedModel
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K)))
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [GeometricallyConnected X.hom] :
    ∃ (S : Finset (FinitePlace K))
      (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
      Algebra.FiniteType ℤ ((S : Set (FinitePlace K)).integer K) ∧
      Smooth M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      GeometricallyConnected M.hom ∧
      Nonempty (numberFieldModelGenericFiber K S M ≅ X) := by
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨T, M, hft, hqc, hsep, ⟨e⟩⟩ :=
    numberFieldSpreadSeparatedExistence K ∅ X
  let : LocallyOfFiniteType M.hom := hft
  let : QuasiCompact M.hom := hqc
  let : IsSeparated M.hom := hsep
  let B : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K))) :=
    Over.mk (𝟙 _)
  let : LocallyOfFiniteType B.hom := by dsimp [B]; infer_instance
  let : QuasiCompact B.hom := by dsimp [B]; infer_instance
  let f : M ⟶ B := Over.homMk M.hom (by simp [B])
  let P : MorphismProperty Scheme.{u} := @Smooth ⊓ @GeometricallyConnected
  have hgen : P (numberFieldModelGenericFiber K T.val M).hom := by
    rw [← Over.w e.hom]
    exact ⟨inferInstance,
      (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr
        inferInstance⟩
  have hfgen : P (((Over.pullback
      (Spec.map (CommRingCat.ofHom
        ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype))).map f).left) :=
    (property_pullback_structureMap_iff P _ M).mpr hgen
  obtain ⟨U, hU⟩ :=
    (numberFieldSpreadEventualSmoothGeometricallyConnected K T.val M B f).mp hfgen
  let N := numberFieldLevelModelBaseChange K U.property M
  have hN : P N.hom := (property_pullback_structureMap_iff P _ M).mp hU
  let : Smooth N.hom := hN.1
  let : GeometricallyConnected N.hom := hN.2
  let : QuasiCompact N.hom := by
    dsimp [N, numberFieldLevelModelBaseChange]
    infer_instance
  let : IsSeparated N.hom := by
    dsimp [N, numberFieldLevelModelBaseChange]
    infer_instance
  let V := numberFieldPrincipalLevelAbove K U.val
  let Q := numberFieldLevelModelBaseChange K V.property N
  let eU : numberFieldModelGenericFiber K U.val N ≅
      numberFieldModelGenericFiber K T.val M :=
    modelPullbackCompIso
      (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K U.property)))
      (Spec.map (CommRingCat.ofHom
        ((U.val : Set (FinitePlace K)).integer K).toSubring.subtype))
      (Spec.map (CommRingCat.ofHom
        ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype))
      (by rw [← Spec.map_comp]; rfl) M
  let eV : numberFieldModelGenericFiber K V.val Q ≅
      numberFieldModelGenericFiber K U.val N :=
    modelPullbackCompIso
      (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K V.property)))
      (Spec.map (CommRingCat.ofHom
        ((V.val : Set (FinitePlace K)).integer K).toSubring.subtype))
      (Spec.map (CommRingCat.ofHom
        ((U.val : Set (FinitePlace K)).integer K).toSubring.subtype))
      (by rw [← Spec.map_comp]; rfl) N
  refine ⟨V.val, Q, numberFieldPrincipalLevelAbove_finiteType K U.val,
    ?_, ?_, ?_, ?_, ⟨eV ≪≫ eU ≪≫ e⟩⟩
  all_goals dsimp [Q, numberFieldLevelModelBaseChange]; infer_instance

/-- Every smooth separated quasi-compact geometrically connected
number-field scheme has points over almost all finite completions. -/
theorem eventually_nonempty_ringPoint_of_smooth_geometricallyConnected
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K)))
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [GeometricallyConnected X.hom] :
    ∀ᶠ v in Filter.cofinite (α := FinitePlace K),
      Nonempty (RingPoint K X (FiniteCompletion K v)) := by
  classical
  obtain ⟨S, M, hRft, hsm, hqc, hsep, hconn, ⟨e⟩⟩ :=
    exists_numberFieldSmoothConnectedModel K X
  let R : Type u := ((S : Set (FinitePlace K)).integer K)
  let : Algebra.FiniteType ℤ R := hRft
  let : Smooth M.hom := hsm
  let : QuasiCompact M.hom := hqc
  let : IsSeparated M.hom := hsep
  let : GeometricallyConnected M.hom := hconn
  let B : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType B.hom := by dsimp [B]; infer_instance
  let : CompactSpace B.left := by dsimp [B]; infer_instance
  let f : M ⟶ B := Over.homMk M.hom (by simp [B])
  let lifts := numberFieldComponentAlmostAllIntegralPointLifts
    Langlands.AlgebraicGeometry.uniformLangWeil K R B M f
    (locallyOfFiniteType_toSpecULiftZ_of_over R B) inferInstance
    hsm hsep hqc hconn
  filter_upwards [S.eventually_cofinite_notMem, lifts.1.eventually_cofinite_notMem]
    with v hvS hv
  let : Algebra R (v.adicCompletionIntegers K) :=
    instAdelicLevelModelPoints10 K S (.inr (.inr ⟨v, hvS⟩))
  let : Algebra R (FiniteCompletion K v) :=
    ((algebraMap K (FiniteCompletion K v)).comp
      ((S : Set (FinitePlace K)).integer K).subtype).toAlgebra
  let : SMul R (FiniteCompletion K v) :=
    (inferInstance : Algebra R (FiniteCompletion K v)).toSMul
  let : Algebra R K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let : IsScalarTower R (v.adicCompletionIntegers K) (FiniteCompletion K v) :=
    IsScalarTower.of_algebraMap_eq (R := R)
      (S := v.adicCompletionIntegers K) (A := FiniteCompletion K v) fun _ => rfl
  let : IsScalarTower R K (FiniteCompletion K v) :=
    IsScalarTower.of_algebraMap_eq (R := R)
      (S := K) (A := FiniteCompletion K v) fun _ => rfl
  let p : RingPoint R B (v.adicCompletionIntegers K) :=
    Over.homMk (ringTest R (v.adicCompletionIntegers K)).hom (by simp [B])
  let a := (lifts.2 v hv p).1
  let aK : RingPoint R M (FiniteCompletion K v) :=
    RingPoint.changeRing (IsScalarTower.toAlgHom R (v.adicCompletionIntegers K)
      (FiniteCompletion K v)) a
  let aF : RingPoint K (numberFieldModelGenericFiber K S M) (FiniteCompletion K v) :=
    ringPointBaseChangeEquiv R K (FiniteCompletion K v) M aK
  exact ⟨aF ≫ e.hom⟩

end Langlands.Global
