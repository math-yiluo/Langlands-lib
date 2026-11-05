import Langlands.Global.AdelicLevelModelPullbackStatement
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackProofs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Pullbacks at actual arithmetic levels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
variable {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)]
variable [∀ i, Algebra C (R i)] (π : ∀ i, A →ₐ[C] R i)

/-- The actual coefficient restrictions followed by actual scalar base change. -/
private def localModelRestriction (X : Over (Spec (CommRingCat.of C)))
    (p : RingPoint C X A) (i : ι) :
    RingPoint (R i) (ringBaseChange C (R i) X) (R i) :=
  ringPointBaseChangeEquiv C (R i) (R i) X (p.changeRing (π i))

private theorem localModelRestriction_natural
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (p : RingPoint C X A) (i : ι) :
    localModelRestriction C A R π Y (p ≫ f) i =
      localModelRestriction C A R π X p i ≫
        (Over.pullback (Spec.algebraMap C (R i))).map f := by
  unfold localModelRestriction
  rw [show RingPoint.changeRing (π i) (p ≫ f) =
    RingPoint.changeRing (π i) p ≫ f from (Category.assoc _ _ _).symm]
  exact ringPointBaseChangeEquiv_natural C (R i) (R i) f _

variable [∀ i, TopologicalSpace (R i)]

/-- The common initial-topology construction used in the arithmetic cases. -/
@[instance_reducible]
private def restrictionPointTopology (X : Over (Spec (CommRingCat.of C))) :
    TopologicalSpace (RingPoint C X A) :=
  TopologicalSpace.induced (localModelRestriction C A R π X)
    (localModelPointProductTopology C R X)

private theorem localModelRestriction_isInducing
    (X : Over (Spec (CommRingCat.of C))) :
    @IsInducing (RingPoint C X A)
      (∀ i, RingPoint (R i) (ringBaseChange C (R i) X) (R i))
      (restrictionPointTopology C A R π X) (localModelPointProductTopology C R X)
      (localModelRestriction C A R π X) := by
  let := restrictionPointTopology C A R π X
  let := localModelPointProductTopology C R X
  exact ⟨rfl⟩

variable [∀ i, IsTopologicalRing (R i)] [∀ i, IsLocalRing (R i)]
variable [∀ i, IsOpenUnits (R i)]

private theorem continuous_restrictionPointMap
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) :
    Continuous[restrictionPointTopology C A R π X,
      restrictionPointTopology C A R π Y]
      (fun p : RingPoint C X A => (p ≫ f : RingPoint C Y A)) := by
  let : TopologicalSpace (RingPoint C X A) := restrictionPointTopology C A R π X
  let : TopologicalSpace (RingPoint C Y A) := restrictionPointTopology C A R π Y
  let (i : ι) : TopologicalSpace (RingPoint (R i) (ringBaseChange C (R i) X) (R i)) :=
    schemePointTopology _ _ _
  let (i : ι) : TopologicalSpace (RingPoint (R i) (ringBaseChange C (R i) Y) (R i)) :=
    schemePointTopology _ _ _
  apply (localModelRestriction_isInducing C A R π Y).continuous_iff.mpr
  apply continuous_pi
  intro i
  let fi : ringBaseChange C (R i) X ⟶ ringBaseChange C (R i) Y :=
    (Over.pullback (Spec.algebraMap C (R i))).map f
  have h := (schemePointContinuity_proof (R i) (R i)
    (ringBaseChange C (R i) X) (ringBaseChange C (R i) Y) fi).comp
      ((continuous_apply i).comp (localModelRestriction_isInducing C A R π X).continuous)
  convert h using 1
  funext p
  exact localModelRestriction_natural C A R π f p i

/-- Initial local-model topologies preserve the actual pullback point comparison.
No injectivity or surjectivity of the restriction maps is required. -/
private theorem isHomeomorph_restrictionPullback
    {X Y Z : Over (Spec (CommRingCat.of C))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c) :
    letI : TopologicalSpace (RingPoint C X A) := restrictionPointTopology C A R π X
    letI : TopologicalSpace (RingPoint C Y A) := restrictionPointTopology C A R π Y
    @IsHomeomorph (RingPoint C c.pt A)
      {q : RingPoint C X A × RingPoint C Y A // q.1 ≫ f = q.2 ≫ g}
      (restrictionPointTopology C A R π c.pt) inferInstance
      (affineSchemePullbackPointComparison C A c) := by
  let : TopologicalSpace (RingPoint C X A) := restrictionPointTopology C A R π X
  let : TopologicalSpace (RingPoint C Y A) := restrictionPointTopology C A R π Y
  let : TopologicalSpace (RingPoint C c.pt A) := restrictionPointTopology C A R π c.pt
  let (i : ι) : TopologicalSpace (RingPoint (R i) (ringBaseChange C (R i) X) (R i)) :=
    schemePointTopology _ _ _
  let (i : ι) : TopologicalSpace (RingPoint (R i) (ringBaseChange C (R i) Y) (R i)) :=
    schemePointTopology _ _ _
  let (i : ι) : TopologicalSpace (RingPoint (R i) (ringBaseChange C (R i) c.pt) (R i)) :=
    schemePointTopology _ _ _
  let E := affineSchemePullbackPointEquiv C A c hc
  have hto : Continuous E := by
    exact ((continuous_restrictionPointMap C A R π c.fst).prodMk
      (continuous_restrictionPointMap C A R π c.snd)).subtype_mk _
  have hinv : Continuous E.symm := by
    apply (localModelRestriction_isInducing C A R π c.pt).continuous_iff.mpr
    apply continuous_pi
    intro i
    let F := Over.pullback (Spec.algebraMap C (R i))
    let ci := c.map F
    let hci : IsLimit ci := (c.isLimitMapConeEquiv F) (isLimitOfPreserves F hc)
    let : TopologicalSpace (RingPoint (R i) (F.obj X) (R i)) :=
      schemePointTopology _ _ _
    let : TopologicalSpace (RingPoint (R i) (F.obj Y) (R i)) :=
      schemePointTopology _ _ _
    let : TopologicalSpace (RingPoint (R i) ci.pt (R i)) :=
      schemePointTopology _ _ _
    let H := schemePullbackPointHomeomorph (R i) (R i) ci hci
    let t :
        {q : RingPoint C X A × RingPoint C Y A // q.1 ≫ f = q.2 ≫ g} →
        {q : RingPoint (R i) (ringBaseChange C (R i) X) (R i) ×
          RingPoint (R i) (ringBaseChange C (R i) Y) (R i) //
          q.1 ≫ F.map f = q.2 ≫ F.map g} :=
      fun q => ⟨(localModelRestriction C A R π X q.1.1 i,
        localModelRestriction C A R π Y q.1.2 i), by
          rw [← localModelRestriction_natural C A R π f,
            ← localModelRestriction_natural C A R π g, q.2]⟩
    have ht : Continuous t := by
      exact ((((continuous_apply i).comp
        (localModelRestriction_isInducing C A R π X).continuous).comp
          (continuous_fst.comp continuous_subtype_val)).prodMk
        (((continuous_apply i).comp
        (localModelRestriction_isInducing C A R π Y).continuous).comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _
    have heq : (fun q => localModelRestriction C A R π c.pt (E.symm q) i) =
        H.symm ∘ t := by
      funext q
      apply H.injective
      change H (localModelRestriction C A R π c.pt (E.symm q) i) =
        H (H.symm (t q))
      refine Eq.trans ?_ (H.apply_symm_apply (t q)).symm
      apply Subtype.ext
      apply Prod.ext
      · change localModelRestriction C A R π c.pt (E.symm q) i ≫ F.map c.fst =
          localModelRestriction C A R π X q.1.1 i
        rw [← localModelRestriction_natural]
        congr 1
        exact congrArg (fun z => z.val.1) (E.apply_symm_apply q)
      · change localModelRestriction C A R π c.pt (E.symm q) i ≫ F.map c.snd =
          localModelRestriction C A R π Y q.1.2 i
        rw [← localModelRestriction_natural]
        congr 1
        exact congrArg (fun z => z.val.2) (E.apply_symm_apply q)
    change Continuous (fun q => localModelRestriction C A R π c.pt (E.symm q) i)
    rw [heq]
    exact H.symm.continuous.comp ht
  exact ({ toEquiv := E, continuous_toFun := hto, continuous_invFun := hinv } :
    RingPoint C c.pt A ≃ₜ
      {q : RingPoint C X A × RingPoint C Y A // q.1 ≫ f = q.2 ≫ g}).isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Both arithmetic-level pullback comparisons are homeomorphisms on actual points. -/
theorem adelicLevelModelPullback : AdelicLevelModelPullbackStatement.{u} := by
  constructor
  · intro k F _ _ _ S X Y Z f g c hc
    let (i : CurvePlaceLevelFactorIndex k F S) : IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
      adelicLocalFactorUnits.1 k F S i
    exact isHomeomorph_restrictionPullback (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevel k F S) (CurvePlaceLevelFactor k F S)
      (curvePlaceLevelFactorAlgHom k F S) c hc
  · intro K _ _ S X Y Z f g c hc
    let (i : NumberFieldLevelFactorIndex K S) : IsOpenUnits (NumberFieldLevelFactor K S i) :=
      adelicLocalFactorUnits.2 K S i
    exact isHomeomorph_restrictionPullback ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K S) (NumberFieldLevelFactor K S)
      (numberFieldLevelFactorAlgHom K S) c hc

end Langlands.Global
