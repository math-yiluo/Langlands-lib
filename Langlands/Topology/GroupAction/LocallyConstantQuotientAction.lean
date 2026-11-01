import Langlands.Topology.GroupAction.CompactLocallyConstantAction
import Langlands.Topology.LocallyConstant.QuotientDescent

/-! # Continuous equivariant locally constant quotient descent -/

noncomputable section

universe u v w

namespace Langlands.CompactAction.DiscreteLocallyConstant

open CategoryTheory Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {A : Type w}

/-- All upstairs locally constant functions satisfying the literal quotient fibers. -/
abbrev FiberCompatible (q : C(X, Y)) (A : Type w) :=
  {f : DiscreteLocallyConstant X A // Function.FactorsThrough f q}

/-- Pullback with its complete fiber equations. -/
def compatiblePullback (q : C(X, Y)) (f : DiscreteLocallyConstant Y A) :
    FiberCompatible q A :=
  ⟨pullback q f, fun _ _ h => congrArg f h⟩

/-- Descent uses the original quotient topology and the complete fiber equations. -/
def compatibleDescend (q : C(X, Y)) (hq : IsQuotientMap q)
    (f : FiberCompatible q A) : DiscreteLocallyConstant Y A :=
  ⟨LocallyConstantQuotient.descend q hq f.val.toLocallyConstant f.property⟩

@[simp]
theorem compatibleDescend_apply (q : C(X, Y)) (hq : IsQuotientMap q)
    (f : FiberCompatible q A) (x : X) : compatibleDescend q hq f (q x) = f.val x :=
  LocallyConstantQuotient.descend_apply q hq f.val.toLocallyConstant f.property x

@[simp]
theorem compatibleDescend_pullback (q : C(X, Y)) (hq : IsQuotientMap q)
    (f : DiscreteLocallyConstant Y A) :
    compatibleDescend q hq (compatiblePullback q f) = f := by
  ext y
  obtain ⟨x, rfl⟩ := hq.surjective y
  exact compatibleDescend_apply q hq (compatiblePullback q f) x

@[simp]
theorem compatiblePullback_descend (q : C(X, Y)) (hq : IsQuotientMap q)
    (f : FiberCompatible q A) :
    compatiblePullback q (compatibleDescend q hq f) = f := by
  apply Subtype.ext
  ext x
  exact compatibleDescend_apply q hq f x

/-- The function-set equivalence retains the original quotient pullback. -/
def compatibleEquiv (q : C(X, Y)) (hq : IsQuotientMap q) :
    DiscreteLocallyConstant Y A ≃ FiberCompatible q A where
  toFun := compatiblePullback q
  invFun := compatibleDescend q hq
  left_inv := compatibleDescend_pullback q hq
  right_inv := compatiblePullback_descend q hq

variable (G : Type v) [Group G]
  [MulAction G X] [ContinuousConstSMul G X]
  [MulAction G Y] [ContinuousConstSMul G Y]
  (q : C(X, Y)) (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)

/-- The original inverse-precomposition action preserves all quotient fibers. -/
def compatibleSmul (g : G) (f : FiberCompatible q A) : FiberCompatible q A :=
  ⟨g • f.val, fun x y h => by
    change f.val (g⁻¹ • x) = f.val (g⁻¹ • y)
    apply f.property
    rw [heq, heq, h]⟩

omit [ContinuousConstSMul G Y] in
@[simp]
theorem compatibleSmul_apply (g : G) (f : FiberCompatible q A) (x : X) :
    (compatibleSmul G q heq g f).val x = f.val (g⁻¹ • x) := rfl

/-- The quotient pullback intertwines the actual restricted function action. -/
theorem compatiblePullback_smul (g : G) (f : DiscreteLocallyConstant Y A) :
    compatiblePullback q (g • f) = compatibleSmul G q heq g (compatiblePullback q f) :=
  Subtype.ext (pullback_smul G q heq g f)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Restriction of the upstairs action to the entire fiber-compatible subtype. -/
def compatibleAction : Action TopCat.{max u w} G where
  V := TopCat.of (FiberCompatible q A)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        ⟨compatibleSmul G q heq g, continuous_of_discreteTopology⟩
      map_one' := by
        apply TopCat.ext
        intro f
        apply Subtype.ext
        exact one_smul G f.val
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro f
        apply Subtype.ext
        exact mul_smul g h f.val }

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace X] [ContinuousSMul G X]

/-- Joint continuity is inherited from the original discrete upstairs action. -/
def compatibleContinuousAction : ContAction TopCat.{max u w} G :=
  ⟨compatibleAction (A := A) G q heq, (Action.isContinuous_def _).mpr (by
    change Continuous (fun p : G × FiberCompatible q A => compatibleSmul G q heq p.1 p.2)
    apply Continuous.subtype_mk
    exact continuous_smul.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩

/-- The fiber-compatible action embeds by the unchanged subtype inclusion. -/
def compatibleInclusion :
    compatibleContinuousAction (A := A) G q heq ⟶ continuousAction (X := X) (A := A) G :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      comm := fun g => by
        apply TopCat.ext
        intro f
        rfl }

variable [CompactSpace Y] [ContinuousSMul G Y]

/-- An equivariant quotient gives a continuous equivariant descent isomorphism,
with the original group topology and complete upstairs fiber equations. -/
def compatibleDescentIso (hq : IsQuotientMap q) :
    continuousAction (X := Y) (A := A) G ≅ compatibleContinuousAction (A := A) G q heq :=
  ObjectProperty.isoMk _ (Action.mkIso
    { hom := TopCat.ofHom ⟨compatiblePullback q, continuous_of_discreteTopology⟩
      inv := TopCat.ofHom ⟨compatibleDescend q hq, continuous_of_discreteTopology⟩
      hom_inv_id := by
        apply TopCat.ext
        intro f
        exact compatibleDescend_pullback q hq f
      inv_hom_id := by
        apply TopCat.ext
        intro f
        exact compatiblePullback_descend q hq f }
    (fun g => by
      apply TopCat.ext
      intro f
      exact compatiblePullback_smul G q heq g f))

@[simp]
theorem compatibleDescentIso_hom_apply (hq : IsQuotientMap q)
    (f : DiscreteLocallyConstant Y A) :
    (compatibleDescentIso (A := A) G q heq hq).hom.hom.hom f = compatiblePullback q f := rfl

@[simp]
theorem compatibleDescentIso_inv_apply (hq : IsQuotientMap q)
    (f : FiberCompatible q A) (x : X) :
    (toLocallyConstant ((compatibleDescentIso (A := A) G q heq hq).inv.hom.hom f)) (q x) =
      f.val x := compatibleDescend_apply q hq f x

end Langlands.CompactAction.DiscreteLocallyConstant
