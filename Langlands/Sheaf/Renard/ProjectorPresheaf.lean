import Langlands.Sheaf.Renard.BasisSheaf
import Langlands.HarmonicAnalysis.PointwiseTestAlgebra
import Langlands.Algebra.NonUnitalModuleCorner
import Langlands.Topology.LocallyProfinite

/-!
# Compact-open projector presheaves for the original pointwise-test action
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v

namespace Langlands.Sheaf.Renard.ProjectorBasisSheaf

variable {X : Type u} [TopologicalSpace X]

/-- All compact opens of the original supplied topology. -/
def compactOpenBasis (hX : Langlands.Topology.IsLocallyProfinite X) : OpenBasis X where
  opens := {U | IsCompact (U : Set X)}
  isBasis := by
    convert hX.hasCompactOpenNeighborhoodBasis.isTopologicalBasis using 1
    ext S
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact ⟨U.isOpen, hU⟩
    · rintro ⟨ho, hc⟩
      exact ⟨⟨S, ho⟩, hc, rfl⟩

variable (hX : Langlands.Topology.IsLocallyProfinite X)

/-- The actual compact basis opens, with their unchanged inclusion category. -/
abbrev CompactOpen := BasisOpen (compactOpenBasis hX)

theorem compact (U : CompactOpen hX) : IsCompact (U.obj : Set X) := U.property

theorem clopen (U : CompactOpen hX) : IsClopen (U.obj : Set X) := by
  let := hX.t2Space
  exact ⟨(compact hX U).isClosed, U.obj.isOpen⟩

def emptyOpen : CompactOpen hX := ⟨⊥, isCompact_empty⟩

def unionOpen (U V : CompactOpen hX) : CompactOpen hX :=
  ⟨U.obj ⊔ V.obj, (compact hX U).union (compact hX V)⟩

def interOpen (U V : CompactOpen hX) : CompactOpen hX :=
  ⟨U.obj ⊓ V.obj, (compact hX U).inter_right (clopen hX V).isClosed⟩

/-- The original compact-open characteristic function. -/
def test (U : CompactOpen hX) : PointwiseTestAlgebra.Carrier X :=
  PointwiseTestAlgebra.characteristic (clopen hX U) (compact hX U)

/-- The published characteristic idempotent, without changing its carrier. -/
def idempotent (U : CompactOpen hX) : Idempotent (PointwiseTestAlgebra.Carrier X) :=
  PointwiseTestAlgebra.characteristicIdempotent (clopen hX U) (compact hX U)

@[simp] theorem idempotent_val (U : CompactOpen hX) :
    (idempotent hX U : PointwiseTestAlgebra.Carrier X) = test hX U := rfl

@[simp] theorem test_empty : test hX (emptyOpen hX) = 0 :=
  PointwiseTestAlgebra.characteristic_empty

theorem test_mul_of_le {U V : CompactOpen hX} (h : U.obj ≤ V.obj) :
    test hX U * test hX V = test hX U :=
  PointwiseTestAlgebra.characteristic_mul_of_subset _ _ _ _ h

theorem test_mul (U V : CompactOpen hX) :
    test hX U * test hX V = test hX (interOpen hX U V) :=
  PointwiseTestAlgebra.characteristic_mul _ _ _ _

theorem test_union (U V : CompactOpen hX) :
    test hX (unionOpen hX U V) =
      test hX U + test hX V - test hX (interOpen hX U V) :=
  PointwiseTestAlgebra.characteristic_union _ _ _ _

variable (M : Type v) [AddCommGroup M] [hM : NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]

/-- The specified original action of the actual characteristic test. -/
def action (U : CompactOpen hX) : M →+ M :=
  NonUnitalModuleCorner.originalAction (test hX U)

theorem action_apply (U : CompactOpen hX) (m : M) :
    action hX M U m = hM.toDistribSMul.toSMul.smul (test hX U) m := rfl

theorem action_mul (U V : CompactOpen hX) (m : M) :
    action hX M U (action hX M V m) =
      action hX M (interOpen hX U V) m := by
  change NonUnitalModuleCorner.originalAction (test hX U) (NonUnitalModuleCorner.originalAction (test hX V) m) = _
  rw [← NonUnitalModuleCorner.originalAction_mul, test_mul]
  rfl

theorem action_comm (U V : CompactOpen hX) (m : M) :
    action hX M U (action hX M V m) =
      action hX M V (action hX M U m) := by
  change NonUnitalModuleCorner.originalAction (test hX U) (NonUnitalModuleCorner.originalAction (test hX V) m) =
    NonUnitalModuleCorner.originalAction (test hX V) (NonUnitalModuleCorner.originalAction (test hX U) m)
  rw [← NonUnitalModuleCorner.originalAction_mul, ← NonUnitalModuleCorner.originalAction_mul, mul_comm]

theorem action_absorb {U V : CompactOpen hX} (h : U.obj ≤ V.obj) (m : M) :
    action hX M U (action hX M V m) = action hX M U m := by
  change NonUnitalModuleCorner.originalAction (test hX U) (NonUnitalModuleCorner.originalAction (test hX V) m) = _
  rw [← NonUnitalModuleCorner.originalAction_mul, test_mul_of_le hX h]
  rfl

/-- Exactly the published fixed-part carrier for the original module. -/
abbrev Value (U : CompactOpen hX) := NonUnitalModuleCorner.FixedPart (idempotent hX U) M

theorem fixedPart_eq_range (U : CompactOpen hX) :
    NonUnitalModuleCorner.fixedPart (idempotent hX U) M = (action hX M U).range :=
  NonUnitalModuleCorner.fixedPart_eq_range _

theorem value_fixed {U : CompactOpen hX} (s : Value hX M U) :
    action hX M U s.val = s.val := s.property

/-- Projection for the smaller open composed with inclusion for the larger. -/
def restrict {U V : CompactOpen hX} (_h : U.obj ≤ V.obj) :
    Value hX M V →+ Value hX M U :=
  (NonUnitalModuleCorner.projection (idempotent hX U)).comp (NonUnitalModuleCorner.inclusion (idempotent hX V))

theorem restrict_eq_projection_inclusion {U V : CompactOpen hX} (h : U.obj ≤ V.obj) :
    restrict hX M h =
      (NonUnitalModuleCorner.projection (idempotent hX U)).comp (NonUnitalModuleCorner.inclusion (idempotent hX V)) := rfl

@[simp] theorem restrict_val {U V : CompactOpen hX} (h : U.obj ≤ V.obj)
    (s : Value hX M V) : (restrict hX M h s).val = action hX M U s.val := rfl

theorem coe_restrict {U V : CompactOpen hX} (h : U.obj ≤ V.obj) :
    ⇑(restrict hX M h) =
      fun s => ⟨hM.toDistribSMul.toSMul.smul (test hX U) s.val,
        NonUnitalModuleCorner.coordinate_idempotent (idempotent hX U) s.val⟩ := rfl

@[simp] theorem restrict_self (U : CompactOpen hX) :
    restrict hX M (le_refl U.obj) = AddMonoidHom.id (Value hX M U) :=
  NonUnitalModuleCorner.projection_inclusion _

theorem restrict_comp {U V W : CompactOpen hX}
    (hUV : U.obj ≤ V.obj) (hVW : V.obj ≤ W.obj) :
    (restrict hX M hUV).comp (restrict hX M hVW) = restrict hX M (hUV.trans hVW) := by
  ext s
  exact Subtype.ext (action_absorb hX M hUV s.val)

/-- The actual contravariant additive functor of projector values. -/
def rawPresheaf : RawPresheaf.{u,v} (compactOpenBasis hX) where
  obj U := AddCommGrpCat.of (Value hX M U.unop)
  map f := AddCommGrpCat.ofHom (restrict hX M f.unop.hom.le)
  map_id U := by
    exact congrArg AddCommGrpCat.ofHom (restrict_self hX M U.unop)
  map_comp f g := by
    exact congrArg AddCommGrpCat.ofHom
      (restrict_comp hX M g.unop.hom.le f.unop.hom.le).symm

@[simp] theorem restriction_hom {U V : CompactOpen hX} (h : U.obj ≤ V.obj) :
    (restriction (rawPresheaf hX M) h).hom = restrict hX M h := rfl

@[simp] theorem restriction_val {U V : CompactOpen hX} (h : U.obj ≤ V.obj)
    (s : Sections (rawPresheaf hX M) V) :
    (restriction (rawPresheaf hX M) h s).val = action hX M U s.val := rfl

theorem empty_value_eq_zero (U : CompactOpen hX) (hU : U.obj = ⊥)
    (s : Value hX M U) : s = 0 := by
  have ht : test hX U = 0 := by
    have he : U = emptyOpen hX := by
      apply ObjectProperty.FullSubcategory.ext
      exact hU
    rw [he, test_empty]
  apply Subtype.ext
  have hs := value_fixed hX M s
  change NonUnitalModuleCorner.originalAction (test hX U) s.val = s.val at hs
  rw [ht, NonUnitalModuleCorner.originalAction_zero] at hs
  exact hs.symm

theorem isNormalized : IsNormalized (rawPresheaf hX M) := by
  intro U hU
  exact ⟨fun s t => (empty_value_eq_zero hX M U hU s).trans
    (empty_value_eq_zero hX M U hU t).symm⟩

/-- The source-normalized presheaf; the empty group is proved to be zero. -/
def presheaf : Presheaf.{u,v} (compactOpenBasis hX) :=
  ⟨rawPresheaf hX M, isNormalized hX M⟩

end Langlands.Sheaf.Renard.ProjectorBasisSheaf
