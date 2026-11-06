import Langlands.LocalFactor.NonabelianDualityDefect
import Langlands.LocalFactor.NonabelianDualityReduction
import Langlands.VirtualRepresentation.ExactInductionDual
import Langlands.VirtualRepresentation.ExactInductionTwist

/-!
# Duality and actual common-closure induction

The norm-twisted contragredient commutes with actual common-closure induction.
Trace pullback commutes with negation of the additive character.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (E L : Extension F) (h : E.field ≤ L.field)

/-- Actual common-closure induction commutes with the contragredient. -/
theorem continuousDual_induce (x : Virtual.{uF, uV} F L) :
    ExactGrothendieckGroup.continuousDual (induce F E L h x) =
      induce F E L h (ExactGrothendieckGroup.continuousDual x) := by
  unfold induce
  simp only [LinearMap.comp_apply]
  rw [ExactGrothendieckGroup.continuousDual_induce _ (nestedWeil_open F E L),
    ← ExactGrothendieckGroup.continuousRestrict_continuousDual]

/-- The two actual restricted norm characters agree on the nested subgroup. -/
theorem normCharacter_nestedWeilEquiv :
    (CommonClosureWeilDeligne.normCharacter F L).comp
        (nestedWeilEquiv F E L h : _ →ₜ* _) =
      (CommonClosureWeilDeligne.normCharacter F E).comp
        ⟨((weilSubgroup F L).subgroupOf (weilSubgroup F E)).subtype,
          continuous_subtype_val⟩ := by
  ext w
  rfl

/-- Actual common-closure induction commutes with the restricted norm twist. -/
theorem normTwist_induce (x : Virtual.{uF, uV} F L) :
    ExactGrothendieckGroup.continuousTwist
        (CommonClosureWeilDeligne.normCharacter F E) (induce F E L h x) =
      induce F E L h
        (ExactGrothendieckGroup.continuousTwist
          (CommonClosureWeilDeligne.normCharacter F L) x) := by
  change ExactGrothendieckGroup.continuousTwist _
      (ExactGrothendieckGroup.continuousInduce _ (nestedWeil_open F E L)
        (ExactGrothendieckGroup.continuousRestrict
          (nestedWeilEquiv F E L h : _ →ₜ* _) x)) =
    ExactGrothendieckGroup.continuousInduce _ (nestedWeil_open F E L)
      (ExactGrothendieckGroup.continuousRestrict
        (nestedWeilEquiv F E L h : _ →ₜ* _)
        (ExactGrothendieckGroup.continuousTwist _ x))
  rw [ExactGrothendieckGroup.continuousRestrict_continuousTwist,
    normCharacter_nestedWeilEquiv,
    ExactGrothendieckGroup.continuousInduce_continuousTwist]

/-- The composite operation in the fixed-Haar equation commutes with
actual common-closure induction. -/
theorem normTwistedDual_induce (x : Virtual.{uF, uV} F L) :
    ExactGrothendieckGroup.continuousTwistedDual
        (CommonClosureWeilDeligne.normCharacter F E) (induce F E L h x) =
      induce F E L h
        (ExactGrothendieckGroup.continuousTwistedDual
          (CommonClosureWeilDeligne.normCharacter F L) x) := by
  simp only [ExactGrothendieckGroup.continuousTwistedDual_apply]
  rw [continuousDual_induce, normTwist_induce]

/-- Pullback along the actual field trace commutes with the inverse additive
character, for the canonical field topologies. -/
theorem traceCharacter_scale_neg_one :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    letI := (fieldData F L).topology
    letI := (fieldData F L).valuativeRel
    letI := (fieldData F L).localField
    ∀ ψ : AdditiveCharacter F E,
      traceCharacter F E L h (ψ.scale (-1)) =
        (traceCharacter F E L h ψ).scale (-1) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let := (fieldData F L).topology
  let := (fieldData F L).valuativeRel
  let := (fieldData F L).localField
  intro ψ
  ext x
  simp only [traceCharacter_apply,
    HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply,
    Units.val_neg, Units.val_one, neg_one_mul, map_neg]

end Langlands.LocalFactor.CommonClosure

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- On degree-zero virtual elements the defect is unchanged by actual
common-closure induction, with arbitrary Haar measures on both fields. -/
theorem dualityDefect_induce (e : ReciprocityFamily F)
    (ε : Assignment.{uF, uV} F) (hε : IsSystem F e ε)
    (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E)
    (μL μL' : HaarMeasure F L) (x : DegreeZero.{uF, uV} F L) :
    dualityDefect F ε hε.2.1 E ψ μ μ' (induce F E L h x.val) =
      dualityDefect F ε hε.2.1 L (traceCharacter F E L h ψ) μL μL' x.val := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let := (fieldData F L).topology
  let := (fieldData F L).valuativeRel
  let := (fieldData F L).localField
  let y : DegreeZero.{uF, uV} F L :=
    ⟨ExactGrothendieckGroup.continuousTwistedDual
      (CommonClosureWeilDeligne.normCharacter F L) x.val, by
        change degree F L _ = 0
        rw [ExactGrothendieckGroup.degree_continuousTwistedDual]
        exact x.property⟩
  change Additive.ofMul (ε E ψ μ (induce F E L h x.val) *
      ε E (ψ.scale (-1)) μ'
        (ExactGrothendieckGroup.continuousTwistedDual
          (CommonClosureWeilDeligne.normCharacter F E) (induce F E L h x.val))) = _
  rw [normTwistedDual_induce]
  change Additive.ofMul (ε E ψ μ (induce F E L h x.val) *
      ε E (ψ.scale (-1)) μ' (induce F E L h y.val)) = _
  rw [hε.2.2.2.1 E L h ψ μ μL x,
    hε.2.2.2.1 E L h (ψ.scale (-1)) μ' μL' y,
    traceCharacter_scale_neg_one]
  rfl

/-- Degree-zero elements of the duality kernel induce into the duality
kernel. This is a restriction of the actual common-closure induction map. -/
def induceDualityKernel (e : ReciprocityFamily F)
    (ε : Assignment.{uF, uV} F) (hε : IsSystem F e ε)
    (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E)
    (μL μL' : HaarMeasure F L) :
    ↥(DegreeZero.{uF, uV} F L ⊓
        dualityKernel F ε hε.2.1 L (traceCharacter F E L h ψ) μL μL') →ₗ[ℤ]
      dualityKernel F ε hε.2.1 E ψ μ μ' :=
  (induce F E L h).restrict fun x hx => by
    change dualityDefect F ε hε.2.1 E ψ μ μ' (induce F E L h x) = 0
    rw [dualityDefect_induce F e ε hε E L h ψ μ μ' μL μL' ⟨x, hx.1⟩]
    exact hx.2

end Langlands.LocalFactor.NonabelianSystem
