import Langlands.Automorphic.GroupSchemeAmbient
import Langlands.Global.AdelicSplitCenterMeasure
import Langlands.Analysis.Local.QuotientMass
import Mathlib.MeasureTheory.Function.L2Space

/-! # Continuous functions in the actual positive-central quotient L² space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.PositiveRealTorus
open Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i

/-- The actual almost-everywhere quotient for the supplied measure on the actual quotient. -/
abbrev QuotientL2 (measureQ : Measure Q) := Lp ℂ 2 measureQ

/-- Continuous square-integrable functions, before passing to almost-everywhere classes. -/
def continuousL2Submodule (measureQ : Measure Q) : Submodule ℂ C(Q, ℂ) where
  carrier := {f | MemLp f 2 measureQ}
  zero_mem' := MemLp.zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

@[simp] theorem mem_continuousL2Submodule (measureQ : Measure Q) (f : C(Q, ℂ)) :
    f ∈ continuousL2Submodule F G T i measureQ ↔ MemLp f 2 measureQ := Iff.rfl

/-- The genuine complex-linear map to square-integrable null classes. -/
def continuousL2ToLp (measureQ : Measure Q) :
    continuousL2Submodule F G T i measureQ →ₗ[ℂ] QuotientL2 F G T i measureQ where
  toFun f := f.property.toLp f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeFn_continuousL2ToLp (measureQ : Measure Q)
    (f : continuousL2Submodule F G T i measureQ) :
    continuousL2ToLp F G T i measureQ f =ᵐ[measureQ] (f.val : Q → ℂ) :=
  MemLp.coeFn_toLp f.property

/-- Full support makes the continuous realization faithful. -/
theorem continuousL2ToLp_injective (measureQ : Measure Q) [measureQ.IsOpenPosMeasure] :
    Function.Injective (continuousL2ToLp F G T i measureQ) := by
  intro f g h
  apply Subtype.ext
  apply ContinuousMap.coe_injective
  apply MeasureTheory.Measure.eq_of_ae_eq
    ((MemLp.toLp_eq_toLp_iff f.property g.property).mp h)
    f.val.continuous g.val.continuous

variable [IsAffine G.X.left]

/-- Positive right pullback on continuous functions on the actual quotient. -/
def continuousPositiveQuotientRightAction :
    Representation ℂ (AdelicGroupPoints F G) C(Q, ℂ) where
  toFun g :=
    { toFun f := f.comp ⟨LeftCosetSpace.rightTranslate Γ g,
        LeftCosetSpace.continuous_rightTranslate Γ g⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro q
    exact congrArg f (LeftCosetSpace.rightTranslate_one Γ q)
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro q
    exact congrArg f (LeftCosetSpace.rightTranslate_mul Γ g h q).symm

@[simp] theorem continuousPositiveQuotientRightAction_apply (g : AdelicGroupPoints F G)
    (f : C(Q, ℂ)) (q : Q) :
    continuousPositiveQuotientRightAction F G T i g f q =
      f (LeftCosetSpace.rightTranslate Γ g q) := rfl

/-- Pullback to actual adelic points gives the existing continuous rational function carrier. -/
def positiveQuotientContinuousPullback :
    C(Q, ℂ) →ₗ[ℂ] ContinuousRationalFunctions F G where
  toFun f :=
    ⟨⟨fun x => f (LeftCosetSpace.mk Γ x), by
      intro q x
      exact congrArg f (LeftCosetSpace.mk_subgroup_mul Γ
        ⟨rational F G q, rationalSubgroup_le_positiveRationalSubgroup F G T i ⟨q, rfl⟩⟩ x)⟩,
      f.continuous.comp (LeftCosetSpace.continuous_mk Γ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem positiveQuotientContinuousPullback_apply (f : C(Q, ℂ))
    (x : AdelicGroupPoints F G) :
    (positiveQuotientContinuousPullback F G T i f).val.val x =
      f (LeftCosetSpace.mk Γ x) := rfl

theorem positiveQuotientContinuousPullback_injective :
    Function.Injective (positiveQuotientContinuousPullback F G T i) := by
  intro f g h
  apply ContinuousMap.ext
  intro q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  exact congrArg (fun f : ContinuousRationalFunctions F G => f.val.val x) h

/-- The pointwise and quotient constructions use the same positive right action. -/
theorem positiveQuotientContinuousPullback_rightAction (g : AdelicGroupPoints F G)
    (f : C(Q, ℂ)) :
    positiveQuotientContinuousPullback F G T i
      (continuousPositiveQuotientRightAction F G T i g f) =
        continuousRightAction F G g (positiveQuotientContinuousPullback F G T i f) := by
  rfl

/-- Right invariance is a measure-preservation condition on the actual quotient maps. -/
def QuotientMeasureRightInvariant (measureQ : Measure Q) : Prop :=
  ∀ g : AdelicGroupPoints F G,
    MeasurePreserving (LeftCosetSpace.rightTranslate Γ g) measureQ measureQ

variable (measureQ : Measure (PositiveRationalQuotient F G T i))
variable (hInvariant : QuotientMeasureRightInvariant F G T i measureQ)

/-- Positive right pullback is an isometry of the actual L² space. -/
def quotientL2RightTranslate (g : AdelicGroupPoints F G) :
    QuotientL2 F G T i measureQ →ₗᵢ[ℂ] QuotientL2 F G T i measureQ :=
  Lp.compMeasurePreservingₗᵢ ℂ (LeftCosetSpace.rightTranslate Γ g) (hInvariant g)

omit [IsAffine G.X.left] in
theorem coeFn_quotientL2RightTranslate (g : AdelicGroupPoints F G)
    (f : QuotientL2 F G T i measureQ) :
    quotientL2RightTranslate F G T i measureQ hInvariant g f =ᵐ[measureQ]
      fun q => f (LeftCosetSpace.rightTranslate Γ g q) :=
  Lp.coeFn_compMeasurePreserving f (hInvariant g)

omit [IsAffine G.X.left] in
@[simp] theorem quotientL2RightTranslate_one (f : QuotientL2 F G T i measureQ) :
    quotientL2RightTranslate F G T i measureQ hInvariant 1 f = f := by
  have hid : LeftCosetSpace.rightTranslate Γ (1 : AdelicGroupPoints F G) = id :=
    funext (LeftCosetSpace.rightTranslate_one Γ)
  change Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate Γ 1) (hInvariant 1) f = f
  simp only [hid]
  exact Lp.compMeasurePreserving_id_apply f

omit [IsAffine G.X.left] in
theorem quotientL2RightTranslate_mul (g h : AdelicGroupPoints F G)
    (f : QuotientL2 F G T i measureQ) :
    quotientL2RightTranslate F G T i measureQ hInvariant (g * h) f =
      quotientL2RightTranslate F G T i measureQ hInvariant g
        (quotientL2RightTranslate F G T i measureQ hInvariant h f) := by
  have hcomp : LeftCosetSpace.rightTranslate Γ (g * h) =
      LeftCosetSpace.rightTranslate Γ h ∘ LeftCosetSpace.rightTranslate Γ g :=
    funext fun q => (LeftCosetSpace.rightTranslate_mul Γ g h q).symm
  change Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate Γ (g * h)) (hInvariant (g * h)) f =
    Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate Γ g) (hInvariant g)
      (Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate Γ h) (hInvariant h) f)
  simpa only [← hcomp] using
    Lp.compMeasurePreserving_comp_apply f (hInvariant h) (hInvariant g)

/-- The actual positive right regular representation on quotient L² classes. -/
def quotientL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (QuotientL2 F G T i measureQ) where
  toFun g := (quotientL2RightTranslate F G T i measureQ hInvariant g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    exact quotientL2RightTranslate_one F G T i measureQ hInvariant
  map_mul' g h := by
    apply LinearMap.ext
    exact quotientL2RightTranslate_mul F G T i measureQ hInvariant g h

/-- The same square-integrability condition is stable under continuous positive pullback. -/
def continuousL2Subrepresentation :
    Subrepresentation (continuousPositiveQuotientRightAction F G T i) where
  toSubmodule := continuousL2Submodule F G T i measureQ
  apply_mem_toSubmodule g _f hf := hf.comp_measurePreserving (hInvariant g)

/-- Positive right translation on continuous square-integrable representatives. -/
def continuousL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (continuousL2Submodule F G T i measureQ) :=
  (continuousL2Subrepresentation F G T i measureQ hInvariant).toRepresentation

/-- Passing to null classes intertwines the two actual positive right actions. -/
theorem continuousL2ToLp_rightAction (g : AdelicGroupPoints F G)
    (f : continuousL2Submodule F G T i measureQ) :
    continuousL2ToLp F G T i measureQ (continuousL2RightAction F G T i measureQ hInvariant g f) =
      quotientL2RightAction F G T i measureQ hInvariant g (continuousL2ToLp F G T i measureQ f) :=
  (Lp.toLp_compMeasurePreserving f.property (hInvariant g)).symm

section CanonicalMeasure

variable [LocallyOfFiniteType G.X.hom]
variable (hi : Function.Injective (Langlands.GroupScheme.characterRestrict i))
variable [(Langlands.GroupScheme.characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ Langlands.GroupScheme.splitTorus (Spec (CommRingCat.of F)) I)
variable (hc : Langlands.GroupScheme.IsCentral i)
variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

include hi I e hc in
/-- The previously constructed normalized quotient measure supplies actual right invariance. -/
theorem haarQuotientMeasureRightInvariant :
    QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i) :=
  measurePreserving_rightTranslate_positiveRationalQuotientHaarMeasure F G T i hi I e hc

include hi I e hc in
/-- Exact quotient compatibility and the existing homeomorphism prove full support. -/
theorem haarQuotientMeasure_isOpenPosMeasure :
    (positiveRationalQuotientHaarMeasure F G T i).IsOpenPosMeasure := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let : (normOneRationalQuotientHaarMeasure F G).IsOpenPosMeasure :=
    (normOneRationalQuotientHaarMeasure_isCompatible F G).isOpenPosMeasure
  exact (positiveQuotientHomeomorph F G T i hi I e hc).continuous.isOpenPosMeasure_map
    (positiveQuotientHomeomorph F G T i hi I e hc).surjective

include hi I e hc in
/-- Canonical Haar normalization gives a faithful continuous realization in the actual L². -/
theorem haarContinuousL2ToLp_injective :
    Function.Injective
      (continuousL2ToLp F G T i (positiveRationalQuotientHaarMeasure F G T i)) := by
  let := haarQuotientMeasure_isOpenPosMeasure F G T i hi I e hc
  exact continuousL2ToLp_injective F G T i _

end CanonicalMeasure

end Langlands.Automorphic.GroupSchemeFunctions
