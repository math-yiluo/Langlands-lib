import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Induction.SplitKernelLocalizationData

/-! Actual coefficient data and the canonical weighted split-stages integrand. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Induction.SplitStagesCharacter

open MeasureTheory QuotientIntegration HarmonicAnalysis

universe uG uL uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
variable (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
variable (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
variable (θ : SmoothCharacter ℂ r.ker)
variable (hθ : SplitKernelLocalization.SectionInvariant r s θ.toMonoidHom)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)

local notation "K" => P.comap s
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "σP" => σ.comp φ
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rP)) HP
local notation "A" => SplitKernelLocalization.kernelIntersection rP HP

/-- Pullback of the supplied smooth kernel character through the actual kernel map. -/
def kernelCharacter : SmoothCharacter ℂ (rP).ker where
  toMonoidHom := θ.toMonoidHom.comp (splitStagesKernelEquiv r s hrs P hker).toMonoidHom
  isOpen_ker := θ.isOpen_ker.preimage
    (splitStagesKernelContinuousEquiv r s hrs P hker).continuous

local notation "θP" => SmoothCharacter.toMonoidHom (kernelCharacter r s hrs P hker θ)
local notation "η" => SplitKernelLocalization.intersectionCharacter rP θP HP
local notation "C" => Jacquet.Localization.Coinvariants σP A η

include hsH in
omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TopologicalSpace L] [IsTopologicalGroup L] in
/-- The nested section containment is derived only over `P.comap s`. -/
theorem section_mem (l : K) : sP l ∈ HP := hsH l

include hH in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Closedness of the nested inducing subgroup is the actual subtype preimage. -/
theorem subgroup_closed : IsClosed (HP : Set P) :=
  hH.preimage (continuous_subtype_val : Continuous P.subtype)

include hθ in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TopologicalSpace L] [IsTopologicalGroup L] in
/-- Section invariance pulls back through the actual kernel identification. -/
theorem sectionInvariant : SplitKernelLocalization.SectionInvariant rP sP θP := by
  intro l n
  exact hθ (l : L) (splitStagesKernelEquiv r s hrs P hker n)

local notation "hSI" => section_mem s P H hsH
local notation "hθP" => sectionInvariant r s hrs P hker θ hθ
local notation "hHPc" => subgroup_closed P H hH

section Coefficient

variable [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
variable [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
variable [mI : MeasurableSpace ((H.subgroupOf P).comap
  (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [bI : BorelSpace ((H.subgroupOf P).comap
  (splitStagesRetraction r s hrs P hker).ker.subtype)]

/-- The existing subgroup-to-kernel Haar ratio for inverse section conjugation. -/
abbrev haarCharacter : K →* ℂˣ :=
  Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)

/-- The specified Haar twist on the actual localized coefficient carrier. -/
abbrev coefficientAction : Representation ℂ K C :=
  twist (haarCharacter r s hrs P H hker hH hsH)
    (SplitKernelLocalization.subgroupAction rP sP θP hθP HP hSI σP)

/-- The complete coefficient action on actual quotient representatives. -/
@[simp] theorem coefficientAction_mk (l : K) (v : V) :
    coefficientAction r s hrs P H hker hHP hH hsH θ hθ σ l
        (Jacquet.Localization.mk σP A η v) =
      (haarCharacter r s hrs P H hker hH hsH l : ℂ) •
        Jacquet.Localization.mk σP A η
          (σP (SplitKernelLocalization.subgroupSection sP HP hSI l) v) := rfl

end Coefficient

/-- The prescribed inverse-character-weighted value before quotient descent. -/
def kernelFunction (f : CompactFunctions H σ) (l : L) (n : (rP).ker) : C :=
  Jacquet.Localization.mk σP A η
    (((θP n)⁻¹ : ℂˣ) • eval H σ f.val (((n : P) : G) * s l))

omit [T2Space G] [LocallyCompactSpace G] [TopologicalSpace L] [IsTopologicalGroup L] in
/-- Left intersection covariance and the inverse character cancel in localization. -/
theorem kernelFunction_left_mul (f : CompactFunctions H σ) (l : L)
    (i : I) (n : (rP).ker) :
    kernelFunction r s hrs P H hker hHP θ σ f l ((i : (rP).ker) * n) =
      kernelFunction r s hrs P H hker hHP θ σ f l n := by
  let a : A := (SplitKernelLocalization.intersectionEquiv rP HP).symm i
  have hval : ((φ (a : HP)) : G) = (((i : (rP).ker) : P) : G) := rfl
  have hf : eval H σ f.val ((((((i : (rP).ker) * n) : (rP).ker) : P) : G) * s l) =
      σP (a : HP) (eval H σ f.val (((n : P) : G) * s l)) := by
    simpa only [Subgroup.coe_mul, mul_assoc, MonoidHom.comp_apply, hval] using
      (eval_covariant H σ f.val (φ (a : HP)) (((n : P) : G) * s l))
  change Jacquet.Localization.mk σP A η
      (((θP ((i : (rP).ker) * n))⁻¹ : ℂˣ) •
        eval H σ f.val ((((((i : (rP).ker) * n) : (rP).ker) : P) : G) * s l)) = _
  rw [hf]
  simp only [Units.smul_def, map_smul]
  rw [Jacquet.Localization.mk_apply_subgroup σP A η a]
  change _ = (((θP n)⁻¹ : ℂˣ) : ℂ) •
    Jacquet.Localization.mk σP A η (eval H σ f.val (((n : P) : G) * s l))
  have ha : η a = θP (i : (rP).ker) := rfl
  rw [ha]
  simp only [map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), mul_one]

/-- The canonical descended function, with values in the specified coefficient quotient. -/
def integrandFunction (f : CompactFunctions H σ) (l : L) : LeftQuotient I → C :=
  QuotientIntegration.descend I
    (kernelFunction r s hrs P H hker hHP θ σ f l)
    (kernelFunction_left_mul r s hrs P H hker hHP θ σ f l)

@[simp] theorem integrandFunction_mk (f : CompactFunctions H σ) (l : L) (n : (rP).ker) :
    integrandFunction r s hrs P H hker hHP θ σ f l (quotientMap I n) =
      Jacquet.Localization.mk σP A η
        (((θP n)⁻¹ : ℂˣ) • eval H σ f.val (((n : P) : G) * s l)) := rfl

omit [T2Space G] [LocallyCompactSpace G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem kernelCharacter_isLocallyConstant : IsLocallyConstant θP := by
  apply (IsLocallyConstant.iff_exists_open θP).mpr
  intro x
  refine ⟨(fun y : (rP).ker => y * x⁻¹) ⁻¹' ((θP).ker : Set (rP).ker),
    (kernelCharacter r s hrs P hker θ).isOpen_ker.preimage
      (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change θP (y * x⁻¹) = 1 at hy
    exact mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using hy)

/-- The inverse smooth character and the original compact function give local constancy. -/
theorem kernelFunction_isLocallyConstant (f : CompactFunctions H σ) (l : L) :
    IsLocallyConstant (kernelFunction r s hrs P H hker hHP θ σ f l) := by
  have hf := (eval_isLocallyConstant H σ f.val).comp_continuous
    ((continuous_subtype_val.comp continuous_subtype_val).mul continuous_const :
      Continuous (fun n : (rP).ker => ((n : P) : G) * s l))
  exact (kernelCharacter_isLocallyConstant r s hrs P hker θ).comp₂ hf
    (fun c v => Jacquet.Localization.mk σP A η ((c⁻¹ : ℂˣ) • v))

/-- Local constancy descends through the actual left quotient topology. -/
theorem integrandFunction_isLocallyConstant (f : CompactFunctions H σ) (l : L) :
    IsLocallyConstant (integrandFunction r s hrs P H hker hHP θ σ f l) := by
  intro t
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel I)).isCoinducing.isOpen_preimage.mp
  exact kernelFunction_isLocallyConstant r s hrs P H hker hHP θ σ f l t

local notation "slice" => splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ
local notation "σI" => MonoidHom.comp σP (MonoidHom.subgroupComap (Subgroup.subtype (MonoidHom.ker rP)) HP)

/-- Localization may shrink support; it remains inside the actual compact kernel slice. -/
theorem support_integrandFunction_subset (f : CompactFunctions H σ) (l : L) :
    Function.support (integrandFunction r s hrs P H hker hHP θ σ f l) ⊆
      quotientSupport I (eval I σI (slice f l).val) := by
  intro q hq
  obtain ⟨n, rfl⟩ := Quotient.exists_rep q
  refine ⟨n, ?_, rfl⟩
  intro hn
  apply hq
  change Jacquet.Localization.mk σP A η
    (((θP n)⁻¹ : ℂˣ) • eval I σI (slice f l).val n) = 0
  rw [hn, smul_zero, map_zero]

include hr hs hP hH hsH hσ in
/-- Compact support is inherited from the actual compact, closed slice support. -/
theorem integrandFunction_hasCompactSupport (f : CompactFunctions H σ) (l : L) :
    HasCompactSupport (integrandFunction r s hrs P H hker hHP θ σ f l) := by
  apply (slice f l).property.of_isClosed_subset isClosed_closure
  exact closure_minimal
    (support_integrandFunction_subset r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l)
    (isClosed_quotientSupport I σI (slice f l).val)

variable [MeasurableSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable [BorelSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]

/-- The canonical descended integrand as the actual compactly supported simple function. -/
def integrand (f : CompactFunctions H σ) (l : L) : SimpleFunc (LeftQuotient I) C :=
  compactlySupportedSimpleFunc
    (integrandFunction r s hrs P H hker hHP θ σ f l)
    (integrandFunction_isLocallyConstant r s hrs P H hker hHP θ σ f l)
    (integrandFunction_hasCompactSupport r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l)

/-- Its value on every quotient representative is the prescribed inverse weight. -/
@[simp] theorem integrand_mk (f : CompactFunctions H σ) (l : L) (n : (rP).ker) :
    integrand r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l (quotientMap I n) =
      Jacquet.Localization.mk σP A η
        (((θP n)⁻¹ : ℂˣ) • eval H σ f.val (((n : P) : G) * s l)) := rfl

/-- Finiteness on compact sets gives finite measure to each nonzero fiber. -/
theorem integrand_finMeasSupp (ν : Measure (LeftQuotient I)) [IsFiniteMeasureOnCompacts ν]
    (f : CompactFunctions H σ) (l : L) :
    (integrand r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l).FinMeasSupp ν :=
  compactlySupportedSimpleFunc_finMeasSupp ν _ _ _

end Langlands.Induction.SplitStagesCharacter
