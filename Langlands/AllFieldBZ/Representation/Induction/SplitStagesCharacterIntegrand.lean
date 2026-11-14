import Langlands.AllFieldBZ.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Induction.SplitStagesCharacterIntegrand

/-!
# All-field port of `Langlands.Representation.Induction.SplitStagesCharacterIntegrand`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.SplitStagesCharacterIntegrand` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.Induction.SplitStagesCharacter
open Langlands.Induction.SplitStagesCharacter
open MeasureTheory
open Langlands.QuotientIntegration hiding LeftQuotient
open Langlands.HarmonicAnalysis
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
variable (θ : Langlands.Induction.SmoothCharacter ℂ r.ker)
variable (hθ : Langlands.Induction.SplitKernelLocalization.SectionInvariant r s θ.toMonoidHom)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)

local notation "K" => P.comap s
local notation "rP" => Langlands.Induction.splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "σP" => σ.comp φ
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rP)) HP
local notation "A" => Langlands.Induction.SplitKernelLocalization.kernelIntersection rP HP

local notation "θP" => Langlands.Induction.SmoothCharacter.toMonoidHom (kernelCharacter r s hrs P hker θ)
local notation "η" => Langlands.Induction.SplitKernelLocalization.intersectionCharacter rP θP HP
local notation "C" => Jacquet.Localization.Coinvariants σP A η

local notation "hSI" => section_mem s P H hsH
local notation "hθP" => sectionInvariant r s hrs P hker θ hθ
local notation "hHPc" => subgroup_closed P H hH

section Coefficient
variable [LocallyCompactSpace (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker]
variable [BorelSpace (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker]
variable [mI : MeasurableSpace ((H.subgroupOf P).comap
  (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [bI : BorelSpace ((H.subgroupOf P).comap
  (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker.subtype)]

end Coefficient
omit [T2Space G] [LocallyCompactSpace G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem _root_.Langlands.Induction.SplitStagesCharacter.kernelCharacter_isLocallyConstant : IsLocallyConstant θP := by
  apply (IsLocallyConstant.iff_exists_open θP).mpr
  intro x
  refine ⟨(fun y : (rP).ker => y * x⁻¹) ⁻¹' ((θP).ker : Set (rP).ker),
    (kernelCharacter r s hrs P hker θ).isOpen_ker.preimage
      (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change θP (y * x⁻¹) = 1 at hy
    exact mul_inv_eq_one.mp (by simpa only [map_mul, map_inv] using hy)

local notation "slice" => Langlands.Induction.splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σ hσ
local notation "σI" => MonoidHom.comp σP (MonoidHom.subgroupComap (Subgroup.subtype (MonoidHom.ker rP)) HP)

variable [MeasurableSpace (Langlands.Induction.LeftQuotient
  ((H.subgroupOf P).comap (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker.subtype))]
variable [BorelSpace (Langlands.Induction.LeftQuotient
  ((H.subgroupOf P).comap (Langlands.Induction.splitStagesRetraction r s hrs P hker).ker.subtype))]

end Langlands.AllFieldBZ.Induction.SplitStagesCharacter
