import Langlands.AllFieldBZ.Representation.Induction.InverseTranspose
import Langlands.Representation.Induction.SplitStagesComparison

/-!
# All-field port of `Langlands.Representation.Induction.SplitStagesComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.SplitStagesComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
open MeasureTheory
open MeasureTheory.Measure
open Langlands.QuotientIntegration hiding LeftQuotient
open Langlands.HarmonicAnalysis
open scoped NNReal
open scoped ENNReal
universe uG uL uV uW

section Transport
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {τ : Representation ℂ G W}

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Transport
section Assembly
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
variable (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
variable (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)

local notation "K" => P.comap s
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "σP" => σ.comp φ
local notation "ρP" => compactInduced HP σP
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P

include hsH in
omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem _root_.Langlands.Induction.splitStagesSection_mem (l : P.comap s) :
    sP l ∈ H.subgroupOf P := hsH l

include hσ in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem _root_.Langlands.Induction.splitStagesCoefficient_smooth : IsSmooth σP :=
  isSmooth_comp φ
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hσ

variable [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
variable [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [BorelSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [MeasurableSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable [BorelSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable (ν : Measure (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)))
variable [IsFiniteMeasureOnCompacts ν]
variable (hKernelBasis : ∀ O : Set (splitStagesRetraction r s hrs P hker).ker,
  IsOpen O → (1 : (splitStagesRetraction r s hrs P hker).ker) ∈ O →
    ∃ U : OpenSubgroup (splitStagesRetraction r s hrs P hker).ker,
      IsCompact (U : Set (splitStagesRetraction r s hrs P hker).ker) ∧
        (U : Set (splitStagesRetraction r s hrs P hker).ker) ⊆ O)
variable (μN : Measure (splitStagesRetraction r s hrs P hker).ker)
variable (μI : Measure
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype) μN μI ν)

local notation "hSI" => splitStagesSection_mem s P H hsH
local notation "hHPc" => (hH.preimage (continuous_subtype_val : Continuous P.subtype))
local notation "χ" => Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)
local notation "κ" => twist χ (splitKernelCoefficientAction rP sP HP hSI σP)

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)

variable (hN : IsClosed (r.ker : Set G))
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O)

end Assembly
end Langlands.AllFieldBZ.Induction
