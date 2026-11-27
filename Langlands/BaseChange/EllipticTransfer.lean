import Langlands.BaseChange.EllipticLocusClopen
import Langlands.BaseChange.EllipticTransferStatement
import Langlands.BaseChange.RegularEllipticOpen
import Langlands.BaseChange.RegularTransfer

/-!
# Transfer of test functions supported in the elliptic sets

This module proves `EllipticTransferStatement` (Henniart–Lemaire 2011, I.2.5, Proposition,
restricted to the elliptic sets, as used in II.6.10) from the regular transfer
`regularTransfer` by cutting the transferred function off with the indicator of the regular
elliptic set of `GL_n(F)`, respectively of the σ-elliptic set of `GL_n(E)`. The cut-off is
again a Schwartz–Bruhat function because these sets and their complements in the
(σ-)regular sets are open (`Langlands.BaseChange.EllipticLocusClopen`), and it keeps
concordance because these sets are unions of (σ-)conjugacy classes. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat schwartzBruhatSubmodule)
open Langlands.JacquetLanglands Langlands.TraceFormula Langlands.QuotientIntegration

universe u v

attribute [local instance high] leftQuotientMeasurableSpace

section CutOff

variable {X : Type*} [TopologicalSpace X]

/-- Cutting a Schwartz–Bruhat function off by the indicator of an open set `U` gives a
Schwartz–Bruhat function, provided its support lies in the union of `U` and an open set `V`
disjoint from `U`. -/
theorem indicator_mem_schwartzBruhatSubmodule (φ : SchwartzBruhat X) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hφ : ∀ x, φ x ≠ 0 → x ∈ U ∪ V) :
    U.indicator (φ : X → ℂ) ∈ schwartzBruhatSubmodule X := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    (SchwartzBruhat.hasCompactSupport φ).mono
      fun x hx h0 => hx (Set.indicator_apply_eq_zero.mpr fun _ => h0)⟩
  have hφx : ∀ᶠ y in nhds x, φ y = φ x :=
    (IsLocallyConstant.iff_eventually_eq _).mp (SchwartzBruhat.locallyConstant φ) x
  by_cases hxU : x ∈ U
  · filter_upwards [hU.mem_nhds hxU, hφx] with y hyU hy
    rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hxU, hy]
  · by_cases hxV : x ∈ V
    · filter_upwards [hV.mem_nhds hxV] with y hyV
      rw [Set.indicator_of_notMem (Set.disjoint_right.mp hUV hyV),
        Set.indicator_of_notMem hxU]
    · have h0 : φ x = 0 := by
        by_contra hne
        rcases hφ x hne with h | h
        · exact hxU h
        · exact hxV h
      filter_upwards [hφx] with y hy
      rw [Set.indicator_of_notMem hxU]
      by_cases hyU : y ∈ U
      · rw [Set.indicator_of_mem hyU, hy, h0]
      · rw [Set.indicator_of_notMem hyU]

/-- The cut-off of a Schwartz–Bruhat function by the indicator of an open set `U`, when its
support lies in the union of `U` and an open set `V` disjoint from `U`. -/
def cutOff (φ : SchwartzBruhat X) {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hφ : ∀ x, φ x ≠ 0 → x ∈ U ∪ V) : SchwartzBruhat X :=
  ⟨U.indicator (φ : X → ℂ), indicator_mem_schwartzBruhatSubmodule φ hU hV hUV hφ⟩

theorem coe_cutOff (φ : SchwartzBruhat X) {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hφ : ∀ x, φ x ≠ 0 → x ∈ U ∪ V) :
    (cutOff φ hU hV hUV hφ : X → ℂ) = U.indicator (φ : X → ℂ) :=
  rfl

end CutOff

section Orbital

variable {G : Type*} [Group G] {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]

/-- If the twisted conjugacy class of `δ` lies in `U`, cutting `f` off by `U` does not change
the twisted orbit function at `δ`. -/
theorem twistedOrbitFunction_indicator_of_mem (θ : Θ) {δ : G} {U : Set G}
    (hU : ∀ x : G, x⁻¹ * δ * θ x ∈ U) (f : G → ℂ) :
    twistedOrbitFunction θ δ (U.indicator f) = twistedOrbitFunction θ δ f := by
  funext q
  induction q using Quotient.ind with
  | _ x =>
    rw [twistedOrbitFunction_mk, twistedOrbitFunction_mk, Set.indicator_of_mem (hU x)]

/-- If the twisted conjugacy class of `δ` does not meet `U`, the twisted orbit function at `δ`
of a function cut off by `U` vanishes. -/
theorem twistedOrbitFunction_indicator_of_forall_notMem (θ : Θ) {δ : G} {U : Set G}
    (hU : ∀ x : G, x⁻¹ * δ * θ x ∉ U) (f : G → ℂ) :
    twistedOrbitFunction θ δ (U.indicator f) = 0 := by
  funext q
  induction q using Quotient.ind with
  | _ x =>
    rw [twistedOrbitFunction_mk, Set.indicator_of_notMem (hU x)]
    rfl

theorem twistedOrbitalIntegral_indicator_of_mem (θ : Θ) {δ : G} {U : Set G}
    (hU : ∀ x : G, x⁻¹ * δ * θ x ∈ U) [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G → ℂ) :
    twistedOrbitalIntegral θ δ ν (U.indicator f) = twistedOrbitalIntegral θ δ ν f := by
  unfold twistedOrbitalIntegral
  rw [twistedOrbitFunction_indicator_of_mem θ hU f]

theorem twistedOrbitalIntegral_indicator_of_forall_notMem (θ : Θ) {δ : G} {U : Set G}
    (hU : ∀ x : G, x⁻¹ * δ * θ x ∉ U) [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G → ℂ) :
    twistedOrbitalIntegral θ δ ν (U.indicator f) = 0 := by
  unfold twistedOrbitalIntegral
  rw [twistedOrbitFunction_indicator_of_forall_notMem θ hU f]
  exact integral_zero _ _

end Orbital

/-- Transfer of test functions supported in the elliptic sets (Henniart–Lemaire, I.2.5,
Proposition, restricted to the elliptic sets; II.6.10). -/
theorem ellipticTransfer : EllipticTransferStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n h
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μF μE hμF hμE
  obtain ⟨h1, h2⟩ := regularTransfer F E σ l n h μF μE
  -- The regular elliptic set and the σ-elliptic set, with their complements in the
  -- regular and σ-regular sets.
  set UF := {γ : GeneralLinear n F | IsRegularElliptic γ} with hUF
  set VF := {γ : GeneralLinear n F | IsRegularSemisimple γ ∧ ¬ IsRegularElliptic γ} with hVF
  set UE := {δ : GeneralLinear n E | IsSigmaElliptic σ l δ} with hUE
  set VE := {δ : GeneralLinear n E | IsSigmaRegular σ l δ ∧ ¬ IsSigmaElliptic σ l δ} with hVE
  have hUFo : IsOpen UF := isOpen_regularElliptic F n
  have hVFo : IsOpen VF := isOpen_setOf_isRegularSemisimple_and_not_isRegularElliptic n
  have hUEo : IsOpen UE := isOpen_setOf_isSigmaElliptic h n
  have hVEo : IsOpen VE := isOpen_setOf_isSigmaRegular_and_not_isSigmaElliptic h n
  have hUVF : Disjoint UF VF := Set.disjoint_left.mpr fun _ hU hV => hV.2 hU
  have hUVE : Disjoint UE VE := Set.disjoint_left.mpr fun _ hU hV => hV.2 hU
  have hcovF : ∀ γ : GeneralLinear n F, IsRegularSemisimple γ → γ ∈ UF ∪ VF := by
    intro γ hγ
    by_cases he : IsRegularElliptic γ
    · exact Or.inl he
    · exact Or.inr ⟨hγ, he⟩
  have hcovE : ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ → δ ∈ UE ∪ VE := by
    intro δ hδ
    by_cases he : IsSigmaElliptic σ l δ
    · exact Or.inl he
    · exact Or.inr ⟨hδ, he⟩
  -- Conjugation and σ-conjugation preserve the two sets.
  have hinvF : ∀ (γ : GeneralLinear n F) (x : GeneralLinear n F),
      x⁻¹ * γ * (MonoidHom.id (GeneralLinear n F)) x ∈ UF ↔ γ ∈ UF :=
    fun γ x => isRegularElliptic_conj_iff x γ
  have hinvE : ∀ (δ : GeneralLinear n E) (x : GeneralLinear n E),
      x⁻¹ * δ * entrywiseAut σ n x ∈ UE ↔ δ ∈ UE :=
    fun δ x => isSigmaElliptic_twistedConj_iff h x δ
  -- An elliptically supported function is its own cut-off.
  have hselfF : ∀ f : GeneralLinear n F → ℂ, IsEllipticSupported f → UF.indicator f = f := by
    intro f hf
    funext γ
    by_cases hγ : γ ∈ UF
    · exact Set.indicator_of_mem hγ f
    · rw [Set.indicator_of_notMem hγ]
      by_contra hne
      exact hγ (hf γ (Ne.symm hne))
  have hselfE : ∀ φ : GeneralLinear n E → ℂ, IsSigmaEllipticSupported σ l φ →
      UE.indicator φ = φ := by
    intro φ hφ
    funext δ
    by_cases hδ : δ ∈ UE
    · exact Set.indicator_of_mem hδ φ
    · rw [Set.indicator_of_notMem hδ]
      by_contra hne
      exact hδ (hφ δ (Ne.symm hne))
  refine ⟨fun φ hφ => ?_, fun f hf hfv => ?_⟩
  · -- Part (1): transfer `φ`, then cut off by the regular elliptic set.
    obtain ⟨f', hf'reg, hf'v, hf'c⟩ := h1 φ hφ.isSigmaRegularSupported
    refine ⟨cutOff f' hUFo hVFo hUVF fun γ hγ => hcovF γ (hf'reg γ hγ), ?_, ?_, ?_⟩
    · intro γ hγ
      by_contra he
      apply hγ
      change UF.indicator (f' : GeneralLinear n F → ℂ) γ = 0
      exact Set.indicator_of_notMem (s := UF) he _
    · intro γ hγ hnn μγ _ _ νγ hc
      rw [coe_cutOff]
      by_cases he : γ ∈ UF
      · rw [orbitalIntegral, twistedOrbitalIntegral_indicator_of_mem _
          (fun x => (hinvF γ x).mpr he)]
        exact hf'v γ hγ hnn μγ νγ hc
      · exact twistedOrbitalIntegral_indicator_of_forall_notMem _
          (fun x hx => he ((hinvF γ x).mp hx)) _ _
    · intro δ γ ha hγ μδ _ _ μγ _ _ νδ νγ hcδ hcγ hassoc
      rw [coe_cutOff]
      by_cases he : γ ∈ UF
      · rw [orbitalIntegral, twistedOrbitalIntegral_indicator_of_mem _
          (fun x => (hinvF γ x).mpr he)]
        exact hf'c δ γ ha hγ μδ μγ νδ νγ hcδ hcγ hassoc
      · have hδ : δ ∉ UE := fun hδ => he ((isSigmaElliptic_iff_of_isNormAssociated h ha).mp hδ)
        rw [orbitalIntegral, twistedOrbitalIntegral_indicator_of_forall_notMem _
          (fun x hx => he ((hinvF γ x).mp hx)), sigmaOrbitalIntegral, ← hselfE φ hφ,
          twistedOrbitalIntegral_indicator_of_forall_notMem _
            (fun x hx => hδ ((hinvE δ x).mp hx))]
  · -- Part (2): transfer `f`, then cut off by the σ-elliptic set.
    obtain ⟨φ', hφ'reg, -, hφ'c⟩ := h2 f hf.isRegularSupported hfv
    refine ⟨cutOff φ' hUEo hVEo hUVE fun δ hδ => hcovE δ (hφ'reg δ hδ), ?_, hfv, ?_⟩
    · intro δ hδ
      by_contra he
      apply hδ
      change UE.indicator (φ' : GeneralLinear n E → ℂ) δ = 0
      exact Set.indicator_of_notMem (s := UE) he _
    · intro δ γ ha hγ μδ _ _ μγ _ _ νδ νγ hcδ hcγ hassoc
      rw [coe_cutOff]
      by_cases he : γ ∈ UF
      · have hδ : δ ∈ UE := (isSigmaElliptic_iff_of_isNormAssociated h ha).mpr he
        rw [sigmaOrbitalIntegral, twistedOrbitalIntegral_indicator_of_mem _
          (fun x => (hinvE δ x).mpr hδ)]
        exact hφ'c δ γ ha hγ μδ μγ νδ νγ hcδ hcγ hassoc
      · have hδ : δ ∉ UE := fun hδ => he ((isSigmaElliptic_iff_of_isNormAssociated h ha).mp hδ)
        rw [sigmaOrbitalIntegral, twistedOrbitalIntegral_indicator_of_forall_notMem _
          (fun x hx => hδ ((hinvE δ x).mp hx)), orbitalIntegral, ← hselfF f hf,
          twistedOrbitalIntegral_indicator_of_forall_notMem _
            (fun x hx => he ((hinvF γ x).mp hx))]

end Langlands.BaseChange
