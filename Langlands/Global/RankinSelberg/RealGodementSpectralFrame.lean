import Langlands.Global.RankinSelberg.RealGodementCompactFrame
import Langlands.Global.RankinSelberg.RealGodementCompactProfile
import Langlands.Global.RankinSelberg.RealGodementFiniteGeneration
import Langlands.Global.RankinSelberg.RealGodementParametricSection

/-! # Fixed compact Godement generators over all real character exponents -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula RealGodementProfiles RealJacquetFrobenius RealUniformWhittakerDual

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "K" => unitaryCompact ℝ (m + 1)
local notation "U" => Matrix.unitaryGroup (Fin (m + 1)) ℝ
local notation "P" => (Fin (m + 1) → ℂ)

private def orthogonalPoint : U →* K where
  toFun u := ⟨Unitary.toUnits u, u.property⟩
  map_one' := Subtype.ext (map_one Unitary.toUnits)
  map_mul' u v := Subtype.ext (map_mul Unitary.toUnits u v)

/-- The profile on orthogonal matrices associated to a function on the compact subgroup of GL. -/
def frameProfile (f : K → ℂ) : U → ℂ := f ∘ orthogonalPoint

@[simp] theorem compactSectionRestriction_standardSection_frameProfile (z : P) (f : K → ℂ) :
    compactSectionRestriction (standardSection z (frameProfile f)) = f := by
  funext k
  let u : U := ⟨k.val.val, k.property⟩
  have hu : Unitary.toUnits u = k.val := Units.ext rfl
  change standardSection z (frameProfile f) k.val = f k
  rw [← hu]
  exact (congrFun (compactRestriction_standardSection (frameProfile f) z) u).trans
    (congrArg f (Subtype.ext hu))

private theorem isCompactProfile_of_leftStable {p : Fin (m + 1) → Fin 2} {z : P}
    (W : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    {F : H → ℂ} (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (characterList p z)))
    (hFW : compactSectionRestriction F ∈ W) :
    IsCompactProfile p (compactRestriction F) := by
  apply isCompactProfile_of_mem_principalSeries hF
  let L (u : U) : W :=
    ⟨fun k => compactSectionRestriction F (orthogonalPoint u * k), hW _ hFW (orthogonalPoint u)⟩
  let T : Module.Dual ℂ W →ₗ[ℂ] (U → ℂ) := {
    toFun a u := a (L u)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T)
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  refine ⟨(LinearMap.proj (orthogonalPoint u)).comp W.subtype, funext fun v => ?_⟩
  change F (Unitary.toUnits v * Unitary.toUnits u) = F (Unitary.toUnits (v * u))
  rw [map_mul]

/-- The functions in a common compact subspace that have the specified principal-series signs. -/
def spectralFrameSpace (p : Fin (m + 1) → Fin 2) (W : Submodule ℂ (K → ℂ)) :
    Submodule ℂ (K → ℂ) :=
  W ⊓ (principalSeries ℝ (m + 1) (realPositionCharacter (characterList p 0))).map
    compactSectionRestriction

theorem isCompactProfile_frameProfile {p : Fin (m + 1) → Fin 2} {W : Submodule ℂ (K → ℂ)}
    [FiniteDimensional ℂ W] (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    {f : K → ℂ} (hf : f ∈ spectralFrameSpace p W) : IsCompactProfile p (frameProfile f) := by
  obtain ⟨hfW, F, hF, rfl⟩ := hf
  exact isCompactProfile_of_leftStable W hW hF hfW

theorem mem_spectralFrameSpace_of_principalSeries {p : Fin (m + 1) → Fin 2} {z : P}
    {W : Submodule ℂ (K → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    {F : H → ℂ} (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (characterList p z)))
    (hFW : compactSectionRestriction F ∈ W) : compactSectionRestriction F ∈ spectralFrameSpace p W := by
  have hProfile : IsCompactProfile p (frameProfile (compactSectionRestriction F)) :=
    isCompactProfile_of_leftStable W hW hF hFW
  exact ⟨hFW, standardSection 0 _, (standardSection_mem hProfile 0).1.1,
    compactSectionRestriction_standardSection_frameProfile 0 _⟩

/-- A Godement generator with a fixed lower compact profile and a fixed compact test.
Its upper compact restrictions stay in the common space for all exponents. -/
structure SpectralSectionFamily [MeasurableSpace G] (μ : Measure G) (p : Fin (m + 1) → Fin 2)
    (W : Submodule ℂ (K → ℂ)) where
  lower : Matrix.unitaryGroup (Fin m) ℝ → ℂ
  lower_profile : IsCompactProfile (fun i => p i.succ) lower
  support : Set X
  support_compact : IsCompact support
  support_fullRank : ∀ x ∈ support, HasFullRowRank x
  test : 𝓢(X, ℂ)
  test_zero : ∀ x ∉ support, test x = 0
  compact_mem : ∀ z : P, compactSectionRestriction
    (sectionValue μ (charData (p 0) (z 0)) (standardSection (fun i => z i.succ) lower) test) ∈ W

section Sections

variable [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
variable {μ : Measure (Langlands.GeneralLinear m ℝ)} {p : Fin (m + 1) → Fin 2}
variable {W : Submodule ℂ (unitaryCompact ℝ (m + 1) → ℂ)}

/-- The standard lower section of a fixed spectral generator. -/
def SpectralSectionFamily.lowerSection (C : SpectralSectionFamily μ p W) (z : P) : G → ℂ :=
  standardSection (fun i => z i.succ) C.lower

/-- The section at the selected exponent vector. -/
def SpectralSectionFamily.upperSection (C : SpectralSectionFamily μ p W) (z : P) : H → ℂ :=
  sectionValue μ (charData (p 0) (z 0)) (C.lowerSection z) C.test

/-- The upper compact restriction of a spectral generator. -/
def SpectralSectionFamily.column (C : SpectralSectionFamily μ p W) (z : P) : K → ℂ :=
  compactSectionRestriction (C.upperSection z)

variable [BorelSpace (Langlands.GeneralLinear m ℝ)] [IsFiniteMeasureOnCompacts μ]

theorem SpectralSectionFamily.differentiable_section (C : SpectralSectionFamily μ p W) (g : H) :
    Differentiable ℂ (fun z : P => C.upperSection z g) := by
  unfold SpectralSectionFamily.upperSection
  have hTail : Differentiable ℂ (fun (z : P) (i : Fin m) => z i.succ) :=
    differentiable_pi.mpr fun i => (ContinuousLinearMap.proj i.succ : P →L[ℂ] ℂ).differentiable
  have hPair : Continuous (fun q : P × G => ((fun i : Fin m => q.1 i.succ), q.2)) :=
    (hTail.continuous.comp continuous_fst).prodMk continuous_snd
  have hLowerJoint : Continuous (fun q : (Fin m → ℂ) × G => standardSection q.1 C.lower q.2) :=
    continuous_standardSection_family C.lower_profile.1
  have hJoint : Continuous (fun q : P × G => C.lowerSection q.1 q.2) := by
    simpa only [Function.comp_def, SpectralSectionFamily.lowerSection] using hLowerJoint.comp hPair
  have hPoint (h : G) : Differentiable ℂ (fun z : P => C.lowerSection z h) := by
    have hLower := differentiable_standardSection C.lower h
    simpa only [Function.comp_def, SpectralSectionFamily.lowerSection] using hLower.comp hTail
  have hHead : Differentiable ℂ (fun z : P => z 0) :=
    (ContinuousLinearMap.proj 0 : P →L[ℂ] ℂ).differentiable
  have hTest : Continuous (C.test : X → ℂ) := C.test.continuous
  exact realGodementParametricSection (m := m) (n := m + 1) μ (p 0) (fun z : P => z 0) hHead
    C.lowerSection hJoint hPoint C.support C.support_compact C.support_fullRank _ hTest C.test_zero g

variable [Measure.IsMulRightInvariant μ]

theorem SpectralSectionFamily.section_mem_principalSeries
    (C : SpectralSectionFamily μ p W) (z : P) :
    C.upperSection z ∈ principalSeries ℝ (m + 1) (realPositionCharacter (characterList p z)) := by
  rw [characterList_cons]
  exact realGodementSection m μ _ _ _ (standardSection_mem C.lower_profile _).1.1
    C.support C.support_compact C.support_fullRank C.test C.test.smooth' C.test_zero

theorem SpectralSectionFamily.column_mem [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    (C : SpectralSectionFamily μ p W) (z : P) : C.column z ∈ spectralFrameSpace p W :=
  mem_spectralFrameSpace_of_principalSeries hW (C.section_mem_principalSeries z) (C.compact_mem z)

theorem SpectralSectionFamily.section_eq_standardSection [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    (C : SpectralSectionFamily μ p W) (z : P) :
    C.upperSection z = standardSection z (frameProfile (C.column z)) := by
  have hProfile := isCompactProfile_frameProfile hW (C.column_mem hW z)
  apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries (C.section_mem_principalSeries z)
    (standardSection_mem hProfile z).1.1
  intro g hg
  exact (congrFun (compactSectionRestriction_standardSection_frameProfile z (C.column z))
    (⟨g, hg⟩ : K)).symm

private def spectralGramFamily [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W)
    (z : P) {F : H → ℂ} (hF : F ∈ principalSeries ℝ (m + 1)
      (realPositionCharacter (.character (charData (p 0) (z 0)) ::
        characterList (fun i => p i.succ) (fun i => z i.succ))))
    (hFW : compactSectionRestriction F ∈ W) {S : Set M} (hS : IsCompact S)
    (hUnit : ∀ y ∈ S, IsUnit y) {β : M → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβZero : ∀ y ∉ S, β y = 0) {φ : Matrix.unitaryGroup (Fin m) ℝ → ℂ}
    (hφ : IsCompactProfile (fun i => p i.succ) φ) : SpectralSectionFamily μ p W := by
  let Φ := gramTest (charData (p 0) (z 0)) F β
  have hT : IsCompact (rowGram ⁻¹' S) := isCompact_rowGram_preimage hS
  have hZero (x : X) (hx : x ∉ rowGram ⁻¹' S) : Φ x = 0 :=
    gramTest_eq_zero _ _ hβZero hx
  have hCompact : HasCompactSupport Φ :=
    hT.of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ hx => by_contra fun h => hx (hZero _ h)) hT.isClosed)
  refine ⟨φ, hφ, rowGram ⁻¹' S, hT,
    fun x hx => hasFullRowRank_of_isUnit_rowGram (hUnit (rowGram x) hx),
    hCompact.toSchwartzMap (contDiff_gramTest _ _ hF hS.isClosed hUnit hβ hβZero), hZero, ?_⟩
  intro w
  exact compactGramSection_mem μ (p 0) (z 0) _ W hW hF hFW hS hUnit hβ.continuous hβZero
    (standardSection_mem hφ (fun i => w i.succ)).1.1.1.continuous (w 0)

end Sections

/-- Compact sections with fixed lower profiles and fixed compact full-row-rank
tests span the same prescribed finite compact space at every upper exponent vector. -/
def RealGodementSpectralFrameStatement (m : ℕ) : Prop :=
  ∀ [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] [Measure.IsMulRightInvariant μ],
  ∀ (p : Fin (m + 1) → Fin 2) (W : Submodule ℂ (unitaryCompact ℝ (m + 1) → ℂ))
    [FiniteDimensional ℂ W],
    (∀ f ∈ W, ∀ q : unitaryCompact ℝ (m + 1),
      (fun k : unitaryCompact ℝ (m + 1) => f (q * k)) ∈ W) →
    ∀ z : Fin (m + 1) → ℂ, Submodule.span ℂ (Set.range fun C : SpectralSectionFamily μ p W => C.column z) =
      spectralFrameSpace p W

theorem realGodementSpectralFrame : RealGodementSpectralFrameStatement m := by
  intro _ _ μ _ _ _ p W _ hW z
  let V : Submodule ℂ (K → ℂ) := Submodule.span ℂ (Set.range fun C : SpectralSectionFamily μ p W =>
    C.column z)
  have hle : V ≤ spectralFrameSpace p W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨C, rfl⟩
    exact C.column_mem hW z
  let : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  refine le_antisymm hle fun f hf => ?_
  let F := standardSection z (frameProfile f)
  have hF := (standardSection_mem (isCompactProfile_frameProfile hW hf) z).1.1
  rw [characterList_cons] at hF
  have hEq : compactSectionRestriction F = f :=
    compactSectionRestriction_standardSection_frameProfile z f
  have hFW : compactSectionRestriction F ∈ W := hEq.symm ▸ hf.1
  let c := charData (p 0) (z 0)
  let ds := characterList (fun i => p i.succ) (fun i => z i.succ)
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose S β b hS hUnit hβ hZero hb hError using fun j : ℕ =>
    realGodementCompactApproximation m μ c ds F hF (ε j) (hε j)
  let Q (j : ℕ) := compactSectionRestriction (sectionValue μ c (lowerCutoff ds (b j))
    (gramTest c F (β j)))
  have hQ (j : ℕ) : Q j ∈ V := by
    obtain ⟨r, hr⟩ := exists_polynomial_gramSection_tendsto μ c ds hF (hS j) (hUnit j)
      (hβ j).continuous (hZero j) (hb j).continuous
    let L (i : ℕ) : G → ℂ := lowerCutoff ds (r i).eval
    have hL (i : ℕ) : L i ∈ Automorphic.realStandardKFinite m ds := by
      change L i ∈ Automorphic.realStandardKFinite m
        (characterList (fun i => p i.succ) (fun i => z i.succ))
      rw [characterList, standardKFinite_map_character]
      exact lowerCutoff_polynomial_mem_kFiniteFunctions ds (r i)
    let C (i : ℕ) : SpectralSectionFamily μ p W :=
      spectralGramFamily hW z hF hFW (hS j) (hUnit j) (hβ j) (hZero j)
        (isCompactProfile_compactRestriction (hL i))
    have hColumn (i : ℕ) : (C i).column z =
        compactSectionRestriction (sectionValue μ c (L i) (gramTest c F (β j))) := by
      change compactSectionRestriction (sectionValue μ c
        (standardSection (fun i => z i.succ) (compactRestriction (L i))) (gramTest c F (β j))) = _
      rw [standardSection_compactRestriction (hL i)]
    have hLim : Tendsto (fun i => (C i).column z) atTop (𝓝 (Q j)) := by
      simp_rw [hColumn]
      exact tendsto_pi_nhds.mpr hr
    exact V.closed_of_finiteDimensional.mem_of_tendsto hLim
      (Eventually.of_forall fun i => Submodule.subset_span ⟨C i, rfl⟩)
  have hLim : Tendsto Q atTop (𝓝 f) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ => dist_nonneg) (fun j => ?_)
    rw [dist_eq_norm, ← hEq]
    exact (hError j k.val k.property).le
  exact V.closed_of_finiteDimensional.mem_of_tendsto hLim (Eventually.of_forall hQ)

end Langlands.Global.RankinSelbergGlobal.RealGodement
