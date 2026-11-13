import Langlands.Representation.Character.Basic
import Langlands.Representation.Hecke.IntegratedAction
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Separation.Profinite

/-!
# Local values of distribution characters

A distribution `Θ` on a locally profinite space has the value `c` at `x`, relative to a
measure `μ`, when `Θ = c • μ` on test functions supported near `x`. For the distribution
character of an admissible representation this expresses that Harish-Chandra's character
function is locally constant near `x` with value `c`.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory HarmonicAnalysis

universe uX uG uH uV uW

section LocalValue

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]

/-- The distribution `Θ` has the local value `c` at `x` relative to the measure `μ`: on some
open neighbourhood `U` of `x`, `Θ f = c * ∫ f dμ` for every test function supported in `U`. -/
def HasLocalValue (μ : Measure X) (Θ : Distribution X) (x : X) (c : ℂ) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ f : SchwartzBruhat X, Function.support f ⊆ U → Θ f = c * ∫ y, f y ∂μ

omit [MeasurableSpace X] in
/-- In a locally compact, Hausdorff, totally disconnected space every open neighbourhood of a
point contains a compact open neighbourhood of it. -/
theorem exists_isCompact_isClopen_subset [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ K : Set X, IsCompact K ∧ IsClopen K ∧ x ∈ K ∧ K ⊆ U := by
  obtain ⟨L, hL, hxL, hLU⟩ := exists_compact_subset hU hx
  obtain ⟨K, hK, hxK, hKL⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (isOpen_interior.mem_nhds hxL)
  exact ⟨K, hL.of_isClosed_subset hK.1 (hKL.trans interior_subset), hK, hxK,
    (hKL.trans interior_subset).trans hLU⟩

/-- A local value is unique for a measure that is finite on compact sets and positive on
nonempty open sets. -/
theorem HasLocalValue.unique [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {Θ : Distribution X} {x : X} {c c' : ℂ}
    (h : HasLocalValue μ Θ x c) (h' : HasLocalValue μ Θ x c') : c = c' := by
  obtain ⟨U, hU, hxU, hf⟩ := h
  obtain ⟨U', hU', hxU', hf'⟩ := h'
  obtain ⟨K, hKc, hKo, hxK, hKU⟩ :=
    exists_isCompact_isClopen_subset (hU.inter hU') ⟨hxU, hxU'⟩
  let f := Hecke.TestFunction.characteristic hKo hKc
  have hsupp : Function.support (f : X → ℂ) = K :=
    Hecke.TestFunction.support_characteristic hKo hKc
  have h1 := hf f (hsupp ▸ hKU.trans Set.inter_subset_left)
  have h2 := hf' f (hsupp ▸ hKU.trans Set.inter_subset_right)
  have hint : ∫ y, f y ∂μ = ((μ K).toReal : ℂ) := by
    change ∫ y, K.indicator (fun _ => (1 : ℂ)) y ∂μ = _
    rw [integral_indicator_const _ hKo.isClosed.measurableSet, Measure.real]
    simp
  have hpos : ((μ K).toReal : ℂ) ≠ 0 := by
    have h0 : 0 < μ K := hKo.isOpen.measure_pos μ ⟨x, hxK⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h0.ne' hKc.measure_lt_top.ne).ne'
  rw [hint] at h1 h2
  exact mul_right_cancel₀ hpos (h1.symm.trans h2)

end LocalValue

section Character

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The character of the admissible representation `ρ` has the value `c` at `g`: for every
Haar measure `μ` on `G` (with the Borel σ-algebra), the distribution character
`Character.distribution μ ρ hρ` has the local value `c` at `g` relative to `μ`. -/
def HasCharacterValue (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (g : G) (c : ℂ) :
    Prop :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  ∀ (μ : Measure G) [μ.IsHaarMeasure], HasLocalValue μ (Character.distribution μ ρ hρ) g c

/-- The character value at a point is unique. -/
theorem HasCharacterValue.unique {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ} {g : G}
    {c c' : ℂ} (h : HasCharacterValue ρ hρ g c) (h' : HasCharacterValue ρ hρ g c') :
    c = c' := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  exact (h Measure.haar).unique (h' Measure.haar)

/-- Character values are invariant under equivalence of representations. -/
theorem hasCharacterValue_iff_of_equivariant {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (σ : Representation ℂ G W)
    (hσ : IsAdmissible σ) (E : V ≃ₗ[ℂ] W) (hE : ∀ g v, E (ρ g v) = σ g (E v)) (g : G)
    (c : ℂ) : HasCharacterValue ρ hρ g c ↔ HasCharacterValue σ hσ g c := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  constructor
  · intro h μ _
    rw [← Character.distribution_eq_of_equivariant μ ρ hρ σ hσ E hE]
    exact h μ
  · intro h μ _
    rw [Character.distribution_eq_of_equivariant μ ρ hρ σ hσ E hE]
    exact h μ

/-- Comparison of character values with a sign `s`: given the values `a` of `ρ` at `g` and
`b` of `σ` at `h`, a common witness `c` with values `s * c` and `c` exists exactly when
`a = s * b`. -/
theorem exists_hasCharacterValue_mul_iff {H : Type uH} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ} {σ : Representation ℂ H W}
    {hσ : IsAdmissible σ} {g : G} {h : H} {a b : ℂ} (s : ℂ)
    (ha : HasCharacterValue ρ hρ g a) (hb : HasCharacterValue σ hσ h b) :
    (∃ c, HasCharacterValue ρ hρ g (s * c) ∧ HasCharacterValue σ hσ h c) ↔ a = s * b := by
  constructor
  · rintro ⟨c, hc, hc'⟩
    rw [ha.unique hc, hb.unique hc']
  · rintro rfl
    exact ⟨b, ha, hb⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- A finite-dimensional smooth representation is admissible. -/
theorem isAdmissible_of_finiteDimensional [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) : IsAdmissible ρ :=
  ⟨hρ, fun _ => inferInstance⟩

/-- The character of a finite-dimensional smooth representation has, at every point `g₀`,
the value `trace ρ(g₀)`. Near `g₀` the representation is constant, so the integrated action
of a test function `f` supported there is `(∫ f dμ) • ρ(g₀)`. -/
theorem hasCharacterValue_trace [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (g₀ : G) :
    HasCharacterValue ρ hρ g₀ (LinearMap.trace ℂ V (ρ g₀)) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  let b := Module.finBasis ℂ V
  let U : Set G := ⋂ i, {g | ρ g (b i) = ρ g₀ (b i)}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    (Hecke.orbitMap_locallyConstant ρ (hρ.1 (b i))).isOpen_fiber _
  have hconst : ∀ g ∈ U, ρ g = ρ g₀ := by
    intro g hg
    exact b.ext fun i => Set.mem_iInter.1 hg i
  refine ⟨U, hU, Set.mem_iInter.2 fun i => rfl, fun f hf => ?_⟩
  have hact : Hecke.integratedAction μ ρ hρ.1 f = (∫ y, f y ∂μ) • ρ g₀ := by
    ext v
    refine b.ext_elem fun i => ?_
    rw [← b.coord_apply, ← b.coord_apply, Hecke.integratedAction_dual, LinearMap.smul_apply,
      map_smul, smul_eq_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : f y = 0
    · simp [hy]
    · simp only
      rw [hconst y (hf hy)]
  rw [Character.distribution_apply, FiniteRankEnd.trace_eq_ambient,
    Character.finiteRankIntegratedAction_coe, hact, map_smul, smul_eq_mul, mul_comm]

end Character

end Langlands.JacquetLanglands
