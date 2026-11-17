import Langlands.JacquetLanglands.LocalCharacter

/-! # Generic twisted distribution characters and their local values -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands

universe uG uV

section Distribution

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)

/-- The finite-rank trace of the integrated action followed by `A`. -/
def twistedDistribution (A : Module.End ℂ V) : Distribution G :=
  FiniteRankEnd.trace.comp
    ({
      toFun := fun f => ⟨(Character.finiteRankIntegratedAction μ ρ hρ f).val.comp A,
        (Character.finiteRankIntegratedAction μ ρ hρ f).property.comp_right A⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        simp [LinearMap.add_comp]
      map_smul' := by
        intro a f
        apply Subtype.ext
        simp [LinearMap.smul_comp] } : SchwartzBruhat G →ₗ[ℂ] finiteRankEnd V)

@[simp]
theorem twistedDistribution_apply (A : Module.End ℂ V) (f : SchwartzBruhat G) :
    twistedDistribution μ ρ hρ A f = FiniteRankEnd.trace
      ⟨(Character.finiteRankIntegratedAction μ ρ hρ f).val.comp A,
        (Character.finiteRankIntegratedAction μ ρ hρ f).property.comp_right A⟩ := rfl

/-- The identity twist gives the ordinary character distribution. -/
@[simp]
theorem twistedDistribution_one :
    twistedDistribution μ ρ hρ 1 = Character.distribution μ ρ hρ := by
  ext f
  rw [twistedDistribution_apply, Character.distribution_apply]
  congr 1

/-- Scaling the twisting endomorphism scales its distribution. -/
theorem twistedDistribution_smul (a : ℂ) (A : Module.End ℂ V) :
    twistedDistribution μ ρ hρ (a • A) = a • twistedDistribution μ ρ hρ A := by
  ext f
  let T := Character.finiteRankIntegratedAction μ ρ hρ f
  change FiniteRankEnd.trace (⟨T.val.comp (a • A), T.property.comp_right _⟩ : finiteRankEnd V) =
    a • FiniteRankEnd.trace (⟨T.val.comp A, T.property.comp_right _⟩ : finiteRankEnd V)
  rw [← map_smul]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  exact LinearMap.comp_smul _ _ _

end Distribution

section LocalValue

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A twisted character value, relative to every Haar measure with the Borel sigma-algebra. -/
def HasTwistedCharacterValue (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) (g : G) (c : ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  ∀ (μ : Measure G) [μ.IsHaarMeasure], HasLocalValue μ (twistedDistribution μ ρ hρ A) g c

/-- Identity-twisted values are the existing ordinary character values. -/
@[simp]
theorem hasTwistedCharacterValue_one_iff (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (g : G) (c : ℂ) :
    HasTwistedCharacterValue ρ hρ 1 g c ↔ HasCharacterValue ρ hρ g c := by
  simp only [HasTwistedCharacterValue, HasCharacterValue, twistedDistribution_one]

/-- The value at a given point is unique. -/
theorem HasTwistedCharacterValue.unique {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}
    {A : Module.End ℂ V} {g : G} {c c' : ℂ}
    (h : HasTwistedCharacterValue ρ hρ A g c)
    (h' : HasTwistedCharacterValue ρ hρ A g c') : c = c' := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  exact (h Measure.haar).unique (h' Measure.haar)

/-- Scaling an endomorphism scales its local twisted character value. -/
theorem HasTwistedCharacterValue.smul {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}
    {A : Module.End ℂ V} {g : G} {c : ℂ}
    (h : HasTwistedCharacterValue ρ hρ A g c) (a : ℂ) :
    HasTwistedCharacterValue ρ hρ (a • A) g (a * c) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨U, hU, hg, hf⟩ := h μ
  refine ⟨U, hU, hg, fun f hsupp => ?_⟩
  rw [twistedDistribution_smul, LinearMap.smul_apply, hf f hsupp, smul_eq_mul, mul_assoc]

/-- In finite dimension, the twisted character at `g` is `trace (ρ(g) ∘ A)`. -/
theorem hasTwistedCharacterValue_trace [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (A : Module.End ℂ V) (g₀ : G) :
    HasTwistedCharacterValue ρ hρ A g₀ (LinearMap.trace ℂ V (ρ g₀ ∘ₗ A)) := by
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
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_ambient]
  change LinearMap.trace ℂ V ((Hecke.integratedAction μ ρ hρ.1 f) ∘ₗ A) = _
  rw [hact, LinearMap.smul_comp, map_smul, smul_eq_mul, mul_comm]

end LocalValue

end Langlands.BaseChange
