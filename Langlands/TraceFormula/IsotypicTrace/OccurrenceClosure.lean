import Langlands.Representation.Character.Basic
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Unitary.IntegratedOperator
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Irreducible

/-!
# The closure of a local occurrence in a Hilbert space

Let `σ` be an isometric action of a totally disconnected locally compact group `Gv` on a
Hilbert space `E` with continuous orbits, and let `j : V → E` be a nonzero `Gv`-equivariant
linear map from an irreducible admissible representation `ρ`. This module proves:

* the Bochner integral of a test function against the orbit of `j x` is `j` of the algebraic
  Hecke action (`map_integratedAction`);
* `j` is injective (`injective_of_isIrreducible`);
* every vector of the closure of the range of `j` that is fixed by an open subgroup lies in the
  range of `j` (`mem_range_of_mem_closure_of_fixed`), and every linear map with values in that
  closure whose values have open stabilizers factors through `j` (`liftThrough`).
-/

noncomputable section

open MeasureTheory Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula.IsotypicTrace

universe uG uE uV uW

section Comparison

variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv] [IsTopologicalGroup Gv]
  [MeasurableSpace Gv] [BorelSpace Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (σ : Gv →* (E →L[ℂ] E))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

omit [IsTopologicalGroup Gv] [CompleteSpace E] in
/-- A test function integrates every continuous orbit. -/
theorem testFunction_orbit_integrable (μ : Measure Gv) [IsFiniteMeasureOnCompacts μ]
    (hσcont : ∀ x, Continuous fun y => σ y x) (f : SchwartzBruhat Gv) (x : E) :
    Integrable (fun y => f y • σ y x) μ := by
  have hfc : Continuous (f : Gv → ℂ) := f.locallyConstant.continuous
  exact (hfc.smul (hσcont x)).integrable_of_hasCompactSupport
    (f.hasCompactSupport.smul_right)

/-- An equivariant linear map carries the algebraic Hecke action to the Bochner integral of
the orbit. -/
theorem map_integratedAction (μ : Measure Gv) [IsFiniteMeasureOnCompacts μ]
    (hσcont : ∀ x, Continuous fun y => σ y x) (hρ : IsSmooth ρ) (j : V →ₗ[ℂ] E)
    (hj : ∀ y x, j (ρ y x) = σ y (j x)) (f : SchwartzBruhat Gv) (x : V) :
    j (Hecke.integratedAction μ ρ hρ f x) = ∫ y, f y • σ y (j x) ∂μ := by
  apply ext_inner_left ℂ
  intro z
  rw [← integral_inner (testFunction_orbit_integrable σ μ hσcont f (j x))]
  have h : inner ℂ z (j (Hecke.integratedAction μ ρ hρ f x)) =
      ∫ g, f g * inner ℂ z (j (ρ g x)) ∂μ :=
    Hecke.integratedAction_dual μ ρ hρ f x ((innerₛₗ ℂ z).comp j)
  rw [h]
  congr 1
  funext y
  rw [inner_smul_right, hj]

end Comparison

section Injective

variable {Gv : Type uG} [Group Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (σ : Gv →* (E →L[ℂ] E))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

/-- The algebraic representation underlying an action by bounded operators. -/
def toRepresentation : Representation ℂ Gv E :=
  (ContinuousLinearMap.toLinearMapRingHom : (E →L[ℂ] E) →+* Module.End ℂ E).toMonoidHom.comp σ

@[simp]
theorem toRepresentation_apply (y : Gv) (x : E) : toRepresentation σ y x = σ y x := rfl

/-- A nonzero equivariant linear map out of an irreducible representation is injective. -/
theorem injective_of_isIrreducible (hirr : Representation.IsIrreducible ρ) (j : V →ₗ[ℂ] E)
    (hj : ∀ y x, j (ρ y x) = σ y (j x)) (hj0 : j ≠ 0) : Function.Injective j := by
  have := hirr
  let f : ρ.IntertwiningMap (toRepresentation σ) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ (toRepresentation σ) j hj
  rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
  · exact h
  · exfalso
    apply hj0
    ext v
    exact congrArg (fun g : ρ.IntertwiningMap (toRepresentation σ) => g v) h

end Injective

section Closure

variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv] [IsTopologicalGroup Gv]
  [MeasurableSpace Gv] [BorelSpace Gv] [T2Space Gv] [LocallyCompactSpace Gv]
  [TotallyDisconnectedSpace Gv] [SecondCountableTopology Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (σ : Gv →* (E →L[ℂ] E))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

omit [MeasurableSpace Gv] [BorelSpace Gv] [SecondCountableTopology Gv] in
/-- Every open subgroup contains a compact open subgroup (van Dantzig). -/
theorem exists_isCompact_openSubgroup_le (K : OpenSubgroup Gv) :
    ∃ L : OpenSubgroup Gv, IsCompact (L : Set Gv) ∧ L ≤ K :=
  ((Topology.LocallyProfiniteProof.vanDantzig Gv).mp
    Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one

/-- A vector of the closure of the range of an equivariant map out of an admissible
representation that is fixed by an open subgroup lies in the range. -/
theorem mem_range_of_mem_closure_of_fixed (μ : Measure Gv) [μ.IsHaarMeasure]
    (hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖) (hσcont : ∀ x, Continuous fun y => σ y x)
    (hρ : IsAdmissible ρ) (j : V →ₗ[ℂ] E) (hj : ∀ y x, j (ρ y x) = σ y (j x))
    (K : OpenSubgroup Gv) (w : E) (hw : w ∈ (LinearMap.range j).topologicalClosure)
    (hfix : ∀ k ∈ K, σ k w = w) : w ∈ LinearMap.range j := by
  obtain ⟨L, hLc, hLK⟩ := exists_isCompact_openSubgroup_le K
  let s : SchwartzBruhat Gv := Hecke.TestFunction.subgroupIndicator L hLc
  have hsc : Continuous (s : Gv → ℂ) := s.locallyConstant.continuous
  have hs_int : Integrable (s : Gv → ℂ) μ := hsc.integrable_of_hasCompactSupport
    s.hasCompactSupport
  have hσmeas : ∀ x : E, AEStronglyMeasurable (fun y => σ y x) μ :=
    fun x => (hσcont x).aestronglyMeasurable
  let Φ : E →L[ℂ] E := Langlands.Analysis.integratedIsometricAction μ σ hσnorm hσmeas s hs_int
  have hΦ : ∀ x, Φ x = ∫ y, s y • σ y x ∂μ := fun x => rfl
  let F : Submodule ℂ E := (fixedVectors ρ L.toSubgroup).map j
  have : Module.Finite ℂ (fixedVectors ρ L.toSubgroup) := hρ.2 L
  have : FiniteDimensional ℂ F := Module.Finite.map _ _
  have hFclosed : IsClosed (F : Set E) := F.closed_of_finiteDimensional
  have hΦrange : LinearMap.range j ≤ F.comap Φ.toLinearMap := by
    rintro _ ⟨v, rfl⟩
    change Φ (j v) ∈ F
    rw [hΦ, ← map_integratedAction σ ρ μ hσcont hρ.1 j hj s v]
    exact Submodule.mem_map_of_mem (Hecke.integratedAction_mem_fixedVectors μ ρ hρ.1
      (Hecke.TestFunction.subgroupIndicator_mem L hLc) v)
  have hΦW : Φ w ∈ F := by
    have hle : (LinearMap.range j).topologicalClosure ≤ F.comap Φ.toLinearMap :=
      Submodule.topologicalClosure_minimal _ hΦrange (hFclosed.preimage Φ.continuous)
    exact hle hw
  have hpt : ∀ y, s y • σ y w = s y • w := by
    intro y
    by_cases hy : y ∈ L
    · rw [hfix y (hLK hy)]
    · have h0 : s y = 0 := by
        simp [s, Hecke.TestFunction.subgroupIndicator_apply, hy]
      simp [h0]
  have hmass : ∫ y, s y ∂μ = (μ.real (L : Set Gv) : ℂ) := by
    simp only [s, Hecke.TestFunction.subgroupIndicator_apply]
    rw [integral_indicator_const _ L.isOpen.measurableSet]
    simp
  have hΦw : Φ w = (μ.real (L : Set Gv) : ℂ) • w := by
    rw [hΦ]
    simp_rw [hpt]
    rw [integral_smul_const, hmass]
  have hne : (μ.real (L : Set Gv) : ℂ) ≠ 0 :=
    Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ L hLc
  have hwF : w ∈ F := by
    have : w = (μ.real (L : Set Gv) : ℂ)⁻¹ • Φ w := by
      rw [hΦw, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact F.smul_mem _ hΦW
  obtain ⟨v, -, hv⟩ := hwF
  exact ⟨v, hv⟩

/-- A vector of the closure that is fixed by an open subgroup `K` is the image of a
`K`-fixed vector. -/
theorem exists_fixed_preimage_of_mem_closure (μ : Measure Gv) [μ.IsHaarMeasure]
    (hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖) (hσcont : ∀ x, Continuous fun y => σ y x)
    (hρ : IsAdmissible ρ) (j : V →ₗ[ℂ] E) (hj : ∀ y x, j (ρ y x) = σ y (j x))
    (hinj : Function.Injective j)
    (K : OpenSubgroup Gv) (w : E) (hw : w ∈ (LinearMap.range j).topologicalClosure)
    (hfix : ∀ k ∈ K, σ k w = w) : ∃ v ∈ fixedVectors ρ K.toSubgroup, j v = w := by
  obtain ⟨v, rfl⟩ :=
    mem_range_of_mem_closure_of_fixed σ ρ μ hσnorm hσcont hρ j hj K w hw hfix
  refine ⟨v, ?_, rfl⟩
  intro k
  apply hinj
  change j (ρ (k : Gv) v) = j v
  rw [hj]
  exact hfix k k.property

end Closure

section Lift

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- A linear map whose values lie in the range of an injective linear map factors through
it. -/
theorem exists_linearMap_lift (j : V →ₗ[ℂ] E) (hinj : Function.Injective j)
    (Φ : V' →ₗ[ℂ] E) (hΦ : ∀ x, Φ x ∈ LinearMap.range j) :
    ∃ Ψ : V' →ₗ[ℂ] V, ∀ x, j (Ψ x) = Φ x := by
  let e := LinearEquiv.ofInjective j hinj
  refine ⟨e.symm.toLinearMap ∘ₗ Φ.codRestrict (LinearMap.range j) hΦ, fun x => ?_⟩
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨Φ x, hΦ x⟩)
  simp only at h
  exact h

end Lift

end Langlands.TraceFormula.IsotypicTrace
