import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.LinearAlgebra.FiniteRankTraceExact

/-!
# Exactness and vanishing properties of twisted distributions

* `twistedDistribution_shortExact`: the twisted distribution is additive on a short exact
  sequence of admissible representations whose twisting endomorphisms are compatible with
  the two maps.
* `FiniteRankEnd.trace_eq_zero_of_offDiagonal` and
  `twistedDistribution_eq_zero_of_offDiagonal`: an operator with zero diagonal blocks
  for a complete family of idempotents has trace zero. This applies when the twisting
  endomorphism permutes equivariant blocks without fixed blocks.
* `FiniteRankEnd.trace_eq_sum_of_resolution` and `twistedDistribution_eq_sum_diagonal`
  compute the trace from the diagonal components of an equivariant decomposition.
-/

noncomputable section

namespace Langlands

universe uV uι

namespace FiniteRankEnd

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A finite-rank endomorphism whose diagonal blocks `e i ∘ T ∘ e i` vanish, for a finite
family of idempotents `e i` with sum `1`, has trace zero. The idempotents need not commute
with each other or with `T`. -/
theorem trace_eq_zero_of_offDiagonal {ι : Type uι} [Fintype ι] (e : ι → Module.End ℂ V)
    (hsum : ∑ i, e i = 1) (hidem : ∀ i, e i ∘ₗ e i = e i) (T : finiteRankEnd V)
    (hT : ∀ i, e i ∘ₗ T.val ∘ₗ e i = 0) : trace T = 0 := by
  let S : ι → finiteRankEnd V := fun i => ⟨T.val ∘ₗ e i, T.property.comp_right (e i)⟩
  have hTS : T = ∑ i, S i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change T.val = ∑ i, T.val ∘ₗ e i
    ext v
    rw [LinearMap.sum_apply]
    simp only [LinearMap.comp_apply]
    rw [← map_sum, ← LinearMap.sum_apply, hsum]
    rfl
  have hS : ∀ i, trace (S i) = 0 := by
    intro i
    have hSi : S i = ⟨(T.val ∘ₗ e i) ∘ₗ e i, (S i).property.comp_right (e i)⟩ := by
      apply Subtype.ext
      change T.val ∘ₗ e i = (T.val ∘ₗ e i) ∘ₗ e i
      rw [LinearMap.comp_assoc, hidem]
    rw [hSi, ← trace_comp_of_hasNoetherianRange (T.val ∘ₗ e i)
      (T.property.comp_right (e i)) (e i)]
    have h0 : (⟨e i ∘ₗ (T.val ∘ₗ e i), ((T.property.comp_right (e i)).comp_left (e i))⟩ :
        finiteRankEnd V) = 0 := by
      apply Subtype.ext
      exact hT i
    rw [h0, map_zero]
  rw [hTS, map_sum]
  exact Finset.sum_eq_zero fun i _ => hS i

/-- A resolution of the identity gives the finite-rank trace as a sum of traces
on the corresponding source spaces. -/
theorem trace_eq_sum_of_resolution {ι : Type uι} [Fintype ι]
    {W : ι → Type uV} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (j : ∀ i, W i →ₗ[ℂ] V) (q : ∀ i, V →ₗ[ℂ] W i)
    (hsum : ∑ i, j i ∘ₗ q i = LinearMap.id) (T : finiteRankEnd V) :
    trace T = ∑ i, trace (⟨(q i ∘ₗ T.val) ∘ₗ j i,
      (T.property.comp_left (q i)).comp_right (j i)⟩ : finiteRankEnd (W i)) := by
  let S (i : ι) : finiteRankEnd V :=
    ⟨j i ∘ₗ (q i ∘ₗ T.val), (T.property.comp_left (q i)).comp_left (j i)⟩
  have hT : T = ∑ i, S i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    ext v
    change T.val v = (∑ i, (S i).val) v
    rw [LinearMap.sum_apply]
    exact (LinearMap.congr_fun hsum (T.val v)).symm.trans (LinearMap.sum_apply _ _ _)
  calc
    trace T = ∑ i, trace (S i) := by rw [hT, map_sum]
    _ = _ := Finset.sum_congr rfl fun i _ =>
      trace_comp_of_hasNoetherianRange (q i ∘ₗ T.val) (T.property.comp_left (q i)) (j i)

end FiniteRankEnd

namespace BaseChange

open MeasureTheory HarmonicAnalysis

universe uG uA uB uC

section Exactness

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {A : Type uA} [AddCommGroup A] [Module ℂ A]
  {B : Type uB} [AddCommGroup B] [Module ℂ B]
  {C : Type uC} [AddCommGroup C] [Module ℂ C]

/-- Twisted distributions are additive on short exact sequences. Let
`0 → A → B → C → 0` be an exact sequence of admissible representations with
equivariant maps `f` and `g`, and let `TA`, `TB`, `TC` be endomorphisms of the three
carriers with `TB ∘ f = f ∘ TA` and `g ∘ TB = TC ∘ g`. Then the twisted distribution of
`(B, TB)` is the sum of those of `(A, TA)` and `(C, TC)`. The endomorphisms need not
intertwine the representations with any twist, and the sequence need not split
equivariantly. -/
theorem twistedDistribution_shortExact
    {ρA : Representation ℂ G A} {ρB : Representation ℂ G B} {ρC : Representation ℂ G C}
    (hA : IsAdmissible ρA) (hB : IsAdmissible ρB) (hC : IsAdmissible ρC)
    (f : ρA.IntertwiningMap ρB) (g : ρB.IntertwiningMap ρC)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    (TA : Module.End ℂ A) (TB : Module.End ℂ B) (TC : Module.End ℂ C)
    (hfT : TB ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ TA)
    (hgT : g.toLinearMap ∘ₗ TB = TC ∘ₗ g.toLinearMap) :
    twistedDistribution μ ρB hB TB =
      twistedDistribution μ ρA hA TA + twistedDistribution μ ρC hC TC := by
  ext φ
  rw [LinearMap.add_apply, twistedDistribution_apply, twistedDistribution_apply,
    twistedDistribution_apply]
  apply FiniteRankEnd.trace_shortExact f.toLinearMap g.toLinearMap hf hg hfg
  · ext a
    change Hecke.integratedAction μ ρB hB.1 φ (TB (f a)) =
      f (Hecke.integratedAction μ ρA hA.1 φ (TA a))
    rw [Hecke.integratedAction_intertwiner μ hA.1 hB.1 f φ (TA a)]
    congr 1
    exact LinearMap.congr_fun hfT a
  · ext b
    change g (Hecke.integratedAction μ ρB hB.1 φ (TB b)) =
      Hecke.integratedAction μ ρC hC.1 φ (TC (g b))
    rw [Hecke.integratedAction_intertwiner μ hB.1 hC.1 g φ (TB b)]
    congr 1
    exact LinearMap.congr_fun hgT b

end Exactness

section OffDiagonal

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A twisted distribution vanishes when the twisting endomorphism has zero diagonal
blocks for a finite family of equivariant idempotents with sum `1`. For example, if the
carrier is a direct sum of `s ≥ 2` subrepresentations and the endomorphism maps each
summand into the next one cyclically, the twisted distribution is `0`. -/
theorem twistedDistribution_eq_zero_of_offDiagonal {ι : Type uι} [Fintype ι]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (e : ι → Module.End ℂ V)
    (hsum : ∑ i, e i = 1) (hidem : ∀ i, e i ∘ₗ e i = e i)
    (hcomm : ∀ i g, e i ∘ₗ ρ g = ρ g ∘ₗ e i)
    (T : Module.End ℂ V) (hT : ∀ i, e i ∘ₗ T ∘ₗ e i = 0) :
    twistedDistribution μ ρ hρ T = 0 := by
  ext φ
  rw [twistedDistribution_apply, LinearMap.zero_apply]
  apply FiniteRankEnd.trace_eq_zero_of_offDiagonal e hsum hidem
  intro i
  let ei : ρ.IntertwiningMap ρ := ⟨e i, hcomm i⟩
  ext v
  change e i (Hecke.integratedAction μ ρ hρ.1 φ (T (e i v))) = 0
  rw [show e i (Hecke.integratedAction μ ρ hρ.1 φ (T (e i v))) =
      ei (Hecke.integratedAction μ ρ hρ.1 φ (T (e i v))) from rfl,
    Hecke.integratedAction_intertwiner μ hρ.1 hρ.1 ei φ]
  change Hecke.integratedAction μ ρ hρ.1 φ ((e i ∘ₗ T ∘ₗ e i) v) = 0
  rw [hT i, LinearMap.zero_apply, map_zero]

end OffDiagonal

section Diagonal

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Resolve a distribution into diagonal traces using equivariant inclusions and projections.
The endomorphism whose trace is taken can mix the summands. -/
theorem twistedDistribution_eq_sum_diagonal {ι : Type uι} [Fintype ι]
    {W : ι → Type uV} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (π : ∀ i, Representation ℂ G (W i)) (hπ : ∀ i, IsAdmissible (π i))
    (j : ∀ i, (π i).IntertwiningMap ρ) (q : ∀ i, ρ.IntertwiningMap (π i))
    (hsum : ∑ i, (j i).toLinearMap ∘ₗ (q i).toLinearMap = LinearMap.id)
    (T : Module.End ℂ V) :
    twistedDistribution μ ρ hρ T =
      ∑ i, twistedDistribution μ (π i) (hπ i)
        ((q i).toLinearMap ∘ₗ T ∘ₗ (j i).toLinearMap) := by
  ext f
  rw [LinearMap.sum_apply]
  simp_rw [twistedDistribution_apply]
  rw [FiniteRankEnd.trace_eq_sum_of_resolution (fun i => (j i).toLinearMap)
    (fun i => (q i).toLinearMap) hsum]
  refine Finset.sum_congr rfl fun i _ => congrArg FiniteRankEnd.trace (Subtype.ext ?_)
  ext v
  exact Hecke.integratedAction_intertwiner μ hρ.1 (hπ i).1 (q i) f (T (j i v))

end Diagonal

end BaseChange

end Langlands
