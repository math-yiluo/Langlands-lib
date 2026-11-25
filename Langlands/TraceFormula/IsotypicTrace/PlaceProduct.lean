import Langlands.TraceFormula.IsotypicTrace.OccurrenceReduction
import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.LocalModularCharacterAdjointDeterminantStatement
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The adelic group as a product at one finite place

For an affine group scheme `G` over a number field `F` and a finite place `v`, the points
`awaySubgroup F G v` of `G(𝔸_F)` with trivial component at `v` form a closed normal subgroup
commuting with the image of `ofPlace`, and `(y, h) ↦ ofPlace y * h` is an isomorphism of
topological groups `G(F_v) × awaySubgroup F G v ≃ₜ* G(𝔸_F)` (`placeSplitting`). Given Haar
measures `μv` on `G(F_v)` and `ν` on `G(𝔸_F)`, a Haar measure `νH` on the away subgroup makes
`ν` the image of `μv × νH` (`exists_awayHaar`). For a split test function
`g ↦ fv (g_v) * fw g` with `fw` right invariant under `G(F_v)` and `fv ≠ 0`, the restriction of
`fw` to the away subgroup is integrable and the integrated action factors through the local
and away integrated actions (`integral_split_eq`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula.IsotypicTrace

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (v : Langlands.Global.FinitePlace F)

/-- The adelic points whose component at `v` is trivial. -/
def awaySubgroup : Subgroup (AdelicGroupPoints F G) :=
  (atPlace F G (.inr v)).toMonoidHom.ker

omit [IsAffine G.X.left] in
theorem mem_awaySubgroup {g : AdelicGroupPoints F G} :
    g ∈ awaySubgroup F G v ↔ atPlace F G (.inr v) g = 1 :=
  MonoidHom.mem_ker

theorem isClosed_awaySubgroup : IsClosed (awaySubgroup F G v : Set (AdelicGroupPoints F G)) :=
  isClosed_eq (atPlace F G (.inr v)).continuous continuous_const

/-- Points trivial at `v` commute with the local factor at `v`. -/
theorem ofPlace_mul_comm (y : PlaceGroupPoints F G (.inr v)) {h : AdelicGroupPoints F G}
    (hh : h ∈ awaySubgroup F G v) :
    ofPlace F G (.inr v) y * h = h * ofPlace F G (.inr v) y := by
  apply ext_atPlace F G
  intro i
  simp only [map_mul]
  by_cases hi : i = .inr v
  · subst hi
    rw [atPlace_ofPlace_same, (mem_awaySubgroup F G v).mp hh, mul_one, one_mul]
  · rw [atPlace_ofPlace_of_ne F G _ i hi, mul_one, one_mul]

theorem inv_ofPlace_atPlace_mul_mem (g : AdelicGroupPoints F G) :
    (ofPlace F G (.inr v) (atPlace F G (.inr v) g))⁻¹ * g ∈ awaySubgroup F G v := by
  rw [mem_awaySubgroup, map_mul, map_inv, atPlace_ofPlace_same, inv_mul_cancel]

/-- Every adelic point is a local point at `v` times a point trivial at `v`. -/
theorem exists_split (g : AdelicGroupPoints F G) :
    ∃ y c, g = ofPlace F G (.inr v) y * c ∧
      ∀ y', ofPlace F G (.inr v) y' * c = c * ofPlace F G (.inr v) y' :=
  ⟨atPlace F G (.inr v) g, _, (mul_inv_cancel_left _ g).symm,
    fun y' => ofPlace_mul_comm F G v y' (inv_ofPlace_atPlace_mul_mem F G v g)⟩

/-- `G(𝔸_F) = G(F_v) × G(𝔸_F^v)` as topological groups. -/
def placeSplitting :
    PlaceGroupPoints F G (.inr v) × awaySubgroup F G v ≃ₜ* AdelicGroupPoints F G where
  toFun p := ofPlace F G (.inr v) p.1 * p.2
  invFun g := (atPlace F G (.inr v) g,
    ⟨(ofPlace F G (.inr v) (atPlace F G (.inr v) g))⁻¹ * g, inv_ofPlace_atPlace_mul_mem F G v g⟩)
  left_inv p := by
    obtain ⟨y, h, hh⟩ := p
    have hy : atPlace F G (.inr v) (ofPlace F G (.inr v) y * h) = y := by
      rw [map_mul, atPlace_ofPlace_same, (mem_awaySubgroup F G v).mp hh, mul_one]
    ext1
    · exact hy
    · apply Subtype.ext
      change (ofPlace F G (.inr v) (atPlace F G (.inr v) (ofPlace F G (.inr v) y * h)))⁻¹ *
        (ofPlace F G (.inr v) y * h) = h
      rw [hy, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ g
  map_mul' p q := by
    change ofPlace F G (.inr v) (p.1 * q.1) * ((p.2 : AdelicGroupPoints F G) * q.2) =
      ofPlace F G (.inr v) p.1 * p.2 * (ofPlace F G (.inr v) q.1 * q.2)
    rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (p.2 : AdelicGroupPoints F G),
      ← ofPlace_mul_comm F G v q.1 p.2.2, mul_assoc]
  continuous_toFun :=
    ((continuous_ofPlace F G _).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    (atPlace F G (.inr v)).continuous.prodMk
      ((((continuous_ofPlace F G _).comp (atPlace F G (.inr v)).continuous).inv.mul
        continuous_id).subtype_mk _)

@[simp] theorem placeSplitting_apply (p : PlaceGroupPoints F G (.inr v) × awaySubgroup F G v) :
    placeSplitting F G v p = ofPlace F G (.inr v) p.1 * p.2 := rfl

instance awaySubgroup_locallyCompactSpace [LocallyOfFiniteType G.X.hom] :
    LocallyCompactSpace (awaySubgroup F G v) :=
  (isClosed_awaySubgroup F G v).locallyCompactSpace

section Measure

variable [LocallyOfFiniteType G.X.hom]
  [MeasurableSpace (PlaceGroupPoints F G (.inr v))] [BorelSpace (PlaceGroupPoints F G (.inr v))]

instance awaySubgroup_secondCountableTopology :
    SecondCountableTopology (awaySubgroup F G v) :=
  inferInstanceAs
    (SecondCountableTopology (awaySubgroup F G v : Set (AdelicGroupPoints F G)))

example : SigmaCompactSpace (awaySubgroup F G v) := inferInstance

/-- A Haar measure on the away subgroup normalized so that `ν` is the image of `μv × νH`. -/
theorem exists_awayHaar (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure] :
    ∃ νH : Measure (awaySubgroup F G v), νH.IsHaarMeasure ∧
      Measure.map (placeSplitting F G v) (μv.prod νH) = ν := by
  let D := placeSplitting F G v
  let μpull := Measure.map D.symm ν
  let μ₂₀ : Measure (awaySubgroup F G v) := Measure.haar
  let c := Measure.haarScalarFactor μpull (μv.prod μ₂₀)
  have hmul : μpull = c • (μv.prod μ₂₀) := Measure.isMulLeftInvariant_eq_smul μpull (μv.prod μ₂₀)
  have hc : c ≠ 0 := by
    intro hz
    exact (NeZero.ne μpull) (by simpa only [hz, zero_smul] using hmul)
  refine ⟨c • μ₂₀, Measure.IsHaarMeasure.nnreal_smul μ₂₀ hc, ?_⟩
  rw [Measure.prod_smul_right, ← hmul]
  exact MeasurableEquiv.map_map_symm D.toHomeomorph.toMeasurableEquiv

/-- **Factorization of the integrated action at `v`.** -/
theorem integral_split_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (π : AdelicGroupPoints F G →* (E →L[ℂ] E))
    (hπnorm : ∀ a x, ‖π a x‖ = ‖x‖) (hπcont : ∀ x, Continuous fun a => π a x)
    (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (νH : Measure (awaySubgroup F G v)) [νH.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G))
    (hν : Measure.map (placeSplitting F G v) (μv.prod νH) = ν)
    (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v))) (fw : AdelicGroupPoints F G → ℂ)
    (hfw : ∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g)
    (hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν) (hfv : fv ≠ 0) :
    Integrable (fun h : awaySubgroup F G v => fw h) νH ∧
      ∀ x, ∫ g, (fv (atPlace F G (.inr v) g) * fw g) • π g x ∂ν =
        ∫ y, fv y • π (ofPlace F G (.inr v) y) (∫ h, fw h • π h x ∂νH) ∂μv := by
  subst hν
  let D := placeSplitting F G v
  let Dm := D.toHomeomorph.toMeasurableEquiv
  have hDm : ∀ p, Dm p = D p := fun p => rfl
  have hsplitf : ∀ p : PlaceGroupPoints F G (.inr v) × awaySubgroup F G v,
      fv (atPlace F G (.inr v) (D p)) * fw (D p) = fv p.1 * fw p.2 := by
    rintro ⟨y, h, hh⟩
    change fv (atPlace F G (.inr v) (ofPlace F G (.inr v) y * h)) *
      fw (ofPlace F G (.inr v) y * h) = fv y * fw h
    rw [map_mul, atPlace_ofPlace_same, (mem_awaySubgroup F G v).mp hh, mul_one,
      ofPlace_mul_comm F G v y hh, hfw]
  have hint : Integrable (fun p : PlaceGroupPoints F G (.inr v) × awaySubgroup F G v =>
      fv p.1 * fw p.2) (μv.prod νH) := by
    have h1 := (integrable_map_equiv Dm _).mp hf
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hDm]
    exact hsplitf p
  have hfwint : Integrable (fun h : awaySubgroup F G v => fw h) νH := by
    obtain ⟨y₀, hy₀⟩ : ∃ y, fv y ≠ 0 := by
      by_contra h
      push Not at h
      exact hfv (Subtype.ext (funext h))
    let U : Set (PlaceGroupPoints F G (.inr v)) := {y | fv y = fv y₀}
    have hU : IsOpen U := fv.locallyConstant.isOpen_fiber _
    have hUpos : μv U ≠ 0 := (hU.measure_pos μv ⟨y₀, rfl⟩).ne'
    obtain ⟨y, hyU, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hUpos
      (ae_restrict_of_ae hint.prod_right_ae)
    have hfvy : fv y ≠ 0 := by
      change fv y = fv y₀ at hyU
      rw [hyU]
      exact hy₀
    have := hy.const_mul (fv y)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hfvy] using this
  refine ⟨hfwint, fun x => ?_⟩
  have hmapDm : Measure.map (placeSplitting F G v) (μv.prod νH) =
      Measure.map Dm (μv.prod νH) := rfl
  rw [hmapDm, integral_map_equiv Dm]
  let πH : awaySubgroup F G v →* (E →L[ℂ] E) := π.comp (awaySubgroup F G v).subtype
  have hπHint : Integrable (fun h : awaySubgroup F G v => fw h • π h x) νH :=
    Langlands.Analysis.isometricActionIntegrand_integrable νH πH (fun h => hπnorm h)
      (fun x => ((hπcont x).comp continuous_subtype_val).aestronglyMeasurable)
      (fun h : awaySubgroup F G v => fw h) hfwint x
  let πD : (PlaceGroupPoints F G (.inr v) × awaySubgroup F G v) →* (E →L[ℂ] E) :=
    π.comp D.toMonoidHom
  have hvint : Integrable (fun p : PlaceGroupPoints F G (.inr v) × awaySubgroup F G v =>
      (fv p.1 * fw p.2) • π (D p) x) (μv.prod νH) :=
    Langlands.Analysis.isometricActionIntegrand_integrable (μv.prod νH) πD
      (fun p => hπnorm (D p))
      (fun x => ((hπcont x).comp D.continuous).aestronglyMeasurable) _ hint x
  have hcomp : (fun p => (fv (atPlace F G (.inr v) (Dm p)) * fw (Dm p)) • π (Dm p) x) =
      fun p : PlaceGroupPoints F G (.inr v) × awaySubgroup F G v =>
        (fv p.1 * fw p.2) • π (D p) x := by
    funext p
    rw [hDm, hsplitf]
  rw [hcomp, integral_prod _ hvint]
  congr 1
  funext y
  have hin : (fun h : awaySubgroup F G v => (fv (y, h).1 * fw (y, h).2) • π (D (y, h)) x) =
      fun h : awaySubgroup F G v => fv y • π (ofPlace F G (.inr v) y) (fw h • π h x) := by
    funext h
    change (fv y * fw h) • π (ofPlace F G (.inr v) y * h) x = _
    rw [map_mul]
    change (fv y * fw h) • π (ofPlace F G (.inr v) y) (π h x) = _
    rw [mul_smul, map_smul]
  rw [hin, integral_smul, ← (π (ofPlace F G (.inr v) y)).integral_comp_comm hπHint]

end Measure

end Langlands.TraceFormula.IsotypicTrace
