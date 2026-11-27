import Langlands.Representation.Plancherel.NestedStandardIntertwiningIntegral
import Langlands.Representation.Aubert.CorrectedOrbitCutIntegrals
import Langlands.Representation.Aubert.General.GroupTransport

/-! # Transport of standard integration between isomorphic ambient groups -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
set_option hygiene false

open MeasureTheory CategoryTheory
open Langlands.Aubert.General Langlands.Induction Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis Langlands.HarmonicAnalysis.SmoothWeakIntegral

namespace Langlands.Plancherel.StandardIntertwining

universe u uV

variable {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  (e : H ≃ₜ* G) {U V : Subgroup G} {U' V' : Subgroup H}
  (hU : ∀ x : H, x ∈ U' ↔ e x ∈ U) (hV : ∀ x : H, x ∈ V' ↔ e x ∈ V)

local notation "eV" => GroupTransport.subgroupEquiv e hV

/-- The quotient of the target radical carries the same source intersection
under an ambient group isomorphism. -/
def ambientEquivQuotient : QuotientSpace (U := U') V' ≃ₜ QuotientSpace (U := U) V :=
  leftQuotientHomeomorph eV (U'.subgroupOf V') (U.subgroupOf V)
    (fun x => (hU x.val).symm)

@[simp]
theorem ambientEquivQuotient_mk (v : V') :
    ambientEquivQuotient e hU hV (Quotient.mk _ v) = Quotient.mk _ (eV v) := rfl

@[simp]
theorem ambientEquivQuotient_symm_mk (v : V) :
    (ambientEquivQuotient e hU hV).symm (Quotient.mk _ v) =
      Quotient.mk _ ((eV).symm v) := by
  apply (ambientEquivQuotient e hU hV).injective
  rw [Homeomorph.apply_symm_apply, ambientEquivQuotient_mk,
    ContinuousMulEquiv.apply_symm_apply]

variable [MeasurableSpace (QuotientSpace (U := U) V)] [BorelSpace (QuotientSpace (U := U) V)]
  [MeasurableSpace (QuotientSpace (U := U') V')] [BorelSpace (QuotientSpace (U := U') V')]

local notation "Qe" => ambientEquivQuotient e hU hV
local notation "qG" => QuotientSpace (U := U) V
local notation "qH" => QuotientSpace (U := U') V'

/-- Transporting the given quotient measure also transports its right
invariance. -/
theorem ambientEquivQuotient_map_right_invariant
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (nu : Measure qH)
    (hnu : ∀ g : V', MeasurePreserving (rightTranslate (U'.subgroupOf V') g) nu nu)
    (g : V) :
    MeasurePreserving (rightTranslate (U.subgroupOf V) g) (nu.map Qe) (nu.map Qe) := by
  let g' := (eV).symm g
  let L := rightTranslate (U.subgroupOf V) g
  let R := rightTranslate (U'.subgroupOf V') g'
  have hcomm : L ∘ Qe = Qe ∘ R := by
    funext q
    induction q using Quotient.inductionOn with
    | h v =>
      change L (Qe (Quotient.mk _ v)) = Qe (R (Quotient.mk _ v))
      simp only [L, R, rightTranslate_mk, ambientEquivQuotient_mk, map_mul, g',
        ContinuousMulEquiv.apply_symm_apply]
  refine ⟨L.continuous.measurable, ?_⟩
  rw [Measure.map_map L.continuous.measurable (Qe).continuous.measurable, hcomm,
    ← Measure.map_map (Qe).continuous.measurable R.continuous.measurable, (hnu g').map_eq]

variable [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {P M : Subgroup G} {P' M' : Subgroup H}
  (d : IsSemidirectDecomposition P M U) (d' : IsSemidirectDecomposition P' M' U')
  (hc : IsClosed (U : Set G)) (hc' : IsClosed (U' : Set H))
  (eM : M' ≃ₜ* M) (A : SmoothRep.{0, u, uV} ℂ M)
  (nu : Measure qG) (nu' : Measure qH) (hnu : MeasurePreserving Qe nu' nu)

local notation "A'" => SmoothRep.pullback eM A
local notation "I" => (DynamicNormalization.leviTwistedInductionFunctor d hc).obj A
local notation "I'" => (DynamicNormalization.leviTwistedInductionFunctor d' hc').obj A'

include hnu in
/-- Weak standard integration commutes with precomposition by an isomorphism
of the ambient groups and the pullback on the inducing carrier. -/
theorem hasIntegral_ambientEquiv_iff (f : I) (f' : I')
    (hf : ∀ x : H, eval _ _ f' x = eval _ _ f (e x)) (J : G → A) :
    HasIntegral d' hc' V' A' nu' f' (J ∘ e) ↔ HasIntegral d hc V A nu f J := by
  have hx (x : H) :
      SmoothWeakIntegral.HasIntegral (A').representation nu'
        (integrand d' hc' V' A' x f') (J (e x)) ↔
      SmoothWeakIntegral.HasIntegral A.representation nu
        (integrand d hc V A (e x) f) (J (e x)) := by
    change SmoothWeakIntegral.HasIntegral (A.representation.comp eM.toMonoidHom) nu'
      (integrand d' hc' V' A' x f') (J (e x)) ↔ _
    refine (hasIntegral_comp_continuousMulEquiv_iff A.representation eM nu'
      (integrand d' hc' V' A' x f') (J (e x))).trans ?_
    have he : integrand d' hc' V' A' x f' = (integrand d hc V A (e x) f) ∘ Qe := by
      funext q
      induction q using Quotient.inductionOn with
      | h v =>
        simp only [Function.comp_apply, ambientEquivQuotient_mk, integrand_mk]
        exact (hf ((v : H) * x)).trans
          (congrArg (eval P (leviInflatedInducingRepresentation d hc A) f) (map_mul e (v : H) x))
    rw [he]
    exact (hasIntegral_measurePreserving_equiv_iff (Qe).toMeasurableEquiv hnu
      (integrand d hc V A (e x) f) (J (e x))).symm
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact (hx y).mp (h y)
  · intro h x
    exact (hx x).mpr (h (e x))

include hnu in
/-- Full convergence transfers between the two actual induction carriers. -/
theorem domain_eq_top_ambientEquiv_iff (E : I ≃ₗ[ℂ] I')
    (hE : ∀ f x, eval _ _ (E f) x = eval _ _ f (e x)) :
    domain d' hc' V' A' nu' = ⊤ ↔ domain d hc V A nu = ⊤ := by
  have h f J := hasIntegral_ambientEquiv_iff e hU hV d d' hc hc' eM A nu nu' hnu f (E f) (hE f) J
  constructor
  · intro ht
    apply eq_top_iff.mpr
    intro f _
    obtain ⟨J', hJ'⟩ := (mem_domain d' hc' V' A' nu' (E f)).1 (by rw [ht]; trivial)
    apply (mem_domain d hc V A nu f).2
    refine ⟨J' ∘ e.symm, (h f (J' ∘ e.symm)).mp ?_⟩
    have hcomp : (J' ∘ e.symm) ∘ e = J' := funext fun x => congrArg J' (e.symm_apply_apply x)
    exact (congrArg (HasIntegral d' hc' V' A' nu' (E f)) hcomp).mpr hJ'
  · intro ht
    apply eq_top_iff.mpr
    intro f' _
    obtain ⟨f, rfl⟩ := E.surjective f'
    obtain ⟨J, hJ⟩ := (mem_domain d hc V A nu f).1 (by rw [ht]; trivial)
    exact (mem_domain d' hc' V' A' nu' (E f)).2 ⟨J ∘ e, (h f J).mpr hJ⟩

end Langlands.Plancherel.StandardIntertwining
