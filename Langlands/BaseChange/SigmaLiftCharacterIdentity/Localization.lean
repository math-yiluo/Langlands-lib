import Langlands.BaseChange.OrbitalIntegral
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.Representation.Hecke.TestFunction

/-! # Localization of concordant test functions by an invariant parameter -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.HarmonicAnalysis Langlands.TraceFormula
open Langlands.JacquetLanglands Langlands.QuotientIntegration

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

namespace ConcordanceLocalization

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict a test function to a clopen subset by setting it to zero off the subset. -/
def cutoff {U : Set X} (hU : IsClopen U) (f : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨fun x => LocallyConstant.charFn ℂ hU x * f x,
    (LocallyConstant.charFn ℂ hU).isLocallyConstant.comp₂ f.locallyConstant (· * ·),
    f.hasCompactSupport.mul_left⟩

open scoped Classical in
lemma cutoff_apply {U : Set X} (hU : IsClopen U) (f : SchwartzBruhat X) (x : X) :
    cutoff hU f x = if x ∈ U then f x else 0 := by
  change U.indicator (fun _ => (1 : ℂ)) x * f x = _
  by_cases hx : x ∈ U <;> simp [hx]

lemma support_cutoff {U : Set X} (hU : IsClopen U) (f : SchwartzBruhat X) :
    Function.support (cutoff hU f) = Function.support f ∩ U := by
  classical
  ext x
  simp only [Function.mem_support, Set.mem_inter_iff, cutoff_apply]
  by_cases hx : x ∈ U <;> simp [hx]

lemma cutoff_characteristic {U K : Set X} (hU : IsClopen U) (hK : IsClopen K)
    (hcK : IsCompact K) :
    cutoff hU (Hecke.TestFunction.characteristic hK hcK) =
      Hecke.TestFunction.characteristic (hK.inter hU) (hcK.inter_right hU.1) := by
  classical
  apply Hecke.TestFunction.ext
  intro x
  rw [cutoff_apply]
  simp only [Hecke.TestFunction.characteristic_apply, Set.indicator_apply, Set.mem_inter_iff]
  by_cases hx : x ∈ U <;> simp [hx]

section Orbital

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [FunLike M G G] [MonoidHomClass M G G]
variable (θ : M) (q : G → Y) (hq : Continuous q)
variable {B : Set Y} (hB : IsClopen B)

open scoped Classical in
lemma orbital_cutoff (hinv : ∀ x g : G, q (x⁻¹ * g * θ x) = q g)
    (g : G) [MeasurableSpace (LeftQuotient (twistedCentralizer θ g))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ g))) (f : SchwartzBruhat G) :
    twistedOrbitalIntegral θ g ν (cutoff (hB.preimage hq) f) =
      if q g ∈ B then twistedOrbitalIntegral θ g ν f else 0 := by
  have h : twistedOrbitFunction θ g (cutoff (hB.preimage hq) f) =
      fun z => if q g ∈ B then twistedOrbitFunction θ g f z else 0 := by
    funext z
    refine Quotient.inductionOn z fun x => ?_
    rw [twistedOrbitFunction_mk, twistedOrbitFunction_mk, cutoff_apply]
    simp only [Set.mem_preimage, hinv]
  rw [twistedOrbitalIntegral, h]
  by_cases hg : q g ∈ B <;> simp [hg, twistedOrbitalIntegral]

end Orbital

section Concordance

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type*} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {n l : ℕ} {σ : E ≃ₐ[F] E}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
variable {μF : Measure (GeneralLinear n F)} {μE : Measure (GeneralLinear n E)}
variable {φ : SchwartzBruhat (GeneralLinear n E)} {f : SchwartzBruhat (GeneralLinear n F)}

/-- Cutting on a common invariant parameter preserves both clauses of concordance. -/
lemma concordant_cutoff (h : AreConcordant σ l μF μE φ f)
    {qE : GeneralLinear n E → Y} {qF : GeneralLinear n F → Y}
    (hqE : Continuous qE) (hqF : Continuous qF)
    (hE : ∀ x δ, qE (x⁻¹ * δ * entrywiseAut σ n x) = qE δ)
    (hF : ∀ x γ, qF (x⁻¹ * γ * x) = qF γ)
    (hassoc : ∀ δ γ, IsNormAssociated σ l δ γ → qE δ = qF γ)
    {B : Set Y} (hB : IsClopen B) :
    AreConcordant σ l μF μE (cutoff (hB.preimage hqE) φ) (cutoff (hB.preimage hqF) f) := by
  classical
  constructor
  · intro γ hreg hnorm μγ _ _ νγ hνγ
    have horb := orbital_cutoff (MonoidHom.id (GeneralLinear n F)) qF hqF hB hF γ νγ f
    change orbitalIntegral γ νγ (cutoff (hB.preimage hqF) f) =
      (if qF γ ∈ B then orbitalIntegral γ νγ f else 0) at horb
    change orbitalIntegral γ νγ (cutoff (hB.preimage hqF) f) = 0
    rw [horb, h.1 γ hreg hnorm μγ νγ hνγ, ite_self]
  · intro δ γ ha hreg μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have htorb := orbital_cutoff (entrywiseAut σ n) qE hqE hB hE δ νδ φ
    have horb := orbital_cutoff (MonoidHom.id (GeneralLinear n F)) qF hqF hB hF γ νγ f
    change sigmaOrbitalIntegral σ n δ νδ (cutoff (hB.preimage hqE) φ) =
      (if qE δ ∈ B then sigmaOrbitalIntegral σ n δ νδ φ else 0) at htorb
    change orbitalIntegral γ νγ (cutoff (hB.preimage hqF) f) =
      (if qF γ ∈ B then orbitalIntegral γ νγ f else 0) at horb
    change sigmaOrbitalIntegral σ n δ νδ (cutoff (hB.preimage hqE) φ) =
      orbitalIntegral γ νγ (cutoff (hB.preimage hqF) f)
    rw [htorb, horb, hassoc δ γ ha, h.2 δ γ ha hreg μδ μγ νδ νγ hνδ hνγ hμ]

end Concordance

/-- Remove the part of the compact test support outside an open set, using a clopen
neighborhood of a parameter whose fiber in the support lies in that open set. -/
lemma exists_cutoff_support [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    {q : X → Y} (hq : Continuous q) (f : SchwartzBruhat X) {U : Set X} (hU : IsOpen U)
    {y : Y} (hfiber : ∀ x ∈ Function.support f, q x = y → x ∈ U) :
    ∃ (B : Set Y) (hB : IsClopen B), y ∈ B ∧
      Function.support (cutoff (hB.preimage hq) f) ⊆ U := by
  have hcompact := ((Hecke.TestFunction.isCompact_support f).inter_right hU.isClosed_compl).image hq
  have hy : y ∈ (q '' (Function.support f ∩ Uᶜ))ᶜ := by
    rintro ⟨x, ⟨hxf, hxU⟩, hxy⟩
    exact hxU (hfiber x hxf hxy)
  obtain ⟨B, hB, hyB, hBsub⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
      (hcompact.isClosed.isOpen_compl.mem_nhds hy)
  refine ⟨B, hB, hyB, ?_⟩
  rw [support_cutoff]
  rintro x ⟨hxf, hxB⟩
  by_contra hxU
  exact hBsub hxB ⟨x, ⟨hxf, hxU⟩, rfl⟩

end ConcordanceLocalization

end Langlands.BaseChange
