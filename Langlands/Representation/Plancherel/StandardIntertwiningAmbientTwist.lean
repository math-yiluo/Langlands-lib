import Langlands.Representation.Plancherel.StandardIntertwiningTargetLaws
import Langlands.Representation.Aubert.General.CharacterTwistEquivalences
import Langlands.Representation.Twist.SmoothPartDefinitions

/-! # Ambient character transport of the actual standard integral -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

universe uX uG uV

variable {X : Type uX} [MeasurableSpace X]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (μ : Measure X)
  (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
  {f : X → V} {v : V}

include hχ in
/-- An open-kernel scalar twist leaves the weak integral relation unchanged,
because it leaves the underlying smooth linear functionals unchanged. -/
theorem hasIntegral_twist_iff :
    HasIntegral (Langlands.twist χ ρ) μ f v ↔ HasIntegral ρ μ f v := by
  constructor
  · intro hf ℓ
    exact hf ((smoothContragredientTwistEquiv χ ρ hχ).symm ℓ)
  · intro hf ℓ
    exact hf (smoothContragredientTwistEquiv χ ρ hχ ℓ)

end Langlands.HarmonicAnalysis.SmoothWeakIntegral

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  (χ : Induction.SmoothCharacter ℂ G) (hχU : U ≤ χ.toMonoidHom.ker)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

set_option hygiene false in
local notation "Aχ" =>
  A.twist (subgroupSmoothCharacter χ M).toMonoidHom
    (subgroupSmoothCharacter χ M).isOpen_ker

include hχU

/-- Scalar character multiplication commutes with the actual Levi-inflated
positive half modulus, without requiring a full-parabolic modulus comparison. -/
theorem leviInflatedInducingRepresentation_characterTwist :
    Langlands.twist (χ.toMonoidHom.comp P.subtype)
        (leviInflatedInducingRepresentation h hU A) =
      leviInflatedInducingRepresentation h hU Aχ := by
  ext p v
  change (χ.toMonoidHom (p : G) : ℂ) •
      ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
        (h.projection p) : ℂ) • A.representation (h.projection p) v) =
    (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
      (h.projection p) : ℂ) •
      ((χ.toMonoidHom ((h.projection p : M) : G) : ℂ) •
        A.representation (h.projection p) v)
  rw [character_eq_projection h χ.toMonoidHom hχU p]
  exact smul_comm _ _ _

/-- Multiplication by the actual ambient character on Levi-normalized
induced functions. -/
def leviInductionCharacterTwistEquiv :
    (Langlands.twist χ.toMonoidHom
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation).Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj Aχ).representation :=
  (Induction.smoothInductionTwistEquiv P χ
    (leviInflatedInducingRepresentation h hU A)).trans
      (Induction.smoothInducedEquiv P (equivOfRepresentationEq
        (leviInflatedInducingRepresentation_characterTwist h hU χ hχU A)))

@[simp]
theorem leviInductionCharacterTwistEquiv_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (g : G) :
    eval P (leviInflatedInducingRepresentation h hU Aχ)
        (leviInductionCharacterTwistEquiv h hU χ hχU A f) g =
      (χ.toMonoidHom g : ℂ) •
        eval P (leviInflatedInducingRepresentation h hU A) f g := rfl

@[simp]
theorem leviInductionCharacterTwistEquiv_symm_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj Aχ) (g : G) :
    eval P (leviInflatedInducingRepresentation h hU A)
        ((leviInductionCharacterTwistEquiv h hU χ hχU A).symm f) g =
      ((χ.toMonoidHom g)⁻¹ : ℂˣ) •
        eval P (leviInflatedInducingRepresentation h hU Aχ) f g := rfl

variable (U' : Subgroup G) (hχU' : U' ≤ χ.toMonoidHom.ker)

include hχU'

/-- On the actual integration quotient the ambient character factors out at
the ambient evaluation point. -/
theorem integrand_characterTwist
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (g : G) :
    integrand h hU U' Aχ g (leviInductionCharacterTwistEquiv h hU χ hχU A f) =
      (χ.toMonoidHom g : ℂ) • integrand h hU U' A g f := by
  funext q
  induction q using Quotient.inductionOn with
  | h u' =>
    simp only [integrand_mk, Pi.smul_apply]
    rw [leviInductionCharacterTwistEquiv_eval h hU χ hχU A f]
    have hu : χ.toMonoidHom (u' : G) = 1 := hχU' u'.property
    rw [map_mul, hu, one_mul]

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- The original weak-integral specification is transported by character
multiplication at every ambient group argument. -/
theorem hasIntegral_characterTwist_iff
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (Jf : G → A) :
    HasIntegral h hU U' Aχ ν (leviInductionCharacterTwistEquiv h hU χ hχU A f)
        (fun g => (χ.toMonoidHom g : ℂ) • Jf g) ↔
      HasIntegral h hU U' A ν f Jf := by
  constructor
  · intro hf g
    have hg := (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_twist_iff
      A.representation ν (subgroupSmoothCharacter χ M).toMonoidHom
      (subgroupSmoothCharacter χ M).isOpen_ker).mp (hf g)
    rw [integrand_characterTwist h hU χ hχU A U' hχU'] at hg
    have hi := hg.smul ((χ.toMonoidHom g : ℂ)⁻¹)
    simpa only [smul_smul, Pi.smul_apply,
      inv_mul_cancel₀ (χ.toMonoidHom g).ne_zero, one_smul] using hi
  · intro hf g
    apply (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_twist_iff
      A.representation ν (subgroupSmoothCharacter χ M).toMonoidHom
      (subgroupSmoothCharacter χ M).isOpen_ker).mpr
    rw [integrand_characterTwist h hU χ hχU A U' hχU']
    exact (hf g).smul _

/-- Character multiplication identifies exactly the actual convergence and
original-carrier representability domains. -/
theorem mem_domain_characterTwist_iff
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    leviInductionCharacterTwistEquiv h hU χ hχU A f ∈ domain h hU U' Aχ ν ↔
      f ∈ domain h hU U' A ν := by
  rw [mem_domain, mem_domain]
  constructor
  · rintro ⟨Jf, hJf⟩
    refine ⟨fun g => ((χ.toMonoidHom g : ℂ)⁻¹) • Jf g, ?_⟩
    apply (hasIntegral_characterTwist_iff h hU χ hχU A U' hχU' ν f _).mp
    simpa only [smul_smul, mul_inv_cancel₀ (χ.toMonoidHom _).ne_zero, one_smul] using hJf
  · rintro ⟨Jf, hJf⟩
    exact ⟨_, (hasIntegral_characterTwist_iff h hU χ hχU A U' hχU' ν f Jf).mpr hJf⟩

/-- Ambient character twisting preserves full convergence of the actual
standard integral; no convergence assertion is assumed for the twist. -/
theorem domain_eq_top_characterTwist_iff :
    domain h hU U' Aχ ν = ⊤ ↔ domain h hU U' A ν = ⊤ := by
  constructor
  · intro hf
    apply top_unique
    intro f _
    apply (mem_domain_characterTwist_iff h hU χ hχU A U' hχU' ν f).mp
    rw [hf]
    exact Submodule.mem_top
  · intro hf
    apply top_unique
    intro f _
    obtain ⟨f, rfl⟩ := (leviInductionCharacterTwistEquiv h hU χ hχU A).surjective f
    apply (mem_domain_characterTwist_iff h hU χ hχU A U' hχU' ν f).mpr
    rw [hf]
    exact Submodule.mem_top

end Langlands.Plancherel.StandardIntertwining
