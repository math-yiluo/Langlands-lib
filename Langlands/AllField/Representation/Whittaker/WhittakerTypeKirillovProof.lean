import Langlands.Representation.Whittaker.WhittakerTypeKirillovProof
import Langlands.AllField.Representation.Whittaker.KirillovStatement
import Langlands.AllField.Representation.Whittaker.MirabolicMinimalityProof
/-!
# Whittaker-type Kirillov surjectivity on the actual mirabolic group

Deduce the exact JPSS inclusion from compact minimality for the actual smooth
mirabolic induction, using the coefficient and support adapters, for the topology
of the supplied data `T`.
-/

noncomputable section

namespace Langlands.AllField

open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement mirabolicCompactMinimality
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped BigOperators

universe uF uV

/-- Every compactly supported modulo unipotent, smooth covariant function on
actual mirabolic matrices is the restriction of a Whittaker coefficient. -/
theorem whittakerTypeKirillov : WhittakerTypeKirillovStatement.{uF, uV} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro n V _ _ ρ ψ hc hne hu hρ _hfinite
  dsimp only
  intro ℓ hℓ hcov _hmult φ hφ
  let Ψ := UnitaryAdditiveCharacter.ofComplex ψ hc hne hu
  have hL : ℓ ∈ glFunctionals Ψ n ρ := by
    apply (mem_glFunctionals_iff_entrywise Ψ ρ ℓ).mpr
    intro g hlow hdiag v
    exact hcov g ⟨hlow, hdiag⟩ v
  let L : glFunctionals Ψ n ρ := ⟨ℓ, hL⟩
  obtain ⟨hφcov, ⟨K, hK⟩, ⟨C, hC, hsupp⟩⟩ := hφ
  have hφcov' : ∀ (u : upperUnipotent (n + 1) F)
      (q : mirabolic n F),
      φ (u.val * q.val) = (standardCharacter Ψ n u : ℂ) * φ q.val := by
    intro u q
    rw [standardCharacter_eq_product]
    exact hφcov u.val q.val
      ⟨fun _ _ hij => u.property.1 hij, u.property.2⟩ q.property
  have hK' : ∀ (q k : mirabolic n F),
      k.val ∈ K → φ (q.val * k.val) = φ q.val := by
    intro q k hk
    exact hK q.val k.val q.property k.property hk
  have hsupp' : ∀ q : mirabolic n F, φ q.val ≠ 0 →
      ∃ (u : upperUnipotent (n + 1) F)
        (c : Langlands.GeneralLinear (n + 1) F),
        c ∈ C ∧ q.val = u.val * c := by
    intro q hq
    obtain ⟨u, c, hu, hc, he⟩ := hsupp q.val q.property hq
    exact ⟨⟨u, ⟨fun _ _ hij => hu.1 _ _ hij, hu.2⟩⟩, c, hc, he⟩
  let f := mirabolicCompactRestriction Ψ n φ hφcov' K hK' C hC hsupp'
  have hW : mirabolicCompactSubrepresentation Ψ n ≤
      mirabolicCoefficientImage Ψ ρ hρ.1 L :=
    mirabolicCompactMinimality F T n Ψ _
      (mirabolicCoefficientImage_ne_bot Ψ ρ hρ.1 L hℓ)
  obtain ⟨v, hv⟩ := hW f.property
  refine ⟨v, ?_⟩
  intro q hq
  have he := congrArg
    (fun g => mirabolicEval Ψ n g ⟨q, hq⟩) hv
  exact he

end Langlands.AllField
