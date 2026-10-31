import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Langlands.Representation.Whittaker.MultiplicityOneProof

/-! # Whittaker uniqueness and model prerequisites: proof

The published bundled multiplicity theorem and the entrywise adapters prove
the unchanged three-clause prerequisites statement.
-/

noncomputable section

namespace Langlands

universe uF uV

/-- Scalar multiplicity one, character inversion on the same representation,
and injectivity of every nonzero Whittaker coefficient map. -/
theorem whittakerPrerequisites : WhittakerPrerequisitesStatement.{uF,uV} := by
  intro p hp F
  let := F.canonicalNormedField
  intro n V _ _ ρ ψ hc hne hu hAdm hIrr
  let Ψ := HarmonicAnalysis.UnitaryAdditiveCharacter.ofComplex ψ hc hne hu
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ₁ ℓ₂ h₁ h₂ hℓ₁
    let L₁ : Whittaker.glFunctionals Ψ n ρ :=
      ⟨ℓ₁, (Whittaker.mem_glFunctionals_iff_entrywise Ψ ρ ℓ₁).mpr h₁⟩
    let L₂ : Whittaker.glFunctionals Ψ n ρ :=
      ⟨ℓ₂, (Whittaker.mem_glFunctionals_iff_entrywise Ψ ρ ℓ₂).mpr h₂⟩
    obtain ⟨c, hc, huniq⟩ :=
      Whittaker.multiplicityOne p hp F n V Ψ ρ hAdm hIrr L₁ L₂ hℓ₁
    refine ⟨c, congrArg Subtype.val hc, ?_⟩
    intro c' hc'
    exact huniq c' (Subtype.ext hc')
  · exact Whittaker.raw_exists_inverse_iff ψ hc hne hu ρ
  · let : Representation.IsIrreducible ρ := hIrr
    intro ℓ hℓ hcov
    exact Whittaker.raw_coefficient_injective ψ hc hne hu ρ ℓ hℓ hcov

end Langlands
