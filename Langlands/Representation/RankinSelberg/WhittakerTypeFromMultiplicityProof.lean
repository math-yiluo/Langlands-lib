import Langlands.Representation.RankinSelberg.WhittakerTypeFromMultiplicityStatement
import Mathlib.RepresentationTheory.Irreducible

/-!
# Whittaker type from scalar multiplicity

An algebraic proof using simplicity of the group-algebra module and the scalar
map onto the full space of character-equivariant functionals.
-/

namespace Langlands.RankinSelberg

universe uF uV

/-- A nonzero spanning functional gives Whittaker type for an irreducible
admissible representation. -/
theorem whittakerTypeFromMultiplicity :
    WhittakerTypeFromMultiplicityStatement.{uF, uV} := by
  intro F _ _ n θ V _ _ π hπ hadm hfunctional
  obtain ⟨ℓ, hℓ, hspan⟩ := hfunctional
  let : IsSimpleModule
      (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F)) π.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule π).mp hπ
  have hℓ' : ℓ ≠ 0 := fun h => hℓ (congrArg Subtype.val h)
  refine ⟨hadm, inferInstance, ?_⟩
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ _ ℓ) ⟨?_, ?_⟩).symm⟩
  · exact smul_left_injective ℂ hℓ'
  · intro ℓ'
    obtain ⟨c, hc⟩ := hspan ℓ'
    exact ⟨c, hc.symm⟩

end Langlands.RankinSelberg
