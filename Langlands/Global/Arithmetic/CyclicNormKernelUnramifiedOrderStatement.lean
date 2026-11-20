import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterStatement

/-! # The local order of a cyclic norm-kernel character -/

noncomputable section

open scoped NumberField

universe uF uE

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open AdelicFunctoriality

/-- Outside finitely many finite places, the local uniformizer value of a cyclic
norm-kernel character has order equal to the residue degree at each place above. -/
def CyclicNormKernelUnramifiedOrderStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
      ∀ᶠ v : FinitePlace F in Filter.cofinite,
        η.IsUnramifiedAt v ∧ ∀ w : FinitePlacesAbove E v,
          w.1.asIdeal.ramificationIdx (𝓞 F) = 1 ∧
          orderOf (η.finiteUniformizerValue v) = w.1.asIdeal.inertiaDeg (𝓞 F)

end Langlands.Global.HeckeCharacter
