import Langlands.Automorphic.Unramified.CyclicTransferStatement

/-! # Hecke characters with norm kernel for cyclic extensions

For a finite Galois extension `E/F` of number fields, global reciprocity identifies
`C_F / N_{E/F} C_E` with `Gal(E/F)^ab` (Neukirch, VI (5.5), p. 391).
For cyclic `Gal(E/F)`, a faithful character of this finite cyclic quotient pulls back
to the character `η` used by Arthur--Clozel, III §4, p. 202.
This module states its existence, its order, and the description of all Hecke
characters trivial on norms as its powers.
-/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

/-- Every cyclic Galois extension `E/F` of number fields has a Hecke character
with kernel exactly the idele-class norm image. Every such character has order
`[E : F]`, and its powers with exponents below `[E : F]` are exactly the Hecke
characters of `F` trivial on norms from `E`. -/
def CyclicNormKernelCharacterStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    (∃ η : HeckeCharacter F, η.HasNormKernel E) ∧
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
      orderOf η = Module.finrank F E ∧
      ∀ χ : HeckeCharacter F,
        χ.IsTrivialOnNorm E ↔ ∃ i < Module.finrank F E, χ = η ^ i

end Langlands.Global.HeckeCharacter
