import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.Automorphic.AssociatedFactorStatement

/-!
# Continuous characters of relative Weil groups and the transfer

At an arithmetic class family, every continuous character of `W_{E/F}` is a continuous
character of `C_F` composed with the transfer `W_{E/F} → C_F`; compare Tate (1979), (1.1),
where the reciprocity isomorphism `C_F ≅ W^{ab}` is an isomorphism of topological groups.
Proposition definitions only.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.ClassField.Global.RelativeWeilGroup

open scoped NumberField

attribute [local instance] relativeGaloisTopology

/-- Every continuous character `ξ` of `W_{E/F}`, with `Gal(E/F)` discrete, is `χ ∘ transfer`
for some continuous character `χ` of the idele class group `C_F`. -/
def TransferCharacterFactorization (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] :
    Prop :=
  ∀ ξ : RelativeWeilGroup c F E →ₜ* ℂˣ,
    ∃ χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ,
      ∀ t : RelativeWeilGroup c F E, ξ t = χ (transfer c F E t)

/-- Tate (1979), (1.1), for relative Weil groups at an arithmetic class family: for every
finite Galois extension `E / F` of number fields, every continuous character of `W_{E/F}`
factors through the transfer as a continuous character of `C_F`. -/
def TransferCharacterFactorizationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E],
    TransferCharacterFactorization c F E

end Langlands.ClassField.Global.RelativeWeilGroup
