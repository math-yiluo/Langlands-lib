import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm

/-!
# Transfer and the intermediate-field inclusion of relative Weil groups

For a tower `F ⊆ K ⊆ E` of number fields with `E / F` Galois, the transfer
`W_{E/F} → C_F` restricted along the inclusion `W_{E/K} → W_{E/F}` is the transfer
`W_{E/K} → C_K` followed by the idele-class norm `C_K → C_F`. Compare Tate (1979),
(1.2.2), and Artin–Tate, Chapter XV. Proposition definitions only.
-/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open scoped NumberField
open Langlands.Global.AdelicFunctoriality

namespace RelativeWeilGroup

attribute [local instance] relativeGaloisTopology

/-- For the tower `F ⊆ K ⊆ E` and the restriction compatibility `h`, the transfer of
the image of `t ∈ W_{E/K}` in `W_{E/F}` is the idele-class norm of the transfer of
`t` to `C_K`. -/
def TransferNormCompatibility (c : FundamentalClass.ClassFamily.{u}) (F K E : Type u)
    [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] [IsGalois F E]
    (h : FundamentalClass.Restriction c) : Prop :=
  haveI : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  ∀ t : RelativeWeilGroup c K E,
    transfer c F E (restrictionInclusion c F E K h t) =
      ideleClassNorm (K := F) (L := K) (transfer c K E t)

/-- Tate (1979), (1.2.2), for relative Weil groups: for every class family with the
restriction compatibility and every tower `F ⊆ K ⊆ E` of number fields with `E / F`
Galois, transfer commutes with the intermediate-field inclusion and the idele-class
norm. -/
def TransferNormCompatibilityStatement : Prop :=
  ∀ (c : FundamentalClass.ClassFamily.{u}) (F K E : Type u)
    [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] [IsGalois F E]
    (h : FundamentalClass.Restriction c),
    TransferNormCompatibility c F K E h

end RelativeWeilGroup

end Langlands.ClassField.Global
