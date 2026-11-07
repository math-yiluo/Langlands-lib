import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.ClassField.Global.RelativeWeilTransfer

/-!
# Transfer of local relative Weil maps and local reciprocity

For a local map `ι : W_{F_z} → W_{E/F}` at a finite place `z`, the composite of `ι`
with the transfer `W_{E/F} → C_F` is the inverse of geometric local reciprocity of
`F_z` followed by `F_zˣ → C_F`; compare Tate (1979), (1.6.1) with `E = F`, and
(W3). Proposition definitions only; nothing is proved.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField
open Langlands.Global.CompletionPadic

universe u

/-- The transfer to `C_F` of `ι g` is the inverse of the image in `C_F` of `g` under
every geometric local reciprocity map of `F_z`. -/
def HasLocalTransferReciprocity {c : FundamentalClass.ClassFamily.{u}} {F E : Type u}
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (z : Langlands.Global.FinitePlace F)
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E) : Prop :=
  ∀ ez : LocalFactor.RankOne.ReciprocityCandidate (padicField z),
    LocalClassField.GeometricWeilReciprocityRelation (padicField z)
        (padicField z).canonicalTopologicalData ez →
      ∀ g : Weil.Local.localWeilGroup (padicField z),
        transfer c F E (ι g) =
          (IdeleClassGroup.ofAdicCompletion (𝓞 F) F z
            (LocalFactor.RankOne.reciprocityUnits (padicField z) ez g))⁻¹

/-- Tate (1979), (1.6.1) with `E = F`, for relative Weil groups: for every class
family, every Galois extension `E / F` of number fields and every local map
`ι : W_{F_z} → W_{E/F}` for a place `w` of `E` above a finite place `z` of `F`, the
transfer of `ι` to `C_F` is inverse geometric local reciprocity at `z`. -/
def LocalTransferReciprocityStatement : Prop :=
  ∀ (c : FundamentalClass.ClassFamily.{u}) (F E : Type u) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
    [w.asIdeal.LiesOver z.asIdeal]
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap z w e ι → HasLocalTransferReciprocity z ι

end Langlands.ClassField.Global.RelativeWeilGroup
