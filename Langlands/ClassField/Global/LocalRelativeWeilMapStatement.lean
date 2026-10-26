import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.ClassField.Global.FundamentalClassStatement

/-! # Existence and conjugacy of local Weil maps into relative Weil groups

Proposition definitions only. Conjugacy is stated for every class family; existence
is stated for the arithmetic fundamental classes. Neither is proved here.
-/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

/-- Two local-to-relative Weil maps for the same reciprocity candidate are conjugate
by an element of the idele class group `C_E` (Tate 1979, §1.5 and (1.6.1)). -/
def LocalRelativeWeilMapConjugacyStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (c : FundamentalClass.ClassFamily.{u})
    (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal]
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w))
    (ι ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
    RelativeWeilGroup.IsLocalRelativeWeilMap v w e ι →
    RelativeWeilGroup.IsLocalRelativeWeilMap v w e ι' →
    ∃ b : IdeleClassGroup (𝓞 E) E, ∀ g : Weil.Local.localWeilGroup (padicField v),
      ι' g = RelativeWeilGroup.inclusion c F E b * ι g *
        (RelativeWeilGroup.inclusion c F E b)⁻¹

/-- For local invariant families forming class formations with the arithmetic
normalization, and global classes that are the corresponding fundamental classes,
every geometrically normalized reciprocity candidate of `E_w` admits a
local-to-relative Weil map `W_{F_v} → W_{E/F}` (Tate 1979, (1.6.1)). -/
def LocalRelativeWeilMapExistenceStatement : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∀ c : FundamentalClass.ClassFamily.{u},
      FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
        FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c →
      ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
        [IsGalois F E] (v : Langlands.Global.FinitePlace F)
        (w : Langlands.Global.FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
        (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w)),
        LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
            (towerPadicField v w).canonicalTopologicalData e →
          ∃ ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E,
            RelativeWeilGroup.IsLocalRelativeWeilMap v w e ι

/-- Existence and `C_E`-conjugacy of local-to-relative Weil maps. -/
def LocalRelativeWeilMapStatement : Prop :=
  LocalRelativeWeilMapConjugacyStatement.{u} ∧ LocalRelativeWeilMapExistenceStatement.{u}

end Langlands.ClassField.Global
