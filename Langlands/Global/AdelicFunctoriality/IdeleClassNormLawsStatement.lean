import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.AdelicFunctoriality.Inclusion

/-! # Tower and inclusion laws for the actual idele-class norm -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField
open scoped NumberField

universe u v w

/-- The actual idele-class norm is transitive in a compatible tower of number fields. -/
def IdeleClassNormTower : Prop :=
  ∀ (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M],
    ∀ x : IdeleClassGroup (𝓞 M) M,
      ideleClassNorm (K := K) (L := M) x =
        ideleClassNorm (K := K) (L := L) (ideleClassNorm (K := L) (L := M) x)

/-- Norm after extension of scalars on lower-field idele classes is the degree power. -/
def IdeleClassNormInclusionPower : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L],
    ∀ x : IdeleClassGroup (𝓞 K) K,
      ideleClassNorm (K := K) (L := L) (ideleClassInclusion (K := K) (L := L) x) =
        x ^ Module.finrank K L

/-- The tower and norm-of-inclusion laws, with separately reusable components. -/
def IdeleClassNormLaws : Prop :=
  IdeleClassNormTower.{u, v, w} ∧ IdeleClassNormInclusionPower.{u, v}

end Langlands.Global.AdelicFunctoriality
