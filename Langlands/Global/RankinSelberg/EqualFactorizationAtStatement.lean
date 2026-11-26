import Langlands.Global.RankinSelberg.EqualArchimedeanFactorizationReduction

/-! # Equal-rank partial Whittaker factorization at one number field

The totally complex closures of the equal-rank integrated and pointwise factorization
at a given field, and the implication from pointwise to integrated factorization at that field.
-/

universe u uQ
open NumberField
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Integrated equal-rank factorization over totally complex fields. -/
def EqualArchimedeanFactorizationTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    EqualArchimedeanFactorizationAt.{u, uQ} F

/-- Pointwise equal-rank factorization over totally complex fields. -/
def EqualPointwiseFactorizationTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    EqualPointwiseFactorizationAt.{u, uQ} F

/-- Same-field integration target for equal ranks. The shared quotient-product
measure formula is available separately in the Library. -/
def EqualArchimedeanFactorizationAtReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    EqualPointwiseFactorizationAt.{u, uQ} F → EqualArchimedeanFactorizationAt.{u, uQ} F

end Langlands.Global.RankinSelbergGlobal
