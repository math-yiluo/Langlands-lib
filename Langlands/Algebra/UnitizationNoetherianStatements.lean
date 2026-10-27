import Mathlib.Algebra.Algebra.Unitization
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Internal Noetherian unitization criteria

Derived statement targets for the actual scalar-projection kernel ideal.
These do not define a source convention for Noetherian nonunital algebras.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationNoetherian

universe uR uA

/-- The unitization is Noetherian exactly when its scalar ring and its
scalar-projection kernel ideal are Noetherian. -/
def KernelCriterionStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A],
    IsNoetherianRing (Unitization R A) ↔
      IsNoetherianRing R ∧
        IsNoetherian (Unitization R A) (RingHom.ker (Unitization.fstHom R A))

/-- Over a Noetherian scalar ring, Noetherianity is equivalent to that
of the actual scalar-projection kernel ideal. -/
def NoetherianScalarCriterionStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA)
    [CommRing R] [IsNoetherianRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A],
    IsNoetherianRing (Unitization R A) ↔
      IsNoetherian (Unitization R A) (RingHom.ker (Unitization.fstHom R A))

/-- The scalar-ring hypothesis is automatic over a field. -/
def FieldCriterionStatement : Prop :=
  ∀ (k : Type uR) (A : Type uA)
    [Field k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A],
    IsNoetherianRing (Unitization k A) ↔
      IsNoetherian (Unitization k A) (RingHom.ker (Unitization.fstHom k A))

/-- The general criterion and its two specializations, in that order. -/
def UnitizationNoetherianStatement : Prop :=
  KernelCriterionStatement.{uR, uA} ∧
    NoetherianScalarCriterionStatement.{uR, uA} ∧
    FieldCriterionStatement.{uR, uA}

end Langlands.Algebra.UnitizationNoetherian
