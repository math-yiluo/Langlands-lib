import Langlands.Algebra.NonUnitalModuleCornerScalars
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Admissible original nonunital modules

Renard (9 July 2026), I.5.1, definition on printed p.26 / PDF32.
The finite-dimensional spaces use precisely the recovered complex scalars.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleAdmissible

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Every idempotent-fixed space is finite-dimensional for its canonical scalars. -/
def IsAdmissible : Prop :=
  ∀ e : Idempotent A,
    letI := NonUnitalModuleCorner.complexModule hA hM e
    FiniteDimensional ℂ (NonUnitalModuleCorner.FixedPart e M)

theorem isAdmissible_iff :
    IsAdmissible hA hM ↔
      ∀ e : Idempotent A,
        letI := NonUnitalModuleCorner.complexModule hA hM e
        FiniteDimensional ℂ (NonUnitalModuleCorner.FixedPart e M) := Iff.rfl

/-- The definition keeps the algebra and the module carrier in independent universes. -/
example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M → Prop :=
  @IsAdmissible.{uA, uM}

end Langlands.Algebra.NonUnitalModuleAdmissible
