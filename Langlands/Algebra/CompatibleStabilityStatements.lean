import Langlands.Algebra.CompatibleSubmodule
import Langlands.LinearAlgebra.StableEndomorphismStatements

/-!
# Stability criteria for compatible nonunital algebra actions

Statement targets over the actual compatible submodules and linear intertwiners.
They specialize Renard 2026, C.II, Definition and Lemma (i)–(iii),
printed pp. 276–278 / PDF pp. 282–284.
-/

set_option autoImplicit false

namespace Langlands.Algebra.CompatibleStability

open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV uA uM uC

/-- The existing stability predicate agrees with equality of actual compatible kernels and
ranges of a self-intertwiner and its square. -/
def StableKernelRangeStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    Stable f.toLinearMap ↔
      f.ker = (f.comp f).ker ∧ f.range = (f.comp f).range

/-- Stability is equivalent to the compatible kernel and range being complementary. -/
def StableIffIsComplStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    Stable f.toLinearMap ↔ IsCompl f.ker f.range

/-- The right-exact stability criterion for actual compatible intertwiners. -/
def StableOfRightExactStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (A : Type uA) (M : Type uM) (C : Type uC)
    [AddCommGroup A] [Module ℂ A]
    [AddCommGroup M] [Module ℂ M]
    [AddCommGroup C] [Module ℂ C]
    (ρA : B →ₙₐ[ℂ] Module.End ℂ A)
    (ρM : B →ₙₐ[ℂ] Module.End ℂ M)
    (ρC : B →ₙₐ[ℂ] Module.End ℂ C)
    (phi : LinearIntertwiner ρA ρM) (psi : LinearIntertwiner ρM ρC)
    (fA : LinearIntertwiner ρA ρA)
    (fM : LinearIntertwiner ρM ρM)
    (fC : LinearIntertwiner ρC ρC),
    phi.range = psi.ker →
    Function.Surjective psi →
    fM.comp phi = phi.comp fA →
    fC.comp psi = psi.comp fM →
    Stable fA.toLinearMap → Stable fM.toLinearMap → Stable fC.toLinearMap

/-- The left-exact stability criterion for actual compatible intertwiners. -/
def StableOfLeftExactStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (A : Type uA) (M : Type uM) (C : Type uC)
    [AddCommGroup A] [Module ℂ A]
    [AddCommGroup M] [Module ℂ M]
    [AddCommGroup C] [Module ℂ C]
    (ρA : B →ₙₐ[ℂ] Module.End ℂ A)
    (ρM : B →ₙₐ[ℂ] Module.End ℂ M)
    (ρC : B →ₙₐ[ℂ] Module.End ℂ C)
    (phi : LinearIntertwiner ρA ρM) (psi : LinearIntertwiner ρM ρC)
    (fA : LinearIntertwiner ρA ρA)
    (fM : LinearIntertwiner ρM ρM)
    (fC : LinearIntertwiner ρC ρC),
    Function.Injective phi →
    phi.range = psi.ker →
    fM.comp phi = phi.comp fA →
    fC.comp psi = psi.comp fM →
    Stable fM.toLinearMap → Stable fC.toLinearMap → Stable fA.toLinearMap

/-- The closed family of compatible-action stability criteria. -/
def CompatibleStabilityStatements : Prop :=
  StableKernelRangeStatement.{uB, uV} ∧
    StableIffIsComplStatement.{uB, uV} ∧
    StableOfRightExactStatement.{uB, uA, uM, uC} ∧
    StableOfLeftExactStatement.{uB, uA, uM, uC}

end Langlands.Algebra.CompatibleStability
