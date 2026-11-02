import Langlands.Sheaf.Renard.LocallyConstantScalarPresheaf
import Mathlib.Basic.Complex.Basic

/-!
# Constants in the actual locally constant scalar section rings

Constants exist as unital ring homomorphisms on every open, including the empty
open. Injectivity requires a nonempty domain for a nontrivial coefficient ring.
-/

open CategoryTheory Opposite TopologicalSpace

universe u r

namespace Langlands.Sheaf.Renard.LocallyConstantScalar

variable {X : Type u} [TopologicalSpace X]

/-- Mathlib's actual unital constant-function homomorphism on an open set. -/
def constants (R : Type r) [Ring R] (U : Opens X) :
    R →+* LocallyConstant U R :=
  LocallyConstant.constRingHom

@[simp]
theorem constants_apply (R : Type r) [Ring R] (U : Opens X) (a : R) (x : U) :
    constants R U a x = a := rfl

/-- Evaluating at a point recovers the coefficient. -/
theorem eval_constants (R : Type r) [Ring R] (U : Opens X) (x : U) :
    (LocallyConstant.evalRingHom x).comp (constants R U) = RingHom.id R := by
  ext a
  rfl

/-- Pullback along every open inclusion preserves the actual constant sections. -/
@[simp]
theorem restrict_constants (R : Type r) [Ring R] {U V : Opens X} (h : U ≤ V) (a : R) :
    restrict R h (constants R V a) = constants R U a := by
  ext x
  rfl

/-- The homomorphisms used for restriction of scalars commute with restriction. -/
theorem restrict_comp_constants (R : Type r) [Ring R] {U V : Opens X} (h : U ≤ V) :
    (restrict R h).comp (constants R V) = constants R U := by
  ext a x
  rfl

/-- The compatibility equation for the actual all-open ring presheaf arrow. -/
@[simp]
theorem ringPresheaf_map_constants (R : Type r) [Ring R] {U V : Opens X}
    (h : U ≤ V) (a : R) :
    (ringPresheaf X R).map (homOfLE h).op (constants R V a) = constants R U a := by
  exact restrict_constants R h a

/-- The same equation on every chosen basis, with its actual inclusion arrows. -/
@[simp]
theorem basisRingPresheaf_map_constants (B : OpenBasis X) (R : Type r) [Ring R]
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (a : R) :
    (basisRingPresheaf B R).map (basisHom h).op (constants R V.obj a) =
      constants R U.obj a := by
  exact restrict_constants R h a

/-- Forgetting the rings retains compatibility with the literal basis restrictions. -/
@[simp]
theorem rawPresheaf_restriction_constants (B : OpenBasis X) (R : Type r) [Ring R]
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (a : R) :
    restriction (rawPresheaf B R) h (constants R V.obj a) = constants R U.obj a := by
  exact restrict_constants R h a

/-- Constants are injective on a nonempty open domain. -/
theorem constants_injective (R : Type r) [Ring R] (U : Opens X) [Nonempty U] :
    Function.Injective (constants R U) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  intro a b h
  exact congrArg (fun s : LocallyConstant U R => s x) h

/-- All constant functions coincide on the actual empty open. -/
theorem constants_empty_eq (R : Type r) [Ring R] (a b : R) :
    constants R (⊥ : Opens X) a = constants R (⊥ : Opens X) b := by
  ext x
  exact False.elim x.property

/-- In particular, the empty-domain zero and one functions are equal. -/
theorem empty_zero_eq_one (R : Type r) [Ring R] :
    (0 : LocallyConstant (⊥ : Opens X) R) = 1 := by
  ext x
  exact False.elim x.property

/-- Nontrivial coefficients cannot inject into the section ring on the empty open. -/
theorem constants_empty_not_injective (R : Type r) [Ring R] [Nontrivial R] :
    ¬ Function.Injective (constants R (⊥ : Opens X)) := by
  intro h
  exact zero_ne_one (h (constants_empty_eq R 0 1))

/-- For a nontrivial ring, nonemptiness is the exact condition for injectivity. -/
theorem constants_injective_iff (R : Type r) [Ring R] [Nontrivial R] (U : Opens X) :
    Function.Injective (constants R U) ↔ Nonempty U := by
  constructor
  · intro h
    by_contra hU
    have heq : constants R U 0 = constants R U 1 := by
      ext x
      exact (hU ⟨x⟩).elim
    exact zero_ne_one (h heq)
  · intro hU
    let := hU
    exact constants_injective R U

/-- The actual empty-open counterexample to the source's complex injectivity sentence. -/
theorem complex_constants_empty_not_injective :
    ¬ Function.Injective (constants ℂ (⊥ : Opens X)) :=
  constants_empty_not_injective ℂ

section Commutative

variable (R : Type r) [CommRing R]

/-- The existing pointwise algebra structure, without replacing the section carrier. -/
abbrev sectionAlgebra (U : Opens X) : Algebra R (LocallyConstant U R) :=
  inferInstance

/-- Its structure homomorphism is the actual constant homomorphism. -/
theorem constants_eq_algebraMap (U : Opens X) :
    constants R U = algebraMap R (LocallyConstant U R) := by
  ext a x
  rfl

@[simp]
theorem algebraMap_apply (U : Opens X) (a : R) (x : U) :
    algebraMap R (LocallyConstant U R) a x = a := rfl

/-- Scalar multiplication is pointwise multiplication by the coefficient. -/
theorem smul_apply (U : Opens X) (a : R) (s : LocallyConstant U R) (x : U) :
    (a • s) x = a * s x := rfl

/-- The action of a constant section agrees with the existing coefficient action. -/
theorem constants_mul_eq_smul (U : Opens X) (a : R) (s : LocallyConstant U R) :
    constants R U a * s = a • s := by
  ext x
  rfl

/-- Mathlib's actual pullback algebra homomorphism along the same open inclusion. -/
def restrictAlgebraHom {U V : Opens X} (h : U ≤ V) :
    LocallyConstant V R →ₐ[R] LocallyConstant U R :=
  LocallyConstant.comapₐ R (inclusion h)

@[simp]
theorem restrictAlgebraHom_toRingHom {U V : Opens X} (h : U ≤ V) :
    (restrictAlgebraHom R h).toRingHom = restrict R h := rfl

/-- Restriction preserves the existing pointwise scalar action. -/
@[simp]
theorem restrict_smul {U V : Opens X} (h : U ≤ V) (a : R) (s : LocallyConstant V R) :
    restrict R h (a • s) = a • restrict R h s := by
  ext x
  rfl

/-- Restriction commutes with the existing algebra maps even on empty domains. -/
@[simp]
theorem restrict_algebraMap {U V : Opens X} (h : U ≤ V) (a : R) :
    restrict R h (algebraMap R (LocallyConstant V R) a) =
      algebraMap R (LocallyConstant U R) a := by
  ext x
  rfl

end Commutative

/-- The source complex-valued section algebra, using the existing pointwise structure. -/
abbrev complexSectionAlgebra (U : Opens X) : Algebra ℂ (LocallyConstant U ℂ) :=
  sectionAlgebra ℂ U

/-- The source complex-valued restrictions are actual complex-algebra homomorphisms. -/
abbrev complexRestrictAlgebraHom {U V : Opens X} (h : U ≤ V) :
    LocallyConstant V ℂ →ₐ[ℂ] LocallyConstant U ℂ :=
  restrictAlgebraHom ℂ h

end Langlands.Sheaf.Renard.LocallyConstantScalar
