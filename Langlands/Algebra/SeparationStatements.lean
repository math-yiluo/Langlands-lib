import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Renard B.III: the unital separation lemma through actual left-ideal quotients

Source: Renard, *Représentations des groupes réductifs p-adiques* (French edition
dated 9 July 2026), Appendix B.III "Lemme de séparation", printed page 273 / PDF
page 279. The lemma says: if `A` is a complex algebra of countable dimension and
`a ∈ A` is not nilpotent, then some simple left `A`-module `M` satisfies
`a · M ≠ 0`. The source proof first adjoins a unit; this module states only the
unital case contained in that proof, together with its intermediate steps.

* `NonnilpotentLeftResolventStatement`: the step "d'après le théorème d'Amitsur
  B.I et sa démonstration, il existe `λ ∈ ℂ×` tel que `a − λ1_A` soit non
  inversible à gauche". No left inverse is the exact product condition
  `∀ b, b * (a - algebraMap ℂ A z) ≠ 1`.
* `PrincipalLeftIdealProperStatement`: an internal ring-theoretic auxiliary. The
  actual principal left ideal `Submodule.span A {x}`, the image of `b ↦ b * x`,
  is proper exactly when `x` has no left inverse.
* `LeftShiftSimpleQuotientStatement`: the source's quotient argument. A shift
  with no left inverse lies in a maximal left ideal `I` whose quotient `A ⧸ I`
  is a simple left module on which `a` moves the class of `1`.
* `UnitalSeparationStatement`: the resulting unital separation lemma, with the
  simple module realized as `A ⧸ I`.

`Submodule A A` is a left ideal. No two-sided ideal and no quotient ring is used.
The ring `A : Type u` lies in an arbitrary universe and need not be commutative;
countable dimension is `Module.rank ℂ A ≤ Cardinal.aleph0`. None of these
propositions is proved or assumed here. The nonunital statement and its
unitization reductions remain separate obligations.
-/

universe u

namespace Langlands.Renard

/-- Renard B.III, first step of the proof in the unital case: in a unital complex
algebra of at most countable dimension, a nonnilpotent element `a` has a nonzero
scalar shift `a - λ1_A` with no left inverse. The source derives this from
Amitsur's theorem B.I and its proof. The conclusion is one-sided: no `b`
satisfies `b * (a - algebraMap ℂ A z) = 1`. -/
@[pp_with_univ]
def NonnilpotentLeftResolventStatement (A : Type u) [Ring A] [Algebra ℂ A] : Prop :=
  Module.rank ℂ A ≤ Cardinal.aleph0 →
    ∀ a : A, ¬ IsNilpotent a →
      ∃ z : ℂ, z ≠ 0 ∧ ∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1

/-- Internal auxiliary for Renard B.III: in a unital ring, the principal left
ideal `A x = Submodule.span A {x}`, which is the image of `b ↦ b * x`, is proper
exactly when `x` has no left inverse. The source uses the direction "the map
`b ↦ b(a − λ1_A)` is not surjective since `1_A` is not reached". -/
@[pp_with_univ]
def PrincipalLeftIdealProperStatement (A : Type u) [Ring A] : Prop :=
  ∀ x : A, (Submodule.span A ({x} : Set A) ≠ ⊤ ↔ ∀ b : A, b * x ≠ 1)

/-- Renard B.III, the quotient argument in the unital case: if `z ≠ 0` and
`a - λ1_A` (with `λ = z`) has no left inverse, then some maximal left ideal `I`
contains the principal left ideal `A (a - λ1_A)`, the left module `A ⧸ I` is
simple, and `a` does not annihilate the class of `1` in `A ⧸ I`. -/
@[pp_with_univ]
def LeftShiftSimpleQuotientStatement (A : Type u) [Ring A] [Algebra ℂ A] : Prop :=
  ∀ (a : A) (z : ℂ), z ≠ 0 →
    (∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1) →
    ∃ I : Submodule A A,
      IsCoatom I ∧ Submodule.span A {a - algebraMap ℂ A z} ≤ I ∧
        IsSimpleModule A (A ⧸ I) ∧ a • I.mkQ 1 ≠ 0

/-- Renard B.III, Lemme, in the unital case: in a unital complex algebra of at
most countable dimension, every nonnilpotent element `a` acts nontrivially on a
simple left module. The module is the quotient `A ⧸ I` by a maximal left ideal
`I`, and `a` does not annihilate the class of `1`. -/
@[pp_with_univ]
def UnitalSeparationStatement (A : Type u) [Ring A] [Algebra ℂ A] : Prop :=
  Module.rank ℂ A ≤ Cardinal.aleph0 →
    ∀ a : A, ¬ IsNilpotent a →
      ∃ I : Submodule A A, IsCoatom I ∧
        IsSimpleModule A (A ⧸ I) ∧ a • I.mkQ 1 ≠ 0

-- Full-telescope checks: each proposition keeps the arbitrary carrier universe `u`;
-- the principal-ideal auxiliary needs only the ring structure.
example : (A : Type u) → [Ring A] → [Algebra ℂ A] → Prop :=
  @NonnilpotentLeftResolventStatement

example : (A : Type u) → [Ring A] → Prop :=
  @PrincipalLeftIdealProperStatement

example : (A : Type u) → [Ring A] → [Algebra ℂ A] → Prop :=
  @LeftShiftSimpleQuotientStatement

example : (A : Type u) → [Ring A] → [Algebra ℂ A] → Prop :=
  @UnitalSeparationStatement

-- The quotient by a left ideal carries the complex vector space structure and scalar
-- tower inherited from the algebra; no further scalar action is introduced.
example (A : Type u) [Ring A] [Algebra ℂ A] (I : Submodule A A) : Module ℂ (A ⧸ I) :=
  inferInstance

example (A : Type u) [Ring A] [Algebra ℂ A] (I : Submodule A A) :
    IsScalarTower ℂ A (A ⧸ I) :=
  inferInstance

example (A : Type u) [Ring A] [Algebra ℂ A] (I : Submodule A A) (z : ℂ) (x : A) :
    z • I.mkQ x = I.mkQ (z • x) ∧ algebraMap ℂ A z • I.mkQ x = z • I.mkQ x :=
  ⟨rfl, algebraMap_smul A z (I.mkQ x)⟩

-- The separating vector is the class of `1`: its image under `a` is the class of `a`,
-- which is nonzero exactly when `a ∉ I`.
example (A : Type u) [Ring A] (I : Submodule A A) (a : A) :
    a • I.mkQ 1 = I.mkQ a ∧ (a • I.mkQ 1 ≠ 0 ↔ a ∉ I) := by
  have h : a • I.mkQ 1 = I.mkQ a := by
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
  refine ⟨h, ?_⟩
  rw [h, Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end Langlands.Renard
