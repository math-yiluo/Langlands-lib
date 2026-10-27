import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Renard B.II: Schur's lemma for simple unital modules over complex algebras

Source: Renard, *Représentations des groupes réductifs p-adiques* (French edition
dated 9 July 2026), Appendix B.II "Lemme de Schur", printed page 272 / PDF page 278.
Let `A` be a complex algebra and `M` a simple `A`-module which is also a complex
vector space. Then
* a) `End_A(M)` is a division algebra;
* b) if `M` has at most countable dimension over `ℂ`, then `End_A(M) ≃ ℂ`; it
  suffices that `A` has at most countable dimension.

The source allows a nonunital algebra and first adjoins a unit. This file states
only the resulting unital core: `A` is an associative unital ring (for the complex
assertions, a unital complex algebra, not necessarily commutative) in universe `u`,
and `M` is an ordinary unital left `A`-module in an independent universe `v`. In the
complex assertions the complex structure of `M` is compatible with that of `A`
through `IsScalarTower ℂ A M`. Simplicity is Mathlib's `IsSimpleModule`, carried
inside every proposition. "Dimension at most countable" is
`Module.rank ≤ Cardinal.aleph0`, and `End_A(M) ≃ ℂ` is bijectivity of the actual
map `algebraMap ℂ (Module.End A M)`, i.e. every `A`-linear endomorphism is scalar
multiplication by a unique complex number (`bijective_algebraMap_end_iff`).

Besides the two parts of the theorem, the cyclic action map `a ↦ a • m`, the
evaluation map `f ↦ f m` and the two countable-dimension transfers used in the
source proof are stated separately. Only propositions are stated here; none of
Schur's assertions is proved or assumed.
-/

universe u v

namespace Langlands.Renard

section Ring

/-- Renard B.II, Théorème a), at ring generality: the endomorphism ring of a simple
unital module over an arbitrary ring is a division ring, i.e. it is nontrivial and
every nonzero endomorphism is invertible. -/
@[pp_with_univ]
def SchurEndDivisionStatement (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module A M] : Prop :=
  IsSimpleModule A M →
    Nontrivial (Module.End A M) ∧ ∀ f : Module.End A M, f ≠ 0 → IsUnit f

/-- Renard B.II, first step of the proof, at ring generality: a nonzero endomorphism
of a simple unital module has zero kernel and full image, so it is bijective. -/
@[pp_with_univ]
def SchurEndBijectiveStatement (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module A M] : Prop :=
  IsSimpleModule A M → ∀ f : Module.End A M, f ≠ 0 → Function.Bijective f

end Ring

section Complex

/-- The complex-linear cyclic action map of Renard B.II, `a ↦ a • m`, is
`(LinearMap.toSpanSingleton A M m).restrictScalars ℂ`. -/
theorem schur_cyclicMap_apply (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] (m : M) (a : A) :
    ((LinearMap.toSpanSingleton A M m).restrictScalars ℂ) a = a • m :=
  rfl

/-- The complex-linear evaluation map of Renard B.II, `f ↦ f m`, is
`LinearMap.applyₗ' ℂ m` on `Module.End A M`. -/
theorem schur_evaluation_apply (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] (m : M)
    (f : Module.End A M) :
    (LinearMap.applyₗ' ℂ m : Module.End A M →ₗ[ℂ] M) f = f m :=
  rfl

/-- Bijectivity of `algebraMap ℂ (Module.End A M)` says exactly that every
`A`-linear endomorphism of `M` is scalar multiplication by a unique complex number.
This explains the scalarity statements below; it proves none of them. -/
theorem bijective_algebraMap_end_iff (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    Function.Bijective (algebraMap ℂ (Module.End A M)) ↔
      ∀ f : Module.End A M, ∃! z : ℂ, ∀ m : M, f m = z • m := by
  rw [Function.bijective_iff_existsUnique]
  refine forall_congr' fun f => existsUnique_congr fun z => ?_
  rw [LinearMap.ext_iff]
  exact forall_congr' fun m => eq_comm

/-- Renard B.II, proof of the countability transfer: for a nonzero vector `m` of a
simple unital module, the complex-linear action map `A → M`, `a ↦ a • m`, is
surjective (`A • m = M`). -/
@[pp_with_univ]
def SchurCyclicMapSurjectiveStatement (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] : Prop :=
  IsSimpleModule A M → ∀ m : M, m ≠ 0 →
    Function.Surjective ((LinearMap.toSpanSingleton A M m).restrictScalars ℂ)

/-- Renard B.II, proof of b): for a nonzero vector `m` of a simple unital module, the
complex-linear evaluation map `End_A(M) → M`, `f ↦ f m`, is injective. -/
@[pp_with_univ]
def SchurEvaluationInjectiveStatement (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] : Prop :=
  IsSimpleModule A M → ∀ m : M, m ≠ 0 →
    Function.Injective (LinearMap.applyₗ' ℂ m : Module.End A M →ₗ[ℂ] M)

/-- Renard B.II, proof of the final sentence: if `A` has at most countable complex
dimension, so does a simple unital `A`-module whose complex structure is compatible
with that of `A`. The compatibility is a premise of the proposition. -/
@[pp_with_univ]
def SchurModuleRankCountableStatement (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] : Prop :=
  IsScalarTower ℂ A M → IsSimpleModule A M →
    Module.rank ℂ A ≤ Cardinal.aleph0 → Module.rank ℂ M ≤ Cardinal.aleph0

/-- Renard B.II, proof of b): if a simple unital module has at most countable complex
dimension, so does its endomorphism algebra. -/
@[pp_with_univ]
def SchurEndRankCountableStatement (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] : Prop :=
  IsSimpleModule A M → Module.rank ℂ M ≤ Cardinal.aleph0 →
    Module.rank ℂ (Module.End A M) ≤ Cardinal.aleph0

/-- Renard B.II, Théorème b): if a simple unital module has at most countable complex
dimension, every endomorphism is scalar multiplication by a unique complex number,
i.e. `algebraMap ℂ (Module.End A M)` is bijective. -/
@[pp_with_univ]
def SchurScalarOfModuleRankCountableStatement (A : Type u) [Ring A] [Algebra ℂ A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    Prop :=
  IsSimpleModule A M → Module.rank ℂ M ≤ Cardinal.aleph0 →
    Function.Bijective (algebraMap ℂ (Module.End A M))

/-- Renard B.II, Théorème b), final sentence: at most countable complex dimension of
`A` suffices for `algebraMap ℂ (Module.End A M)` to be bijective. -/
@[pp_with_univ]
def SchurScalarOfAlgebraRankCountableStatement (A : Type u) [Ring A] [Algebra ℂ A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    Prop :=
  IsSimpleModule A M → Module.rank ℂ A ≤ Cardinal.aleph0 →
    Function.Bijective (algebraMap ℂ (Module.End A M))

/-- Renard B.II, Théorème, unital core: parts a) and b), with both countability
alternatives of b), for a unital complex algebra and a compatible unital module. -/
@[pp_with_univ]
def SchurTheoremStatement (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] : Prop :=
  SchurEndDivisionStatement A M ∧ SchurScalarOfModuleRankCountableStatement A M ∧
    SchurScalarOfAlgebraRankCountableStatement A M

end Complex

end Langlands.Renard
