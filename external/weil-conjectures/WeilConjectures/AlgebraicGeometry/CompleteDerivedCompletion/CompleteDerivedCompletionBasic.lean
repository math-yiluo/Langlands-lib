/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionDefs
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Towers and the derived completion: formal assertions

The tower category is Grothendieck abelian, evaluation and the free diagram are exact,
evaluation preserves K-injective complexes, and the derived evaluations detect
isomorphisms. Source: blueprint Assertions 1--2
(blueprint: proposition-proper-base-change-complete-integral).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The free diagram is exact.
Source: blueprint Assertion 1 (blueprint: proposition-proper-base-change-complete-integral).
Proof: at level m it is the coproduct of copies of N indexed by the subsingleton set of
arrows n to m. Such a finite coproduct is exact; limits of towers are levelwise. -/
theorem freeDiagram_exact (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (freeDiagram l E T n) ∧
      PreservesFiniteColimits (freeDiagram l E T n) := by
  classical
  let A := AdicCompletion.Modules l E T
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  let G := evaluationLeftAdjoint A (op n)
  have (m : ℕᵒᵖ) : PreservesFiniteLimits (G ⋙ (evaluation ℕᵒᵖ A).obj m) := by
    let e : G ⋙ (evaluation ℕᵒᵖ A).obj m ≅
        Functor.const (Discrete (op n ⟶ m)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        simp [G, evaluationLeftAdjoint]
        rfl)
    exact preservesFiniteLimits_of_natIso e.symm
  have hG : PreservesFiniteLimits G := ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation G J (fun m ↦ inferInstance)⟩
  have : G.IsLeftAdjoint := (evaluationAdjunctionRight A (op n)).isLeftAdjoint
  exact ⟨hG, inferInstance⟩

/-- Evaluation of towers is exact and preserves K-injective complexes, and the free diagram
is exact. Source: blueprint Assertion 1 (blueprint:
proposition-proper-base-change-complete-integral). Proof: evaluation is exact since limits and
colimits of towers are levelwise; the free diagram is `freeDiagram_exact`, and an exact left adjoint
makes its right adjoint preserve K-injectives. -/
theorem evaluation_properties (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (ev l E T n) ∧
      PreservesFiniteColimits (ev l E T n) ∧
      PreservesFiniteLimits (freeDiagram l E T n) ∧
      PreservesFiniteColimits (freeDiagram l E T n) ∧
      (∀ I : CochainComplex (Tow l E T) ℤ,
        I.IsKInjective → CochainComplex.IsKInjective
          (((ev l E T n).mapHomologicalComplex (.up ℤ)).obj I)) := by
  refine ⟨inferInstance, inferInstance, (freeDiagram_exact l E T n).1,
    (freeDiagram_exact l E T n).2, ?_⟩
  intro I hI
  exact tower_evaluation_isKInjective _ I (op n)

/-- The derived evaluations detect isomorphisms of derived towers.
Source: blueprint Assertion 2 (blueprint: proposition-proper-base-change-complete-integral).
Proof: exact evaluation commutes with cohomology, and an arrow of towers is an
isomorphism when all of its levels are. -/
theorem dev_conservative (T : Scheme.{u}) {M N : DTow l E T} (a : M ⟶ N) :
    IsIso a ↔ ∀ n : ℕ, IsIso ((dev l E T n).map a) := by
  refine ⟨fun _ n ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro k
  rw [NatTrans.isIso_iff_isIso_app]
  intro m
  let e := (ev l E T m.unop).mapDerivedCategoryHomologyFunctorIso k
  have hn := e.hom.naturality a
  have : IsIso ((DerivedCategory.homologyFunctor _ k).map ((dev l E T m.unop).map a)) :=
    have := h m.unop
    inferInstance
  have : IsIso ((DerivedCategory.homologyFunctor _ k ⋙ ev l E T m.unop).map a ≫
      e.hom.app N) := by
    rw [hn]
    dsimp only [Functor.comp_map]
    infer_instance
  change IsIso ((DerivedCategory.homologyFunctor _ k ⋙ ev l E T m.unop).map a)
  exact (isIso_comp_right_iff _ (e.hom.app N)).mp this

/-- The derived pushforward commutes with derived limits.
Source: blueprint Assertion 4 (blueprint: proposition-proper-base-change-complete-integral). -/
theorem pushLimit_nonempty {T T' : Scheme.{u}} (f : T' ⟶ T) :
    Nonempty (rlim l E T' ⋙ rpushModule l E f ≅ rpush l E f ⋙ rlim l E T) :=
  ⟨pushLimitIso l E f⟩

/-- The derived limit is triangulated.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral). -/
theorem rlim_isTriangulated (T : Scheme.{u}) : (rlim l E T).IsTriangulated :=
  inferInstance

end CompleteDerivedCompletion

end AlgebraicGeometry.ProEtale
