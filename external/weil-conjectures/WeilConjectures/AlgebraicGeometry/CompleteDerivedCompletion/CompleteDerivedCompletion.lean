/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionDefs
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionBasic
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionPullback
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionLimit
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionCompletion

/-!
# Towers and the derived completion

The six assertions about integral module towers and their derived completion, for the
definitions of `CompleteDerivedCompletionDefs`.

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-derived-completion.md
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

/-- All six assertions about integral module towers and their derived completion.
Source: blueprint Notation 1--4 and Assertions 1--6
(blueprint: proposition-proper-base-change-complete-integral).

Proof plan, following the node's fifteen steps:
1. On the small pro-étale site identify internal modules with sheaves of modules using
   `def-weil-pbc-internal-abelian-sheaf-module-equivalence`. Apply
   `lem-weil-pbc-small-module-diagrams-grothendieck`; evaluation is exact by
   `lem-weil-tower-category-levelwise-abelian`.
2. The free diagram at n is N below n and zero above n. Its adjunction to evaluation
   and levelwise exactness give the exact left adjoint. Apply
   `lem-weil-pbc-right-adjoint-preserves-kinjective` to evaluation.
3. Both module and tower categories have K-injective resolutions by
   `prose-03-02`. Apply `lem-weil-pbc-kinjective-total-derived`
   to ordinary limit and levelwise pushforward; the derived-limit exactness also follows
   from `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
4. Represent a derived tower arrow by a map between K-injective resolutions using
   `lem-weil-pbc-kinjective-hom-derived`. Evaluation commutes with cohomology; an arrow
   whose evaluations are isomorphisms is a quasi-isomorphism levelwise and hence globally.
5. Whisker the ordinary module adjunction levelwise. Pullback is exact by
   `prose-03-02`. Apply
   `lem-weil-pbc-tower-derived-evaluation-normalization` to obtain the canonical mate
   isomorphisms, their transition compatibility and their unit and counit equations.
6. Ordinary pushforward and limit have exact left adjoints and preserve K-injectives.
   The right adjoint pushforward preserves ordinary limits by
   `situation-conventions`. Derive that ordinary isomorphism;
   equivalently conjugate the constant-pullback comparison under the derived adjunctions.
7. Products are exact by `proposition-exact-products--1`. Apply
   `lem-weil-pbc-exact-products-roos-comparison` to identify Rlim with the functorial
   Milnor fibre of 1-shift, normalized by the ordinary limit inclusion.
8. For a constant tower, 1-shift is split surjective, by successive subtraction.
   Its kernel is the diagonal complex and the extra summand is contractible. The
   constant-limit unit is therefore an isomorphism, with the specified diagonal map.
9. An exact equivalence preserves products and intertwines the shift endomorphism by
   its projections. By `situation-conventions`, applying it to the
   Milnor fibre gives the comparison for the levelwise equivalence. This is the
   isomorphism obtained by conjugating the constant comparison for its inverse.
10. For bounded finite-free P only finitely many finite sums occur in each total degree.
   They commute with products and the shift. Use `lem-pc-tensor-mapping-cone-iso` for
   cone compatibility and `lem-weil-pbc-independent-bounded-flat-kflat` for K-flatness.
   This gives the tensor comparison naturally on the entire derived tower category.
11. The two-term resolutions R_n=[A→A] use π^(n+1) and transitions (π,1).
   `lemma-reduction-derived-nakayama--1` identifies them with finite reductions.
   `lem-pur-kflat-tensor-quasiiso-independent` gives descent of the strict cone tower;
   tensor-cone compatibility gives exactness. Degree-zero inclusions commute with
   transitions and identify the resulting completion unit with
   `definition-derived-adic-completeness--1`.
12. Choose a K-flat representative by `lem-pc-kflat-resolution`. For fixed m, commute
   tensor with R_m through Rlim by step 10, replace R_m by A_m, and restrict to the
   cofinal tail n≥m using `lem-fix-cofinal-roos-restriction`. The resulting tower splits
   into the constant reduction and the shifted reduction with transition π.
13. The shift on the second tower has m+1-st power zero. Hence 1-shift has the finite
   geometric-series inverse and its fibre is contractible. The constant summand has
   limit the m-th reduction by step 8. Track the augmented degree-zero inclusions:
   the specified map κ_M induces the identity of that constant summand, hence its
   actual finite reduction is invertible.
14. The map red(κ_M) already lives in the derived category of towers. Its evaluations
   are the maps of step 13. Apply the conservativity from step 4 to this map itself.
15. Apply `lem-weil-pbc-ringed-koszul-completion-reflector` with the singleton
   uniformizer. Its tower and unit are those of step 11. Its completion is complete;
   its unit criterion, identified with `definition-derived-adic-completeness--1`, gives the stated
   completeness of every output without assuming completeness of the input.
-/
theorem completeDerivedCompletion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T T' : Scheme.{u}) (f : T' ⟶ T) :
    IsGrothendieckAbelian.{u+1} (CompleteDerivedCompletion.Tow l E T) ∧
    (∀ n : ℕ,
      PreservesFiniteLimits (CompleteDerivedCompletion.ev l E T n) ∧
      PreservesFiniteColimits (CompleteDerivedCompletion.ev l E T n) ∧
      PreservesFiniteLimits (CompleteDerivedCompletion.freeDiagram l E T n) ∧
      PreservesFiniteColimits (CompleteDerivedCompletion.freeDiagram l E T n) ∧
      (∀ I : CochainComplex (CompleteDerivedCompletion.Tow l E T) ℤ,
        I.IsKInjective → CochainComplex.IsKInjective
          (((CompleteDerivedCompletion.ev l E T n).mapHomologicalComplex (.up ℤ)).obj I))) ∧
    (∀ {M N : CompleteDerivedCompletion.DTow l E T} (a : M ⟶ N),
      IsIso a ↔ ∀ n : ℕ, IsIso ((CompleteDerivedCompletion.dev l E T n).map a)) ∧
    (PreservesFiniteLimits (CompleteDerivedCompletion.pull l E f) ∧
      PreservesFiniteColimits (CompleteDerivedCompletion.pull l E f) ∧
      (∀ n : ℕ, CompleteDerivedCompletion.pull l E f ⋙
          CompleteDerivedCompletion.ev l E T' n =
        CompleteDerivedCompletion.ev l E T n ⋙
          CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) ∧
      ∃ β : ∀ n : ℕ,
          CompleteDerivedCompletion.rpush l E f ⋙ CompleteDerivedCompletion.dev l E T n ≅
            CompleteDerivedCompletion.dev l E T' n ⋙ CompleteDerivedCompletion.rpushModule l E f,
        (∀ n : ℕ, (β n).hom = CompleteDerivedCompletion.pushEvaluationMap l E f n) ∧
        (∀ (n : ℕ) (M : CompleteDerivedCompletion.DTow l E T),
          (CompleteDerivedCompletion.dev l E T n).map
              ((CompleteDerivedCompletion.towerAdjunction l E f).unit.app M) ≫
            (β n).hom.app ((CompleteDerivedCompletion.dpull l E f).obj M) =
          (CompleteDerivedCompletion.moduleAdjunction l E f).unit.app
              ((CompleteDerivedCompletion.dev l E T n).obj M) ≫
            (CompleteDerivedCompletion.rpushModule l E f).map
              ((CompleteDerivedCompletion.pullEvaluation l E f n).inv.app M)) ∧
        (∀ (n : ℕ) (N : CompleteDerivedCompletion.DTow l E T'),
          (CompleteDerivedCompletion.dev l E T' n).map
              ((CompleteDerivedCompletion.towerAdjunction l E f).counit.app N) =
          (CompleteDerivedCompletion.pullEvaluation l E f n).hom.app
              ((CompleteDerivedCompletion.rpush l E f).obj N) ≫
            (CompleteDerivedCompletion.dpullModule l E f).map ((β n).hom.app N) ≫
            (CompleteDerivedCompletion.moduleAdjunction l E f).counit.app
              ((CompleteDerivedCompletion.dev l E T' n).obj N)) ∧
        (∀ (n : ℕ) (M : CompleteDerivedCompletion.DTow l E T'),
          (CompleteDerivedCompletion.transition l E T n).app
              ((CompleteDerivedCompletion.rpush l E f).obj M) ≫ (β n).hom.app M =
            (β (n+1)).hom.app M ≫ (CompleteDerivedCompletion.rpushModule l E f).map
              ((CompleteDerivedCompletion.transition l E T' n).app M))) ∧
    Nonempty (CompleteDerivedCompletion.rlim l E T' ⋙
        CompleteDerivedCompletion.rpushModule l E f ≅
      CompleteDerivedCompletion.rpush l E f ⋙ CompleteDerivedCompletion.rlim l E T) ∧
    ((CompleteDerivedCompletion.rlim l E T).IsTriangulated ∧
      (∀ (e : AdicCompletion.Modules l E T ≌ AdicCompletion.Modules l E T')
          [e.functor.Additive],
        Nonempty (CompleteDerivedCompletion.rlim l E T ⋙ e.functor.mapDerivedCategory ≅
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor).mapDerivedCategory ⋙
            CompleteDerivedCompletion.rlim l E T')) ∧
      (∀ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
          (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
          (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)),
        Nonempty (CompleteDerivedCompletion.rlim l E T ⋙
            (CondensedRing.derivedTensor (DerivedNakayama.integerRing l E) T).flip.obj
              (DerivedCategory.Q.obj P) ≅
          CompleteDerivedCompletion.tensorTower l E T P hb hf ⋙
            CompleteDerivedCompletion.rlim l E T))) ∧
    (∀ M : DerivedCategory (AdicCompletion.Modules l E T),
      IsDerivedComplete l E T ((CompleteDerivedCompletion.completion l E T).obj M) ∧
      IsIso ((CompleteDerivedCompletion.red l E T).map
        ((CompleteDerivedCompletion.kappa l E T).app M)) ∧
      ∀ n : ℕ, IsIso ((AdicCompletion.derivedReduction l E T n).map
        ((CompleteDerivedCompletion.kappa l E T).app M))) ∧
    (∀ M : DerivedCategory (AdicCompletion.Modules l E T),
      IsDerivedComplete l E T M ↔ IsIso ((CompleteDerivedCompletion.kappa l E T).app M)) ∧
    (∀ n : ℕ, Nonempty (CompleteDerivedCompletion.red l E T ⋙
        CompleteDerivedCompletion.dev l E T n ≅
      AdicCompletion.derivedReduction l E T n ⋙ AdicCompletion.restrict l E T n)) ∧
    (∃ (_shift : (CompleteDerivedCompletion.red l E T).CommShift ℤ),
      (CompleteDerivedCompletion.red l E T).IsTriangulated) ∧
    (∀ M : DerivedCategory (AdicCompletion.Modules l E T),
      IsIso ((CompleteDerivedCompletion.constantLimitAdjunction l E T).unit.app M)) ∧
    (∃ (_products : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))),
      ∀ M : CompleteDerivedCompletion.DTow l E T,
        IsDerivedLimit (K := fun n : ℕ ↦ (CompleteDerivedCompletion.dev l E T n).obj M)
          (fun n : ℕ ↦ (CompleteDerivedCompletion.transition l E T n).app M)
          ((CompleteDerivedCompletion.rlim l E T).obj M)) ∧
    Nonempty (DerivedCategory.Q ⋙ CompleteDerivedCompletion.rlim l E T ≅
      ExactProductsRoos.fibre ⋙ DerivedCategory.Q) ∧
    (∀ (M : DerivedCategory (AdicCompletion.Modules l E T))
        (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
        (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P)
        (e : DerivedCategory.Q.obj P ≅ M),
      ∃ ε : DerivedCategory.Q.obj (AdicCompletion.roos l E T P) ≅
          (CompleteDerivedCompletion.completion l E T).obj M,
        AdicCompletion.completionMap l E T M P e ≫ ε.hom =
          (CompleteDerivedCompletion.kappa l E T).app M) := by
  refine ⟨CompleteDerivedCompletion.towerGrothendieck l E T,
    fun n ↦ CompleteDerivedCompletion.evaluation_properties l E T n,
    fun a ↦ CompleteDerivedCompletion.dev_conservative l E T a,
    CompleteDerivedCompletion.pullback_properties l E f,
    CompleteDerivedCompletion.pushLimit_nonempty l E f,
    ⟨CompleteDerivedCompletion.rlim_isTriangulated l E T,
      fun e _ ↦ CompleteDerivedCompletion.rlim_equivalence l E e, ?_⟩,
    ?_, ?_, ?_, ?_,
    CompleteDerivedCompletion.constantLimit_unit_isIso l E T,
    CompleteDerivedCompletion.rlim_isDerivedLimit l E T,
    CompleteDerivedCompletion.rlim_roos l E T, ?_⟩
  · exact CompleteDerivedCompletion.tensorLimitIso l E T
  · have hfinite (M : DerivedCategory (AdicCompletion.Modules l E T)) (n : ℕ) :
        IsIso ((AdicCompletion.derivedReduction l E T n).map
          ((CompleteDerivedCompletion.kappa l E T).app M)) := by
      exact CompleteDerivedCompletion.finiteReduction_kappa l E T M n
    intro M
    refine ⟨CompleteDerivedCompletion.completion_isDerivedComplete l E T M, ?_, hfinite M⟩
    apply (CompleteDerivedCompletion.dev_conservative l E T _).2
    intro n
    obtain ⟨e⟩ := CompleteDerivedCompletion.reductionEvaluation l E T n
    apply (NatIso.isIso_map_iff e ((CompleteDerivedCompletion.kappa l E T).app M)).2
    have := hfinite M n
    exact inferInstanceAs (IsIso ((AdicCompletion.restrict l E T n).map
      ((AdicCompletion.derivedReduction l E T n).map
        ((CompleteDerivedCompletion.kappa l E T).app M))))
  · exact CompleteDerivedCompletion.isDerivedComplete_iff l E T
  · exact CompleteDerivedCompletion.reductionEvaluation l E T
  · exact CompleteDerivedCompletion.red_triangulated l E T
  · exact CompleteDerivedCompletion.completionComparison l E T

end AlgebraicGeometry.ProEtale
