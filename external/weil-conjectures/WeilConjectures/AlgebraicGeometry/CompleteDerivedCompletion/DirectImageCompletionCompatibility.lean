/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageCompletionUnitSquare
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageReductionMapIsIso

/-!
# Reduction and completion compatibility for direct image

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proofs (2)--(3).
(blueprint: prop-weil-pbc-direct-image-limits-completion-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical reduction/direct-image mate.
Source: assertion (2), projection-formula normalization.
(blueprint: prop-weil-pbc-direct-image-limits-completion-compatibility) -/
def pushReductionMap : rpushModule l E f ⋙ red l E Y ⟶ red l E X ⋙ rpush l E f :=
  (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
    (.mk _ _ _ _ (pullReduction l E f).hom))

/-- The completion equation follows by applying the derived limit to the augmentation
square and the iterated-mate identity. -/
private theorem directImage_completion_compatibility_eq
    (χ : rpushModule l E f ⋙ dconstant l E Y ≅ dconstant l E X ⋙ rpush l E f)
    (hχ : χ.hom = (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
      (.mk _ _ _ _ (constantInterchange l E
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv)))
    (hsquare : ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (augmentation l E Y).app ((rpushModule l E f).obj K) ≫
          (pushReductionMap l E f).app K =
        χ.hom.app K ≫ (rpush l E f).map ((augmentation l E X).app K)) :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (rpushModule l E f).map ((kappa l E X).app K) ≫
          (pushLimitIso l E f).hom.app ((red l E X).obj K) =
        (kappa l E Y).app ((rpushModule l E f).obj K) ≫
          (rlim l E Y).map ((pushReductionMap l E f).app K) := by
  intro K
  let α := TwoSquare.mk (dconstant l E Y) (dpullModule l E f)
    (dpull l E f) (dconstant l E X)
    (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv
  have hi := iterated_mateEquiv_conjugateEquiv
    (moduleAdjunction l E f) (towerAdjunction l E f)
    (constantLimitAdjunction l E Y) (constantLimitAdjunction l E X) α
  have hu := unit_mateEquiv
    (constantLimitAdjunction l E X) (constantLimitAdjunction l E Y)
    (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f) α) K
  have hhu := congr_app hi ((dconstant l E X).obj K)
  rw [hhu] at hu
  have hnat := (pushLimitIso l E f).hom.naturality ((augmentation l E X).app K)
  have hs := congrArg ((rlim l E Y).map) (hsquare K)
  simp only [Functor.comp_map] at hnat
  simp only [Functor.map_comp] at hs
  dsimp [α] at hu
  have hχK := (congr_app hχ K).symm
  rw [hχK] at hu
  have hu' : (rpushModule l E f).map ((constantLimitAdjunction l E X).unit.app K) ≫
      (pushLimitIso l E f).hom.app ((dconstant l E X).obj K) =
    (constantLimitAdjunction l E Y).unit.app ((rpushModule l E f).obj K) ≫
      (rlim l E Y).map (χ.hom.app K) := by
    simpa [pushLimitIso, α] using hu
  simp only [kappa, NatTrans.comp_app, Functor.map_comp,
    Functor.whiskerRight_app, Category.assoc]
  dsimp [completion]
  rw [hnat, ← Category.assoc, hu', Category.assoc]
  change _ = (constantLimitAdjunction l E Y).unit.app _ ≫
    (rlim l E Y).map ((augmentation l E Y).app _) ≫
      (rlim l E Y).map ((pushReductionMap l E f).app K)
  rw [← hs]

/-- Reduction, completion-unit compatibility, and reconstruction for direct image:
assertions (2) and (3) of proposition-proper-base-change-complete-integral--1.
Source: literature/blueprint/latest/blueprint/sec-proper-base-change/sk-prop-pbc-complete/
prop-weil-pbc-direct-image-limits.proof.md, proofs (2) and (3); Stacks Tags 099N, 0944.
(blueprint: prop-weil-pbc-direct-image-limits-completion-compatibility)

Proof. (2) Let `K` be represented by a K-injective complex `I`. For
`B_n = [O_{E,Y} --π^n--> O_{E,Y}]` in degrees `-1, 0`,
proposition-proper-base-change-complete-integral and lemma-reduction-derived-nakayama--1 identify
`I ⊗ f^*B_n` with the `n`-th reduction of `I`; after `f_*` the resulting tower is strictly the
reduction tower of `f_*I` (lem-weil-pbc-direct-image-cone-tower-strictness). Each `I ⊗ f^*B_n` is
K-injective (lem-weil-pbc-split-perfect-tensor-kinjective), so every evaluation of the mate
`pushReductionMap` at `K` is an isomorphism, and levelwise detection in
proposition-proper-base-change-complete-integral shows `(pushReductionMap).app K` is invertible
(this is lem-weil-pbc-direct-image-completion-compatibility-isIso). The
finite-free chain map `θ_{I,B_n}` of lem-pbc-bounded-free-projection-chain-model
identifies the level-`n` map with the projection-formula morphism
(definition-projection-formula-map), and its strict naturality in `B_n` gives the
transition and quotient-unit squares.
(3) Let `i_K : cK → red K` be the reduction augmentation. The square
lem-weil-pbc-direct-image-completion-unit-square expresses `f_*` of this augmentation
through the constant-tower comparison `χ_K`. Apply `Rlim` and the naturality of
`pushLimitIso`; by lem-weil-pbc-constant-tower-pushforward-normalization,
`Rlim(χ_K)⁻¹ ∘ a_{cK}` is the identity of `Rf_*K` under `Rlim ∘ c ≅ 1`. With the definition
of `kappa` this is the displayed equation. If `K` is derived complete
(definition-derived-adic-completeness--1), `kappa_K` is invertible; in the equation `pushLimitIso`
and `Rlim(pushReductionMap K)` are invertible, so `kappa` of `Rf_*K` is invertible, i.e.
`Rf_*K` is derived complete, and `Rf_* kappa_K` followed by `pushLimitIso` gives
`Rf_*K ≅ Rlim(Rf_*^Tow red K)`. -/
theorem directImage_completion_compatibility :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsIso ((pushReductionMap l E f).app K)) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (rpushModule l E f).map ((kappa l E X).app K) ≫
          (pushLimitIso l E f).hom.app ((red l E X).obj K) =
        (kappa l E Y).app ((rpushModule l E f).obj K) ≫
          (rlim l E Y).map ((pushReductionMap l E f).app K)) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
        IsDerivedComplete l E Y ((rpushModule l E f).obj K) ∧
        Nonempty ((rpushModule l E f).obj K ≅
          (rlim l E Y).obj ((rpush l E f).obj ((red l E X).obj K)))) := by
  have h := directImageCompletionUnitSquare l E f
  rcases h with ⟨χ, hχ, hsquare⟩
  have hpush (K : DerivedCategory (AdicCompletion.Modules l E X)) :
      IsIso ((pushReductionMap l E f).app K) := by
    simpa [pushReductionMap] using directImage_pushReductionMap_isIso l E f K
  have heq := directImage_completion_compatibility_eq l E f χ hχ hsquare
  refine ⟨hpush, heq, ?_⟩
  intro K hK
  have hcomp := completeDerivedCompletion l E Y Y (𝟙 Y)
  have hcriterion := hcomp.2.2.2.2.2.2.2.1
  have hkX := (completeDerivedCompletion l E X X (𝟙 X)).2.2.2.2.2.2.2.1 K
  letI : IsIso ((kappa l E X).app K) := hkX.mp hK
  have hmap : IsIso ((rpushModule l E f).map ((kappa l E X).app K)) := inferInstance
  letI : IsIso ((rpushModule l E f).map ((kappa l E X).app K)) := hmap
  letI : IsIso ((pushLimitIso l E f).hom.app ((red l E X).obj K)) := inferInstance
  letI : IsIso ((pushReductionMap l E f).app K) := hpush K
  letI : IsIso ((rlim l E Y).map ((pushReductionMap l E f).app K)) := inferInstance
  have hky : IsIso ((kappa l E Y).app ((rpushModule l E f).obj K)) := by
    have hc : IsIso ((kappa l E Y).app ((rpushModule l E f).obj K) ≫
        (rlim l E Y).map ((pushReductionMap l E f).app K)) := by
      rw [← heq K]
      infer_instance
    letI := hc
    exact IsIso.of_isIso_comp_right
      ((kappa l E Y).app ((rpushModule l E f).obj K))
      ((rlim l E Y).map ((pushReductionMap l E f).app K))
  constructor
  · exact (hcriterion ((rpushModule l E f).obj K)).mpr hky
  · let e₁ : (rpushModule l E f).obj K ≅
        (rpushModule l E f).obj ((rlim l E X).obj ((red l E X).obj K)) :=
      asIso ((rpushModule l E f).map ((kappa l E X).app K))
    let e₂ : (rpushModule l E f).obj ((rlim l E X).obj ((red l E X).obj K)) ≅
        (rlim l E Y).obj ((rpush l E f).obj ((red l E X).obj K)) :=
      asIso ((pushLimitIso l E f).hom.app ((red l E X).obj K))
    exact ⟨e₁ ≪≫ e₂⟩

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
