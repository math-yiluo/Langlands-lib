/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreHomExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreTorsorIdentity

/-!
# Extending the action on a finite étale generic-fibre torsor

## References

* Stacks Project, Tag 0BQM (full faithfulness), and Tag 0EYJ (extended action)
* Stacks Project, Tag 0BQM, proof (fully faithful restriction of finite étale covers of a normal
  integral scheme to its generic point)
* Tag 0EYJ, proof (extension of the action)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A given finite étale extension of a generic-fibre torsor inherits its action and torsor
identity. This does not require a section or an invertible group order. -/
theorem GaloisCover.exists_action_on_finiteEtale_extension {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη) {P : Scheme.{u}} (π : P ⟶ C)
    [IsFinite π] [Etale π] (ψ : Z.P ⟶ P) (hψ : IsPullback ψ Z.π π j) :
    ∃ (a : G → (P ⟶ P)) (ha : ∀ g : G, a g ≫ π = π),
      a 1 = 𝟙 P ∧ (∀ g h : G, a (g * h) = a h ≫ a g) ∧
      (∀ g : G, Z.smul g ≫ ψ = ψ ≫ a g) ∧
      IsIso (Sigma.desc fun g : G ↦
        pullback.lift (f := π) (g := π) (a g) (𝟙 P) (by simp [ha])) := by
  classical
  have hex (g : G) := finiteEtale_genericFibre_hom_extension hS c q j hCη
    π π Z.π Z.π ψ ψ hψ hψ (Z.smul g) (Z.smul_π g)
  choose a ha using hex
  have hover (g : G) : a g ≫ π = π := (ha g).1.1
  have hcompat (g : G) : Z.smul g ≫ ψ = ψ ≫ a g := (ha g).1.2.symm
  refine ⟨a, hover, ?_, ?_, hcompat, ?_⟩
  · exact ((ha 1).2 (𝟙 P) ⟨by simp, by simp [Z.one_smul]⟩).symm
  · intro g h
    apply ((ha (g * h)).2 (a h ≫ a g) _).symm
    constructor
    · simp [hover]
    · calc
        ψ ≫ (a h ≫ a g) = (ψ ≫ a h) ≫ a g := by simp
        _ = (Z.smul h ≫ ψ) ≫ a g := by rw [hcompat]
        _ = Z.smul h ≫ (Z.smul g ≫ ψ) := by rw [Category.assoc, ← hcompat]
        _ = Z.smul (g * h) ≫ ψ := by rw [Z.mul_smul, Category.assoc]
  · exact GaloisCover.isIso_sigmaDesc_of_genericFibre hS c G q j hCη Z π ψ hψ
      a hover hcompat

end AlgebraicGeometry.Scheme
