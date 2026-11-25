/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraAffineGenerators

/-! # Ring operations detected on homogeneous conormal representatives

Source: Stacks Project, Divisors, Tag 0634.
(blueprint: lem-pur-conormal-algebra-homogeneous-ring-map).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ConormalGradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An additive map with the ideal-power representative formula preserves the unit
and products. This is the affine algebra-law check in conormal functoriality.
Source: Stacks Project, Divisors, Tag 0634.
(blueprint: lem-pur-conormal-algebra-homogeneous-ring-map).

Proof: Lift a product of two ideal-power representatives using the affine ideal
sections and the power-identification isomorphism. The representative formula and
the multiplication field of both presentations then prove multiplicativity on
homogeneous classes. Apply additive homogeneous induction in each variable.
The degree-zero representative of one maps to one, proving preservation of the unit. -/
theorem homogeneous_preserves_ringOperations {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (A : Presentation i) (A' : Presentation i') (U : X.affineOpens) (U' : X'.affineOpens)
    (φ : Γ(X', U'.1) →+* Γ(X, U.1))
    (F : A'.algebra.right.obj.obj (op (i' ⁻¹ᵁ U'.1)) →+
      A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)))
    (hF : ∀ (n : ℕ) (a : (power i' n).val.obj (op U'.1)),
      ∃ b : (power i n).val.obj (op U.1),
        (powerInclusion i n).app U.1 b = φ ((powerInclusion i' n).app U'.1 a) ∧
        F (homogeneousClass i' A'.algebra A'.inclusion n U'.1 a) =
          homogeneousClass i A.algebra A.inclusion n U.1 b) :
    F 1 = 1 ∧ ∀ a b, F (a * b) = F a * F b := by
  have one_class (Y W : Scheme.{u}) (j : W ⟶ Y) [IsClosedImmersion j]
      (B : Presentation j) (V : Y.Opens) :
      homogeneousClass j B.algebra B.inclusion 0 V (show Γ(Y, V) from 1) = 1 := by
    rw [B.constants]
    simp
  constructor
  · obtain ⟨b, hb, hFb⟩ := hF 0 (show Γ(X', U'.1) from 1)
    have hb' : b = (show Γ(X, U.1) from 1) := by
      change b = φ (1 : Γ(X', U'.1)) at hb
      simpa only [map_one] using hb
    rw [one_class, hb', one_class] at hFb
    exact hFb
  · have hmul (m n : ℕ) (a : (power i' m).val.obj (op U'.1))
        (b : (power i' n).val.obj (op U'.1)) :
        F (homogeneousClass i' A'.algebra A'.inclusion m U'.1 a *
          homogeneousClass i' A'.algebra A'.inclusion n U'.1 b) =
        F (homogeneousClass i' A'.algebra A'.inclusion m U'.1 a) *
          F (homogeneousClass i' A'.algebra A'.inclusion n U'.1 b) := by
      obtain ⟨e, he⟩ := A'.affineChart U'
      obtain ⟨ha, _⟩ := he m a
      obtain ⟨hb, _⟩ := he n b
      obtain ⟨q, hq⟩ := A'.powerIdentification (m + n)
      have hx : (@id Γ(X', U'.1) ((powerInclusion i' m).app U'.1 a)) *
          (@id Γ(X', U'.1) ((powerInclusion i' n).app U'.1 b)) ∈
          (i'.ker ^ (m + n)).ideal U' := by
        rw [Scheme.IdealSheafData.ideal_pow, pow_add]
        exact Ideal.mul_mem_mul ha hb
      have hxrange : (@id Γ(X', U'.1) ((powerInclusion i' m).app U'.1 a)) *
          (@id Γ(X', U'.1) ((powerInclusion i' n).app U'.1 b)) ∈
          Set.range ((i'.ker ^ (m + n)).toModulesι.app U'.1) := by
        rw [(i'.ker ^ (m + n)).range_toModulesι_app U']
        exact hx
      obtain ⟨s, hs⟩ := hxrange
      let c := q.inv.app U'.1 s
      have hc : (powerInclusion i' (m + n)).app U'.1 c =
          (@id Γ(X', U'.1) ((powerInclusion i' m).app U'.1 a)) *
          (@id Γ(X', U'.1) ((powerInclusion i' n).app U'.1 b)) := by
        rw [← hq]
        change ((q.inv ≫ q.hom ≫ (i'.ker ^ (m + n)).toModulesι).app U'.1) s = _
        simpa using hs
      obtain ⟨a₁, ha₁, hFa⟩ := hF m a
      obtain ⟨b₁, hb₁, hFb⟩ := hF n b
      obtain ⟨c₁, hc₁, hFc⟩ := hF (m + n) c
      rw [A'.multiplication m n U'.1 a b c hc, hFc, hFa, hFb]
      symm
      apply A.multiplication
      change (powerInclusion i (m + n)).app U.1 c₁ =
        (@id Γ(X, U.1) ((powerInclusion i m).app U.1 a₁)) *
          (@id Γ(X, U.1) ((powerInclusion i n).app U.1 b₁))
      rw [hc₁, hc, map_mul, ha₁, hb₁]
      rfl
    intro a b
    induction a using affine_homogeneous_induction i' A' U' with
    | hzero => simp
    | hadd a₁ a₂ ha₁ ha₂ => simp only [add_mul, map_add, ha₁, ha₂]
    | hhom m a =>
      induction b using affine_homogeneous_induction i' A' U' with
      | hzero => simp
      | hadd b₁ b₂ hb₁ hb₂ => simp only [mul_add, map_add, hb₁, hb₂]
      | hhom n b => exact hmul m n a b

end AlgebraicGeometry.ConormalGradedAlgebra
