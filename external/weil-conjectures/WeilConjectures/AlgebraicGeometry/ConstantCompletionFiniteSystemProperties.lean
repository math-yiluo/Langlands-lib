/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
/-! Flatness and reduction data for the finite constant completion tower.
Source: Stacks Project, Tags 093M and 0912
(auxiliary; not a blueprint node).
The module structures in this statement are the canonical quotient-section module
structures induced by sheafification of the constant quotient presheaves. -/
@[expose] public noncomputable section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]

/-- The canonical `A ⧸ I^(n+1)`-module structure on the sections of the finite
constant quotient sheaf, induced by the sheafification unit of the constant quotient
presheaf (auxiliary; not a blueprint node). -/
@[instance_reducible] def finiteSystemModule (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) (U : Cᵒᵖ) :
    Module (A ⧸ I ^ (n + 1)) (adicTerm J A (finiteSystemUnder J A I) n U) :=
  (((toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of (A ⧸ I ^ (n + 1))))).app U).hom).toModule

/--
Source: Stacks Project, Tags 093M and 0912
(auxiliary; not a blueprint node).
Proof: with the canonical module structures `finiteSystemModule`, the scalar tower
is the naturality of the sheafification unit for the quotient map `A → A ⧸ I^(n+1)`.
Flatness and tensor reduction are
`finiteSystem_flat_and_reduction`. The transition `n + 1 → n` is the constant sheaf
of the surjective quotient ring map; on underlying sheaves of types it is the constant
sheaf of a surjection of sets, which has a set-theoretic section, so the transition
has a section on every object and is surjective.
-/
theorem finiteSystem_properties (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    letI : ∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1))
        (adicTerm J A (finiteSystemUnder J A I) n U) :=
      finiteSystemModule J A I
    (∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)) ∧
    (∀ (n : ℕ) (U : Cᵒᵖ), Module.Flat (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)) ∧
    (∀ (n : ℕ) (U : Cᵒᵖ),
      Function.Surjective (adicTransition J A (finiteSystemUnder J A I) (n + 1) n
        (Nat.le_succ n) U)) ∧
    (∀ (m n : ℕ) (U : Cᵒᵖ),
      ∃ e : TensorProduct A (adicTerm J A (finiteSystemUnder J A I) m U)
          (A ⧸ I ^ (n + 1)) ≃ₗ[A] adicTerm J A (finiteSystemUnder J A I) (min m n) U,
        ∀ (b : adicTerm J A (finiteSystemUnder J A I) m U) (a : A),
          e (b ⊗ₜ[A] Ideal.Quotient.mk _ a) = a •
            adicTransition J A (finiteSystemUnder J A I) m (min m n)
              (Nat.min_le_left m n) U b) := by
  letI : ∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U) := finiteSystemModule J A I
  have htower : ∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U) := by
    intro n U
    apply IsScalarTower.of_algebraMap_smul
    intro a b
    let η : (A ⧸ I ^ (n + 1)) →+* adicTerm J A (finiteSystemUnder J A I) n U :=
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (A ⧸ I ^ (n + 1))))).app U).hom
    let α : A →+* adicTerm J A (finiteSystemUnder J A I) n U :=
      ((quotient J A I n).hom.app U).hom.comp
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U).hom
    change η (Ideal.Quotient.mk _ a) * b = α a * b
    congr 1
    exact ConcreteCategory.congr_hom (congr_app
      (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) U) a
  have hflatred := finiteSystem_flat_and_reduction J A I htower
  refine ⟨htower, hflatred.1, ?_, hflatred.2⟩
  · intro n U
    change Function.Surjective (((finiteSystem J A I).map
      (homOfLE (Nat.le_succ n)).op).hom.app U)
    simp only [finiteSystem, Functor.ofOpSequence_map_homOfLE_succ]
    classical
    let R₀ := CommRingCat.of (A ⧸ I ^ (n + 1))
    let R₁ := CommRingCat.of (A ⧸ I ^ (n + 2))
    let f : R₁ ⟶ R₀ :=
      CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    let e := constantCommuteCompose J (forget CommRingCat.{u})
    let s := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
    have hs : s ≫ (constantSheaf J (Type u)).map
        ((forget CommRingCat.{u}).map f) = 𝟙 _ := by
      rw [← Functor.map_comp]
      trans (constantSheaf J (Type u)).map
        (𝟙 ((forget CommRingCat.{u}).obj R₀))
      · congr 1
        ext x
        exact Function.surjInv_eq hf x
      exact (constantSheaf J (Type u)).map_id _
    let r := e.hom.app R₀ ≫ s ≫ e.inv.app R₁
    have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
        ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
      dsimp only [r]
      rw [Category.assoc, Category.assoc]
      change e.hom.app R₀ ≫ s ≫ e.inv.app R₁ ≫
        (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J
          (forget CommRingCat.{u})).map f = _
      rw [← e.inv.naturality f]
      change e.hom.app R₀ ≫ s ≫
        (constantSheaf J (Type u)).map ((forget CommRingCat.{u}).map f) ≫
        e.inv.app R₀ = _
      rw [← Category.assoc s, hs, Category.id_comp, e.hom_inv_id_app]
    intro x
    exact ⟨r.hom.app U x, congrArg (fun h ↦ h.hom.app U x) hr⟩
end CategoryTheory.ConstantCompletion
