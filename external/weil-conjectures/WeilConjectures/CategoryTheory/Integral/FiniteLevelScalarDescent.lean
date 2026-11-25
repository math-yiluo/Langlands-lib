/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Descent of a module action through a coefficient cokernel

Source: blueprint integral finite-level dual classicality, scalar reduction step;
the coefficient quotient step of the integral dual argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

/-- A module action descends through a ring quotient when the kernel acts by zero.

Source: the finite scalar reduction in the integral
finite-level dual argument (blueprint: lem-sfb-finite-level-scalar-descent).

Proof: tensor the coefficient cokernel with the underlying module. Right exactness
makes this a cokernel again, so the action factors uniquely through the quotient.
The unit equation follows by precomposing with the original ring unit. For the
associativity equation, precompose with the epimorphism induced by two quotient
maps and use associativity of the original action. The resulting module has the
same underlying object and restricts to the original module by the identity.
-/
theorem exists_quotient_module
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    {R S : C} [MonObj R] [MonObj S]
    (q : R ⟶ S) [IsMonHom q] [Epi q]
    (f : R ⟶ R) (w : f ≫ q = 0)
    (h : (ShortComplex.mk f q w).Exact)
    (M : Mod C R) (hk : f ▷ M.X ≫ γ[R,M.X] = 0) :
    ∃ N : Mod C S, Nonempty ((Mod.comap q).obj N ≅ M) := by
  let T := (ShortComplex.mk f q w).map (tensorRight M.X)
  have : Epi T.g := (tensorRight M.X).map_epi q
  have hT : T.Exact := h.map_of_epi_of_preservesCokernel _ inferInstance inferInstance
  let a : S ⊗ M.X ⟶ M.X := hT.desc γ[R,M.X] hk
  have ha : q ▷ M.X ≫ a = γ[R,M.X] := hT.g_desc _ hk
  let ma : ModObj S M.X := ModObj.mk' S a (by
    rw [← IsMonHom.one_hom q, comp_whiskerRight, Category.assoc, ha]
    exact ModObj.one_smul_self R M.X) (by
    have hq : Epi (q ⊗ₘ q) := by
      have : Epi (q ▷ R) := (tensorRight R).map_epi q
      have : Epi (S ◁ q) := (tensorLeft S).map_epi q
      rw [MonoidalCategory.tensorHom_def q q]
      infer_instance
    have : Epi ((q ⊗ₘ q) ▷ M.X) :=
      inferInstanceAs (Epi ((tensorRight M.X).map (q ⊗ₘ q)))
    apply (cancel_epi ((q ⊗ₘ q) ▷ M.X)).1
    rw [← comp_whiskerRight_assoc, ← IsMonHom.mul_hom,
      comp_whiskerRight_assoc, ha]
    rw [MonoidalCategory.tensorHom_def q q, comp_whiskerRight_assoc,
      associator_naturality_middle_assoc, associator_naturality_left_assoc,
      ← whiskerLeft_comp_assoc, ha, ← whisker_exchange_assoc, ha]
    exact ModObj.mul_smul_self R M.X)
  let N : Mod C S := { X := M.X, mod := ma }
  refine ⟨N, ⟨Mod.isoMk (Iso.refl _) ?_⟩⟩
  change (q ▷ M.X ≫ a) ≫ 𝟙 M.X = R ◁ 𝟙 M.X ≫ γ[R,M.X]
  simpa only [Category.comp_id, whiskerLeft_id, Category.id_comp] using ha

end CategoryTheory.Mod
