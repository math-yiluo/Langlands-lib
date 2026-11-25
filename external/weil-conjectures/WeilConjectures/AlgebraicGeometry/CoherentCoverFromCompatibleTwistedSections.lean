/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # A coherent source for compatible twisted sections

Source: Stacks Project, proof of Lemma 0885 (lemma-existence-projective).
(blueprint: lem-weil-pbc-coherent-cover-compatible-twisted-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Compatible sections of an invertibly twisted inverse system, finitely generating
at level zero, give compatible maps from a coherent module, epi at level zero.
This concerns ordinary module maps only, without adic quotients or completion.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0885
(lemma-existence-projective), the displayed maps from the finite negative twist sum.
(blueprint: lem-weil-pbc-coherent-cover-compatible-twisted-sections).

Proof: Let Q be the dual of P. The inverse of tensoring by P is tensoring by Q.
Take G to be the free module on the finite generating index set tensored with Q.
It is finitely presented and quasi-coherent, hence coherent on the Noetherian
scheme. At level n the given sections define a free-module map to F_n tensor P.
Apply the inverse tensor equivalence and then its unit inverse to obtain g_n.
The naturality of the tensor equivalence and the free-module/sections bijection
make the g_n commute with each transition. At level zero the free-module map is
exactly the evaluation epimorphism of the specified generating family. The inverse
equivalence preserves epimorphisms, and composing with the unit isomorphism preserves
this property, so g_0 is epi. This also works for an empty finite generating family.
-/
theorem coherent_cover_from_compatible_twisted_sections
    {X : Scheme.{u}} [IsNoetherian X] (F : ℕᵒᵖ ⥤ X.Modules)
    (P : X.Modules) [P.IsInvertible]
    (σ : (Scheme.Modules.tensorObj (F.obj (op 0)) P).GeneratingSections)
    (hσ : σ.IsFiniteType)
    (s : ∀ n : ℕ, σ.I → (Scheme.Modules.tensorObj (F.obj (op n)) P).sections)
    (hzero : s 0 = σ.s)
    (hsucc : ∀ (n : ℕ) (i : σ.I), SheafOfModules.sectionsMap
      ((tensorRight P).map (F.map (homOfLE (Nat.le_succ n)).op)) (s (n + 1) i) = s n i) :
    ∃ G : CoherentModules X, ∃ g : ∀ n : ℕ, G.obj ⟶ F.obj (op n),
      (∀ n : ℕ, g (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = g n) ∧
        Epi (g 0) := by
  classical
  have : Finite σ.I := hσ.finite
  let A : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) σ.I
  have hA : A.IsFinitePresentation := by
    let q := SheafOfModules.presentationOfIsCokernelFree
      (0 : SheafOfModules.free (R := X.ringCatSheaf) (PEmpty.{u + 1}) ⟶ A)
      (𝟙 A) (by simp) (CokernelCofork.IsColimit.ofId _ rfl)
    have : q.IsFinite := ⟨⟨inferInstanceAs (Finite σ.I)⟩,
      ⟨inferInstanceAs (Finite (PEmpty.{u + 1}))⟩⟩
    exact q.isFinitePresentation
  let e := BraidedCategory.tensorRightEquivalence P (Scheme.Modules.dual P)
    (Scheme.Modules.nonempty_tensorObj_dual_iso_unit P).some
  have hG : (e.inverse.obj A).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorObj A (Scheme.Modules.dual P)
  let G : CoherentModules X := ⟨e.inverse.obj A,
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
      ⟨inferInstance, inferInstance⟩⟩
  let f (n : ℕ) : A ⟶ e.functor.obj (F.obj (op n)) :=
    (e.functor.obj (F.obj (op n))).freeHomEquiv.symm (s n)
  have hf (n : ℕ) : f (n + 1) ≫ e.functor.map
      (F.map (homOfLE (Nat.le_succ n)).op) = f n := by
    rw [SheafOfModules.freeHomEquiv_symm_comp]
    apply congrArg ((e.functor.obj (F.obj (op n))).freeHomEquiv.symm)
    funext i
    exact hsucc n i
  let g (n : ℕ) : G.obj ⟶ F.obj (op n) :=
    e.inverse.map (f n) ≫ e.unitIso.inv.app (F.obj (op n))
  refine ⟨G, g, ?_, ?_⟩
  · intro n
    dsimp only [g]
    have hn := e.unitIso.inv.naturality (F.map (homOfLE (Nat.le_succ n)).op)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← e.inverse.map_comp, hf]
  · have hfzero : f 0 = σ.π := by simp only [f, hzero]; rfl
    have : Epi (f 0) := hfzero.symm ▸ σ.epi
    dsimp only [g]
    infer_instance

end AlgebraicGeometry
