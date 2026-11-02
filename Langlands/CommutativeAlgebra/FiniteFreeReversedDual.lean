import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Reversed duals of finite free cochain complexes -/

universe u

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]

/-- The cochain complex with degree-`i` term `Hom_R(C^(g-i),R)`.
Its differential is the transpose of the corresponding differential of `C`. -/
def reversedDual (g : ℤ) (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (Module.Dual R (C.X (g - i)))
  d i j := ModuleCat.ofHom (C.d (g - j) (g - i)).hom.dualMap
  shape i j hij := by
    have hji : ¬ (ComplexShape.up ℤ).Rel (g - j) (g - i) := by
      simp only [ComplexShape.up_Rel] at hij ⊢
      omega
    rw [C.shape _ _ hji]
    ext f x
    simp
  d_comp_d' i j k _ _ := by
    ext f x
    change f ((C.d (g - j) (g - i)).hom ((C.d (g - k) (g - j)).hom x)) = 0
    have h := congrArg (fun z => z.hom x) (C.d_comp_d (g - k) (g - j) (g - i))
    change (C.d (g - j) (g - i)).hom ((C.d (g - k) (g - j)).hom x) = 0 at h
    rw [h, map_zero]

@[simp] theorem reversedDual_X (g : ℤ) (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (reversedDual g C).X i = ModuleCat.of R (Module.Dual R (C.X (g - i))) := rfl

@[simp] theorem reversedDual_d_apply (g : ℤ) (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j : ℤ) (f : Module.Dual R (C.X (g - i))) (x : C.X (g - j)) :
    (show Module.Dual R (C.X (g - j)) from ((reversedDual g C).d i j).hom f) x =
      f ((C.d (g - j) (g - i)).hom x) := rfl

/-- Reversing duality takes an upper term bound to the complementary lower bound. -/
theorem reversedDual_isStrictlyGE (g b : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (h : C.IsStrictlyLE b) :
    (reversedDual g C).IsStrictlyGE (g - b) := by
  have := h
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro i hi
  have := ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyLE b (g - i) (by omega))
  change IsZero (ModuleCat.of R (Module.Dual R (C.X (g - i))))
  exact ModuleCat.isZero_of_subsingleton _

/-- Reversing duality takes a lower term bound to the complementary upper bound. -/
theorem reversedDual_isStrictlyLE (g a : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (h : C.IsStrictlyGE a) :
    (reversedDual g C).IsStrictlyLE (g - a) := by
  have := h
  apply (CochainComplex.isStrictlyLE_iff _ _).2
  intro i hi
  have := ModuleCat.subsingleton_of_isZero (C.isZero_of_isStrictlyGE a (g - i) (by omega))
  change IsZero (ModuleCat.of R (Module.Dual R (C.X (g - i))))
  exact ModuleCat.isZero_of_subsingleton _

/-- The reversed dual of a bounded finite free complex is bounded finite free. -/
theorem isFiniteFree_reversedDual (g : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (h : IsFiniteFree C) :
    IsFiniteFree (reversedDual g C) := by
  obtain ⟨⟨a, b, ha, hb⟩, hterms⟩ := h
  refine ⟨⟨g - b, g - a, reversedDual_isStrictlyGE g b C hb,
    reversedDual_isStrictlyLE g a C ha⟩, fun i ↦ ?_⟩
  obtain ⟨_, _⟩ := hterms (g - i)
  change Module.Finite R (Module.Dual R (C.X (g - i))) ∧
    Module.Free R (Module.Dual R (C.X (g - i)))
  exact ⟨inferInstance, inferInstance⟩

/-- Evaluation identifies a finite free complex with its twice reversed dual. -/
def reversedDualBidualIso (g : ℤ) (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ∀ i, Module.Finite R (C.X i) ∧ Module.Free R (C.X i)) :
    C ≅ reversedDual g (reversedDual g C) := by
  let e (i : ℤ) : C.X i ≅ (reversedDual g (reversedDual g C)).X i := by
    have := (h (g - (g - i))).1
    have := (h (g - (g - i))).2
    exact (C.XIsoOfEq (by omega : g - (g - i) = i)).symm ≪≫
      (Module.evalEquiv R (C.X (g - (g - i)))).toModuleIso
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Module.Dual.eval R (C.X (g - (g - i)))
    ((C.XIsoOfEq (by omega : g - (g - i) = i)).inv.hom x)).comp
      (C.d (g - (g - i)) (g - (g - j))).hom.dualMap =
    Module.Dual.eval R (C.X (g - (g - j)))
      ((C.XIsoOfEq (by omega : g - (g - j) = j)).inv.hom ((C.d i j).hom x))
  ext f
  change f ((C.d (g - (g - i)) (g - (g - j))).hom
    ((C.XIsoOfEq (by omega : g - (g - i) = i)).inv.hom x)) =
      f ((C.XIsoOfEq (by omega : g - (g - j) = j)).inv.hom ((C.d i j).hom x))
  apply congrArg f
  have hd :
      (C.XIsoOfEq (by omega : g - (g - i) = i)).inv ≫
        C.d (g - (g - i)) (g - (g - j)) =
      C.d i j ≫ (C.XIsoOfEq (by omega : g - (g - j) = j)).inv := by simp
  exact congrArg (fun z => z.hom x) hd

end Langlands.CommutativeAlgebra
