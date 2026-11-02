import Langlands.CommutativeAlgebra.FiniteFreeReversedDual
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Reversed duals of contractible and acyclic complexes -/

universe u

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
/-- A contracting homotopy transposes to a contracting homotopy on the reversed dual. -/
def reversedDualContraction (g : ℤ) (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : Homotopy (𝟙 C) 0) :
    Homotopy (𝟙 (reversedDual g C)) 0 where
  hom i j := ModuleCat.ofHom (h.hom (g - j) (g - i)).hom.dualMap
  zero i j hij := by
    have hji : ¬ (ComplexShape.up ℤ).Rel (g - i) (g - j) := by
      simp only [ComplexShape.up_Rel] at hij ⊢
      omega
    rw [h.zero _ _ hji]
    ext f x
    change f (0 : C.X (g - i)) = 0
    exact map_zero f
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    have hc := h.comm (g - i)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (g - i) (g - i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (g - i - 1) (g - i) by simp)] at hc
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change Module.Dual R (C.X (g - i)) at f
    change @Eq (Module.Dual R (C.X (g - i))) f _
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun z => z.hom x) hc
    change x = (h.hom (g - i + 1) (g - i)).hom
      ((C.d (g - i) (g - i + 1)).hom x) +
      (C.d (g - i - 1) (g - i)).hom
        ((h.hom (g - i) (g - i - 1)).hom x) + 0 at hx
    have hi₁ : g - (i + 1) = g - i - 1 := by omega
    have hi₂ : g - (i - 1) = g - i + 1 := by omega
    change f x = f ((C.d (g - (i + 1)) (g - i)).hom
      ((h.hom (g - i) (g - (i + 1))).hom x)) +
      f ((h.hom (g - (i - 1)) (g - i)).hom
        ((C.d (g - i) (g - (i - 1))).hom x)) + 0
    rw [hi₁, hi₂]
    simpa only [map_add, map_zero, add_zero, add_comm] using congrArg f hx

/-- The homology of a contractible reversed dual vanishes. -/
theorem isZero_homology_reversedDual_of_contraction (g : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (h : Homotopy (𝟙 C) 0) (i : ℤ) :
    IsZero ((reversedDual g C).homology i) := by
  apply (IsZero.iff_id_eq_zero _).2
  simpa using (reversedDualContraction g C h).homologyMap_eq i

/-- A bounded above acyclic complex of projectives has acyclic reversed dual. -/
theorem isZero_homology_reversedDual_of_acyclic (g b : ℤ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.IsStrictlyLE b)
    (hproj : ∀ i, Module.Projective R (C.X i)) (hacyclic : C.Acyclic) (i : ℤ) :
    IsZero ((reversedDual g C).homology i) := by
  have := hC
  have (j : ℤ) : Projective (C.X j) := by
    have := hproj j
    infer_instance
  have := CochainComplex.isKProjective_of_projective C b
  exact isZero_homology_reversedDual_of_contraction g C
    (CochainComplex.IsKProjective.homotopyZero (𝟙 C) hacyclic) i

end Langlands.CommutativeAlgebra
