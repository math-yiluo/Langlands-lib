/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Homology of complexes of abelian groups commutes with products

Products of abelian groups are exact, so the homology of a product of complexes of abelian groups
is the product of their homologies: the functor `HomologicalComplex.homologyFunctor` preserves
products. The proof is elementwise: a family of cycles of the factors is a cycle of the product,
and a family of boundaries of the factors is a boundary of the product.

## Main statements

- `HomologicalComplex.preservesLimitsOfShape_discrete_homologyFunctor_ab`: the homology functors
  of complexes of abelian groups preserve products.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} (M : HomologicalComplex AddCommGrpCat.{u} c)

/-- An element `x` of `M.X i` with `d x = 0` comes from a cycle. -/
lemma ab_exists_iCycles_eq (i : ι) (x : M.X i) (hx : M.d i (c.next i) x = 0) :
    ∃ z : M.cycles i, M.iCycles i z = x :=
  (ShortComplex.ab_exact_iff _).1
    (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk (M.iCycles i) (M.d i (c.next i))
      (M.iCycles_d i _)) (M.cyclesIsKernel i _ rfl)) x hx

/-- A cycle has a vanishing homology class iff it is a boundary. -/
lemma ab_homologyπ_eq_zero_iff (i : ι) (z : M.cycles i) :
    M.homologyπ i z = 0 ↔ ∃ y : M.X (c.prev i), M.toCycles (c.prev i) i y = z := by
  constructor
  · intro hz
    exact (ShortComplex.ab_exact_iff _).1
      (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk (M.toCycles (c.prev i) i)
        (M.homologyπ i) (M.toCycles_comp_homologyπ _ i)) (M.homologyIsCokernel _ i rfl)) z hz
  · rintro ⟨y, rfl⟩
    rw [← ConcreteCategory.comp_apply, toCycles_comp_homologyπ]
    rfl

/-- A variant of `ab_exists_iCycles_eq` with an explicit next index. -/
lemma ab_exists_iCycles_eq' (i j : ι) (hij : c.next i = j) (x : M.X i) (hx : M.d i j x = 0) :
    ∃ z : M.cycles i, M.iCycles i z = x := by
  subst hij
  exact M.ab_exists_iCycles_eq i x hx

/-- A variant of `ab_homologyπ_eq_zero_iff` with an explicit previous index. -/
lemma ab_homologyπ_eq_zero_iff' (i j : ι) (hij : c.prev j = i) (z : M.cycles j) :
    M.homologyπ j z = 0 ↔ ∃ y : M.X i, M.toCycles i j y = z := by
  subst hij
  exact M.ab_homologyπ_eq_zero_iff j z

lemma ab_homologyπ_surjective (i : ι) : Function.Surjective (M.homologyπ i) :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

lemma ab_iCycles_injective (i : ι) : Function.Injective (M.iCycles i) :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

variable {κ : Type w} (K : κ → HomologicalComplex AddCommGrpCat.{max u w} c)

lemma ab_pi_X_ext (i : ι) {x x' : (∏ᶜ K).X i}
    (h : ∀ j, (Pi.π K j).f i x = (Pi.π K j).f i x') : x = x' := by
  have hinj : Function.Injective (piComparison (eval _ c i) K) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  refine hinj ((Concrete.productEquiv _).injective (funext fun j ↦ ?_))
  simp only [Concrete.productEquiv_apply_apply]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, piComparison_comp_π]
  exact h j

lemma ab_pi_X_exists (i : ι) (y : ∀ j, (K j).X i) :
    ∃ x : (∏ᶜ K).X i, ∀ j, (Pi.π K j).f i x = y j := by
  have hsurj : Function.Surjective (piComparison (eval _ c i) K) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hsurj ((Concrete.productEquiv _).symm y)
  refine ⟨x, fun j ↦ ?_⟩
  have := congrArg (Pi.π (fun b ↦ (eval AddCommGrpCat.{max u w} c i).obj (K b)) j) hx
  erw [Concrete.productEquiv_symm_apply_π] at this
  rw [← ConcreteCategory.comp_apply, piComparison_comp_π] at this
  exact this

lemma ab_bijective_piComparison_homologyFunctor (i : ι) :
    Function.Bijective (piComparison (homologyFunctor AddCommGrpCat.{max u w} c i) K) := by
  have hπ (j : κ) (h : (homologyFunctor AddCommGrpCat.{max u w} c i).obj (∏ᶜ K)) :
      Pi.π (fun b ↦ (homologyFunctor AddCommGrpCat.{max u w} c i).obj (K b)) j
        (piComparison (homologyFunctor AddCommGrpCat.{max u w} c i) K h) =
        homologyMap (Pi.π K j) i h := by
    rw [← ConcreteCategory.comp_apply, piComparison_comp_π]
    rfl
  have hπz (j : κ) (z : (∏ᶜ K).cycles i) :
      homologyMap (Pi.π K j) i ((∏ᶜ K).homologyπ i z) =
        (K j).homologyπ i (cyclesMap (Pi.π K j) i z) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, homologyπ_naturality]
  have hi (j : κ) (z : (∏ᶜ K).cycles i) :
      (K j).iCycles i (cyclesMap (Pi.π K j) i z) = (Pi.π K j).f i ((∏ᶜ K).iCycles i z) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, cyclesMap_i]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨z, rfl⟩ := ab_homologyπ_surjective _ i h
    have (j : κ) := (ab_homologyπ_eq_zero_iff _ i (cyclesMap (Pi.π K j) i z)).1 (by
      rw [← hπz, ← hπ, hh, map_zero])
    choose y hy using this
    obtain ⟨Y, hY⟩ := ab_pi_X_exists K (c.prev i) y
    rw [ab_homologyπ_eq_zero_iff]
    refine ⟨Y, ab_iCycles_injective _ i ?_⟩
    refine ab_pi_X_ext K i fun j ↦ ?_
    calc (Pi.π K j).f i ((∏ᶜ K).iCycles i ((∏ᶜ K).toCycles (c.prev i) i Y)) =
          (Pi.π K j).f i ((∏ᶜ K).d (c.prev i) i Y) := by
          rw [← ConcreteCategory.comp_apply ((∏ᶜ K).toCycles (c.prev i) i), toCycles_i]
      _ = (K j).d (c.prev i) i ((Pi.π K j).f (c.prev i) Y) := by
          rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Hom.comm]
      _ = (K j).iCycles i ((K j).toCycles (c.prev i) i (y j)) := by
          rw [hY, ← ConcreteCategory.comp_apply, toCycles_i]
      _ = _ := by rw [hy, hi]
  · intro w
    have (j : κ) := ab_homologyπ_surjective _ i
      (Pi.π (fun b ↦ (homologyFunctor AddCommGrpCat.{max u w} c i).obj (K b)) j w)
    choose z hz using this
    obtain ⟨X, hX⟩ := ab_pi_X_exists K i fun j ↦ (K j).iCycles i (z j)
    obtain ⟨Z, hZ⟩ := ab_exists_iCycles_eq _ i X (ab_pi_X_ext K _ fun j ↦ by
      rw [← ConcreteCategory.comp_apply, ← Hom.comm, ConcreteCategory.comp_apply, hX,
        ← ConcreteCategory.comp_apply, iCycles_d]
      simp)
    refine ⟨(∏ᶜ K).homologyπ i Z, (Concrete.productEquiv _).injective (funext fun j ↦ ?_)⟩
    simp only [Concrete.productEquiv_apply_apply]
    rw [hπ, hπz, ← hz j]
    congr 1
    apply ab_iCycles_injective
    rw [hi, hZ, hX]

instance (i : ι) :
    PreservesLimit (Discrete.functor K) (homologyFunctor AddCommGrpCat.{max u w} c i) :=
  have : IsIso (piComparison (homologyFunctor AddCommGrpCat.{max u w} c i) K) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (ab_bijective_piComparison_homologyFunctor K i)
  PreservesProduct.of_iso_comparison _ _

/-- **Homology commutes with products of complexes of abelian groups.** -/
instance preservesLimitsOfShape_discrete_homologyFunctor_ab (i : ι) :
    PreservesLimitsOfShape (Discrete κ) (homologyFunctor AddCommGrpCat.{max u w} c i) :=
  preservesLimitsOfShape_of_discrete _

end HomologicalComplex
