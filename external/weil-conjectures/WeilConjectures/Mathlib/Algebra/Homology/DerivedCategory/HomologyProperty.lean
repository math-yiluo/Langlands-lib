/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Complexes with homology in a weak Serre class form a triangulated subcategory

Let `P` be a property of objects of an abelian category `A` which is closed under
isomorphisms, kernels, cokernels and extensions (a *weak Serre class*). In a five-term exact
sequence `X₀ ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄` with `X₀`, `X₁`, `X₃`, `X₄` in `P`, the middle term is an
extension of the kernel of `X₃ ⟶ X₄` by the cokernel of `X₀ ⟶ X₁`, hence lies in `P`
(`CategoryTheory.ObjectProperty.prop_of_exact_of_exact_of_exact`).

Consequently the objects of the derived category `D(A)` all of whose homology objects lie
in `P` (`DerivedCategory.homologyProperty P`) form a triangulated subcategory
(`DerivedCategory.homologyProperty_isTriangulated`): for a distinguished
triangle `K ⟶ L ⟶ M ⟶ K⟦1⟧` the long exact homology sequence
`Hⁿ⁻¹ M ⟶ Hⁿ K ⟶ Hⁿ L ⟶ Hⁿ M ⟶ Hⁿ⁺¹ K` is five-term exact.

For any `P` containing zero and closed under isomorphisms, `homologyProperty P` is stable under
the truncations `τ^{≤ n}` and `τ^{≥ n}` of the canonical t-structure
(`DerivedCategory.homologyProperty_truncLE`, `DerivedCategory.homologyProperty_truncGE`): the
homology of a truncation is that of the complex in the surviving degrees and zero elsewhere.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

/-- **The middle term of a five-term exact sequence with outer terms in a weak Serre class lies
in the class**: it is an extension of the kernel of `X₃ ⟶ X₄` by the cokernel of `X₀ ⟶ X₁`. -/
lemma ObjectProperty.prop_of_exact_of_exact_of_exact [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    {X₀ X₁ X₂ X₃ X₄ : A} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    {w₀ : f₀ ≫ f₁ = 0} {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0}
    (h₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (hX₀ : P X₀) (hX₁ : P X₁) (hX₃ : P X₃) (hX₄ : P X₄) : P X₂ := by
  -- the exact sequence `coker f₀ ⟶ X₂ ⟶ X₃`
  let S₁ : ShortComplex A := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) f₂ (by
    rw [← cancel_epi (cokernel.π f₀), cokernel.π_desc_assoc, w₁, comp_zero])
  have hS₁ : S₁.Exact := by
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := cokernel.π f₀, τ₂ := 𝟙 _, τ₃ := 𝟙 _ } : ShortComplex.mk f₁ f₂ w₁ ⟶ S₁)).mp h₁
  -- the short exact sequence `coker f₀ ⟶ X₂ ⟶ ker f₃`
  let S : ShortComplex A := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) (kernel.lift f₃ f₂ w₂) (by
    rw [← cancel_mono (kernel.ι f₃), Category.assoc, kernel.lift_ι, zero_comp]
    exact S₁.zero)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        ({ τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι f₃ } : S ⟶ S₁)).mpr hS₁
      mono_f := h₀.mono_cokernelDesc
      epi_g := h₂.epi_kernelLift }
  exact P.prop_X₂_of_shortExact hS (P.prop_cokernel f₀ hX₀ hX₁) (P.prop_kernel f₃ hX₃ hX₄)

end Abelian

end CategoryTheory

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A)

/-- The objects of the derived category all of whose homology objects satisfy `P`. -/
def homologyProperty : ObjectProperty (DerivedCategory A) :=
  fun M ↦ ∀ n : ℤ, P ((homologyFunctor A n).obj M)

variable {P}

lemma homologyProperty_iff (M : DerivedCategory A) :
    homologyProperty P M ↔ ∀ n : ℤ, P ((homologyFunctor A n).obj M) :=
  Iff.rfl


variable (P)

instance [P.IsClosedUnderIsomorphisms] : (homologyProperty P).IsClosedUnderIsomorphisms where
  of_iso e h n := P.prop_of_iso ((homologyFunctor A n).mapIso e) (h n)

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] : (homologyProperty P).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun n ↦
    P.prop_of_isZero ((homologyFunctor A n).map_isZero (isZero_zero _))⟩

instance [P.IsClosedUnderIsomorphisms] : (homologyProperty P).IsStableUnderShift ℤ where
  isStableUnderShiftBy a :=
    ⟨fun M hM n ↦ P.prop_of_iso
      (((homologyFunctor A 0).shiftIso a n (a + n) rfl).app M).symm (hM (a + n))⟩

/-- **Complexes with homology in a weak Serre class form a triangulated subcategory**: the
middle term of a distinguished triangle has homology sitting in the five-term exact sequence
`Hⁿ⁻¹ M ⟶ Hⁿ K ⟶ Hⁿ L ⟶ Hⁿ M ⟶ Hⁿ⁺¹ K`. -/
instance homologyProperty_isTriangulatedClosed₂ [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (homologyProperty P).IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := (homologyProperty P).le_isoClosure _ fun n ↦
    P.prop_of_exact_of_exact_of_exact
      ((homologyFunctor A 0).homologySequence_exact₁ T hT (n - 1) n (by lia))
      ((homologyFunctor A 0).homologySequence_exact₂ T hT n)
      ((homologyFunctor A 0).homologySequence_exact₃ T hT n (n + 1) rfl)
      (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1))

/-- Blueprint `corollary-ambient-ind-derived--1`, general form: in the derived category
of an abelian category, the complexes whose homology objects lie in a class containing zero,
closed under isomorphisms, kernels, cokernels and extensions form a triangulated
subcategory. -/
instance homologyProperty_isTriangulated [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (homologyProperty P).IsTriangulated where

variable {P}

/-- The truncation `τ^{≤ n} M` of an object whose homology objects satisfy `P` has homology
objects satisfying `P`: they are those of `M` in degrees `≤ n`, and zero above. -/
lemma homologyProperty_truncLE [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {M : DerivedCategory A} (hM : homologyProperty P M) (n : ℤ) :
    homologyProperty P ((TStructure.t.truncLE n).obj M) := by
  intro m
  by_cases hm : m ≤ n
  · have : ((TStructure.t.triangleLEGT n).obj M).obj₃.IsGE (n + 1) :=
      (inferInstance : TStructure.t.IsGE ((TStructure.t.truncGT n).obj M) (n + 1))
    have := isIso_homologyMap_mor₁ _ (TStructure.t.triangleLEGT_distinguished n M) (m - 1) m
      (by lia) (isZero_of_isGE _ (n + 1) _ (by lia)) (isZero_of_isGE _ (n + 1) _ (by lia))
    exact P.prop_of_iso (asIso ((homologyFunctor A m).map
      ((TStructure.t.triangleLEGT n).obj M).mor₁)).symm (hM m)
  · exact P.prop_of_isZero (isZero_of_isLE _ n _ (by lia))

/-- The truncation `τ^{≥ n} M` of an object whose homology objects satisfy `P` has homology
objects satisfying `P`: they are those of `M` in degrees `≥ n`, and zero below. -/
lemma homologyProperty_truncGE [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {M : DerivedCategory A} (hM : homologyProperty P M) (n : ℤ) :
    homologyProperty P ((TStructure.t.truncGE n).obj M) := by
  intro m
  by_cases hm : n ≤ m
  · have := isIso_homologyMap_mor₂ _ (TStructure.t.triangleLTGE_distinguished n M) m (m + 1)
      rfl (isZero_of_isLE _ (n - 1) _ (by lia)) (isZero_of_isLE _ (n - 1) _ (by lia))
    exact P.prop_of_iso (asIso ((homologyFunctor A m).map
      ((TStructure.t.triangleLTGE n).obj M).mor₂)) (hM m)
  · exact P.prop_of_isZero (isZero_of_isGE _ n _ (by lia))

end DerivedCategory
