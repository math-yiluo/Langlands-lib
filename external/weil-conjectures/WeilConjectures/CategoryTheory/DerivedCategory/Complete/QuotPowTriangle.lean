/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The triangles `R ⟶ R ⟶ R/ϖⁿ ⟶ R⟦1⟧`

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. This file builds the distinguished triangles
`DerivedCategory.quotPowTriangle J hϖ hI n : R ⟶ R ⟶ R/Iⁿ ⟶ R⟦1⟧` of `D(J, R)`, whose first
map is the multiplication by `ϖⁿ`, together with their transition morphisms
`DerivedCategory.quotPowTriangleMap`.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

variable {J}


section ShortExact

variable {I : Ideal R} {ϖ : R}

variable (I ϖ) in
/-- The short complex `R ⟶ R ⟶ R/Iⁿ` of `R`-modules, the first map being the multiplication
by `ϖⁿ`, when `ϖ ∈ I`. -/
noncomputable def quotPowShortComplex (hϖ : ϖ ∈ I) (n : ℕ) :
    ShortComplex (ModuleCat.{u + 1} R) :=
  ShortComplex.mk (ϖ ^ n • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) ((Ideal.quotPowCone I).π.app (op n))
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      change Submodule.Quotient.mk (ϖ ^ n • x) = 0
      rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖ n))

lemma mem_of_eq_span (hI : I = Ideal.span {ϖ}) : ϖ ∈ I := hI ▸ Ideal.mem_span_singleton_self ϖ

lemma quotPowShortComplex_shortExact (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
    (n : ℕ) : (quotPowShortComplex I ϖ (mem_of_eq_span hI) n).ShortExact := by
  subst hI
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro (y : R)
    change Submodule.Quotient.mk (p := Ideal.span {ϖ} ^ n) y = 0 ↔ ∃ x : R, ϖ ^ n • x = y
    rw [Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    simp [mul_comm, smul_eq_mul]
  · intro (x : R) (y : R) h
    change ϖ ^ n • x = ϖ ^ n • y at h
    rw [smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub] at h
    rw [← sub_eq_zero]
    exact (mem_nonZeroDivisors_iff.1 (pow_mem hϖ n)).1 _ h
  · exact Submodule.Quotient.mk_surjective _

variable (I ϖ) in
/-- The transition between the short complexes `quotPowShortComplex`: multiplication by `ϖ` on
the first term, the identity on the second, the projection `R/Iⁿ⁺¹ ⟶ R/Iⁿ` on the third. -/
noncomputable def quotPowShortComplexMap (hϖ : ϖ ∈ I) (n : ℕ) :
    quotPowShortComplex I ϖ hϖ (n + 1) ⟶ quotPowShortComplex I ϖ hϖ n where
  τ₁ := ϖ • 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := (Ideal.quotPowFunctor I).map (homOfLE n.le_succ).op
  comm₁₂ := by
    change (ϖ • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) ≫ (ϖ ^ n • 𝟙 _) =
      (ϖ ^ (n + 1) • 𝟙 (𝟙_ (ModuleCat.{u + 1} R))) ≫ 𝟙 _
    rw [comp_id, Linear.smul_comp, id_comp, smul_smul, ← pow_succ']
  comm₂₃ := by
    rw [id_comp]
    exact (Ideal.quotPowCone I).w (homOfLE n.le_succ).op

end ShortExact

section Triangles

variable (J) {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ in
/-- The short exact sequence of constant sheaves `R ⟶ R ⟶ R/Iⁿ`. -/
lemma sheafQuotPowShortComplex_shortExact (n : ℕ) :
    ((quotPowShortComplex I ϖ (mem_of_eq_span hI) n).map
      (constantSheaf J (ModuleCat.{u + 1} R))).ShortExact :=
  (quotPowShortComplex_shortExact hϖ hI n).map_of_exact _

/-- The distinguished triangle `R ⟶ R ⟶ R/Iⁿ ⟶ R⟦1⟧` in `D(J, R)`. -/
noncomputable abbrev quotPowTriangle (n : ℕ) :
    Triangle (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafQuotPowShortComplex_shortExact J hϖ hI n).singleTriangle

lemma quotPowTriangle_distinguished (n : ℕ) : quotPowTriangle J hϖ hI n ∈ distTriang _ :=
  (sheafQuotPowShortComplex_shortExact J hϖ hI n).singleTriangle_distinguished

lemma quotPowTriangle_mor₁ (n : ℕ) :
    (quotPowTriangle J hϖ hI n).mor₁ = ϖ ^ n • 𝟙 (quotPowTriangle J hϖ hI n).obj₁ := by
  change (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
    ((constantSheaf J (ModuleCat.{u + 1} R)).map (ϖ ^ n • 𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) = _
  rw [Functor.map_smul, Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The transition morphisms of triangles `quotPowTriangle (n + 1) ⟶ quotPowTriangle n`. -/
noncomputable def quotPowTriangleMap (n : ℕ) :
    quotPowTriangle J hϖ hI (n + 1) ⟶ quotPowTriangle J hϖ hI n :=
  ShortComplex.ShortExact.singleTriangle.map _ _
    ((constantSheaf J (ModuleCat.{u + 1} R)).mapShortComplex.map
      (quotPowShortComplexMap I ϖ (mem_of_eq_span hI) n))

lemma quotPowTriangleMap_hom₁ (n : ℕ) :
    (quotPowTriangleMap J hϖ hI n).hom₁ = ϖ • 𝟙 (quotPowTriangle J hϖ hI (n + 1)).obj₁ := by
  change (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
    ((constantSheaf J (ModuleCat.{u + 1} R)).map (ϖ • 𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) = _
  rw [Functor.map_smul, Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

lemma quotPowTriangleMap_hom₂ (n : ℕ) :
    (quotPowTriangleMap J hϖ hI n).hom₂ = 𝟙 (quotPowTriangle J hϖ hI (n + 1)).obj₂ := by
  change (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
    ((constantSheaf J (ModuleCat.{u + 1} R)).map (𝟙 (𝟙_ (ModuleCat.{u + 1} R)))) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

end Triangles

end DerivedCategory
