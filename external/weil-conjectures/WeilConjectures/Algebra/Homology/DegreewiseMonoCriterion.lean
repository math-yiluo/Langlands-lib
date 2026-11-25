/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # Degreewise criteria for monomorphisms and epimorphisms

Auxiliary lemmas for checking that a comparison map out of a cokernel is a monomorphism in
each degree, and for working with coproducts and cokernels of cochain complexes degreewise.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `q : L ⟶ G` be a cokernel of `j : L' ⟶ L` and let `α : U ⟶ G` satisfy
`u ≫ α = e ≫ q` with `u` epi. If some `ρ : T ⟶ Z` defined on an object containing `L`
via `ι` kills `L'` and restricts along `e` to `u ≫ m` with `m` mono, then `α` is mono.
```
            u           m
       S ───────▶ U ───────▶ Z
       │          │          ▲
     e │          │ α        │ ρ
   j   ▼    q     ▼    ι     │
L' ──▶ L ───────▶ G     L ──▶ T
```
-/
theorem mono_of_comp_eq {S U L L' G T Z : C} (u : S ⟶ U) [Epi u] (e : S ⟶ L) (j : L' ⟶ L)
    (q : L ⟶ G) (w : j ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q w)) (α : U ⟶ G)
    (hα : u ≫ α = e ≫ q) (ι : L ⟶ T) (ρ : T ⟶ Z) (m : U ⟶ Z) [Mono m]
    (h₁ : e ≫ ι ≫ ρ = u ≫ m) (h₂ : j ≫ ι ≫ ρ = 0) : Mono α := by
  obtain ⟨β, hβ : q ≫ β = ι ≫ ρ⟩ := CokernelCofork.IsColimit.desc' hq (ι ≫ ρ) h₂
  have hαβ : α ≫ β = m := by
    rw [← cancel_epi u, ← Category.assoc, hα, Category.assoc, hβ, h₁]
  exact mono_of_mono_fac hαβ

/-- A morphism through the image subobject of `Φ` that recovers `Φ` is an epimorphism. -/
theorem epi_of_comp_arrow_eq {X Y : C} {Φ : X ⟶ Y} {S : Subobject Y}
    (hS : S = imageSubobject Φ) (d : X ⟶ (S : C)) (hd : d ≫ S.arrow = Φ) : Epi d := by
  subst hS
  obtain rfl : d = factorThruImageSubobject Φ := by
    rw [← cancel_mono (imageSubobject Φ).arrow, hd, imageSubobject_arrow_comp]
  infer_instance

end CategoryTheory.Abelian

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Morphisms out of a degree of a coproduct of complexes agree if they agree on the
summand inclusions. -/
theorem sigma_X_hom_ext {ι : Type*} [HasColimitsOfShape (Discrete ι) C]
    {X : ι → CochainComplex C ℤ} {n : ℤ} {Z : C} {f g : (∐ X).X n ⟶ Z}
    (h : ∀ p, (Sigma.ι X p).f n ≫ f = (Sigma.ι X p).f n ≫ g) : f = g := by
  refine (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
    (colimit.isColimit (Discrete.functor X))).hom_ext fun ⟨p⟩ => ?_
  exact h p

/-- The cokernel of a morphism of complexes is computed degreewise. -/
def isColimitCokernelCoforkF {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := φ.f n) ((cokernel.π φ).f n)
      (by rw [← comp_f, cokernel.condition, zero_f])) :=
  isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
    (cokernel.condition φ) (cokernelIsCokernel φ)

end HomologicalComplex
