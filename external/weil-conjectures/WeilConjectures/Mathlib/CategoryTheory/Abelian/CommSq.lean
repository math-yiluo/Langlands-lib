/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Recognizing pushout squares in an abelian category

Consider a commutative square in an abelian category
```
    t
 X₁ ⟶ X₂
l|    |r
 v    v
 X₃ ⟶ X₄
    b
```
`Mathlib/CategoryTheory/Abelian/CommSq.lean` deduces exactness properties from the assumption
that the square is a pushout square. Here we prove the converse implication, and record the
isomorphism of the cokernels of two parallel legs of a pushout square.

## Main results

* `CategoryTheory.CommSq.isPushout_of_shortExact`: a commutative square whose associated short
  complex `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄` is a short exact sequence is a pushout square.
* `CategoryTheory.IsPullback.isPushout_of_epi`: a pullback square such that
  `X₂ ⊞ X₃ ⟶ X₄` is an epimorphism is a pushout square.
* `CategoryTheory.IsPushout.cokernelIso`: in a pushout square, the induced morphism
  `cokernel l ⟶ cokernel r` between the cokernels of the two parallel legs is an isomorphism.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- The automorphism of a binary biproduct which is the identity on the first summand and
minus the identity on the second summand. -/
@[simps]
noncomputable def biprodNegSnd (X Y : C) : X ⊞ Y ≅ X ⊞ Y where
  hom := biprod.lift biprod.fst (-biprod.snd)
  inv := biprod.lift biprod.fst (-biprod.snd)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- The two short complexes `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄` attached to a commutative square (they only
differ by signs) are isomorphic. -/
noncomputable def CommSq.shortComplexIsoShortComplex' (sq : CommSq t l r b) :
    sq.shortComplex ≅ sq.shortComplex' :=
  ShortComplex.isoMk (Iso.refl _) (biprodNegSnd _ _) (Iso.refl _) (by apply biprod.hom_ext <;> simp)
    (by apply biprod.hom_ext' <;> simp)

lemma CommSq.isPushout_of_shortExact (sq : CommSq t l r b)
    (h : sq.shortComplex.ShortExact) : IsPushout t l r b :=
  IsPushout.of_isColimit' sq (sq.isColimitEquivIsColimitCokernelCofork.symm h.gIsCokernel)

lemma IsPullback.isPushout_of_epi (h : IsPullback t l r b) (he : Epi (biprod.desc r b)) :
    IsPushout t l r b := by
  have he' : Epi (biprod.desc r (-b)) := by
    have : (biprodNegSnd X₂ X₃).hom ≫ biprod.desc r (-b) = biprod.desc r b := by ext <;> simp
    exact epi_of_epi_fac this
  have hm : Mono (biprod.lift t (-l)) := by
    have h₁ : Mono (biprod.lift t l) := by
      simpa only [CommSq.shortComplex'_f] using h.mono_shortComplex'_f
    have e : biprod.lift t l ≫ (biprodNegSnd X₂ X₃).hom = biprod.lift t (-l) := by ext <;> simp
    rw [← e]
    exact mono_comp _ _
  refine h.toCommSq.isPushout_of_shortExact
    { exact := ShortComplex.exact_of_iso h.toCommSq.shortComplexIsoShortComplex'.symm
        h.exact_shortComplex'
      mono_f := hm
      epi_g := he }

namespace IsPushout

variable (sq : IsPushout t l r b)

/-- In a pushout square in an abelian category, the two parallel legs `l : X₁ ⟶ X₃` and
`r : X₂ ⟶ X₄` have isomorphic cokernels. -/
noncomputable def cokernelIso : cokernel l ≅ cokernel r where
  hom := cokernel.map l r t b sq.w.symm
  inv := cokernel.desc r (sq.desc 0 (cokernel.π l) (by simp)) (by simp)
  hom_inv_id := by
    rw [← cancel_epi (cokernel.π l)]
    simp
  inv_hom_id := by
    rw [← cancel_epi (cokernel.π r)]
    simp only [cokernel.π_desc_assoc, comp_id]
    exact sq.hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
lemma π_cokernelIso_hom :
    cokernel.π l ≫ sq.cokernelIso.hom = b ≫ cokernel.π r := by
  simp [cokernelIso]

end IsPushout

end CategoryTheory
