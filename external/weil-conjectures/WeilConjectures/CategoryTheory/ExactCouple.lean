/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact

import WeilConjectures.CategoryTheory.DerivedCoupleMapExactness

/-!
# Bigraded exact couples and their spectral sequences

Source: Stacks Project, Homological Algebra, Definitions 12.21.1 and 12.21.3,
Lemma 12.21.2 and Remark 12.21.5 (Tags 011Q, 011S, 011R, 0AMJ), in the
bigraded convention of the blueprint (blueprint: def-sp-exact-couple).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

/-- A type-`s` exact couple. The image and kernel equalities compare subobjects
of the same bidegree. Type zero is the initial couple of the blueprint.
Source: Stacks Project, Tags 011Q and 0AMJ (blueprint: def-sp-exact-couple). -/
structure BigradedExactCouple (C : Type u) [Category.{v} C] [Abelian C] (s : ℕ) where
  D : ℤ → ℤ → C
  E : ℤ → ℤ → C
  alpha : ∀ p q, D p q ⟶ D (p - 1) (q + 1)
  f : ∀ p q, E p q ⟶ D (p + 2) (q - 1)
  g : ∀ p q, D p q ⟶ E (p + s) (q - s)
  alpha_f_zero : ∀ p q, f p q ≫ alpha (p + 2) (q - 1) = 0
  f_g_zero : ∀ p q, g p q ≫ f (p + s) (q - s) = 0
  g_alpha_zero : ∀ p q, alpha p q ≫ g (p - 1) (q + 1) = 0
  exact_alpha : ∀ p q,
    imageSubobject (f p q) = kernelSubobject (alpha (p + 2) (q - 1))
  exact_f : ∀ p q,
    imageSubobject (g p q) = kernelSubobject (f (p + s) (q - s))
  exact_g : ∀ p q,
    imageSubobject (alpha p q) = kernelSubobject (g (p - 1) (q + 1))

namespace BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

/-- The differential has bidegree `(s+2,-s-1)`.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
def d (X : BigradedExactCouple C s) (p q : ℤ) :
    X.E p q ⟶ X.E (p + 2 + s) (q - 1 - s) :=
  X.f p q ≫ X.g (p + 2) (q - 1)

/-- The consecutive differentials compose to zero, since `f ≫ g ≫ f = 0`.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
theorem d_comp_d (X : BigradedExactCouple C s) (p q : ℤ) :
    X.d p q ≫ X.d (p + 2 + s) (q - 1 - s) = 0 := by
  simp only [d, Category.assoc, ← Category.assoc (X.g (p + 2) (q - 1)),
    X.f_g_zero, zero_comp, comp_zero]

/-- The image of `g` lies in the cycles, since `g ≫ f = 0`.
Source: Stacks Project, Tag 0AMJ (blueprint: def-sp-exact-couple). -/
theorem g_comp_d (X : BigradedExactCouple C s) (p q : ℤ) :
    X.g p q ≫ X.d (p + s) (q - s) = 0 := by
  simp only [d, ← Category.assoc, X.f_g_zero, zero_comp]

/-- The derived `D`-term is the image of the incoming `alpha`.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
noncomputable def derivedD (X : BigradedExactCouple C s) (p q : ℤ) : C :=
  image (X.alpha (p + 1) (q - 1))

/-- The incoming differential transported to its prescribed target bidegree.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
def dInto (X : BigradedExactCouple C s) (p q : ℤ) :
    X.E (p - s - 2) (q + s + 1) ⟶ X.E p q :=
  X.d (p - s - 2) (q + s + 1) ≫ eqToHom (by
    congr 1 <;> omega)

/-- The incoming differential lands in the kernel of the outgoing one: after
rewriting the indices, `dInto p q ≫ d p q` is `d ≫ d` at `(p - s - 2, q + s + 1)`,
which vanishes by `d_comp_d`.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
theorem dInto_comp_d (X : BigradedExactCouple C s) (p q : ℤ) :
    X.dInto p q ≫ X.d p q = 0 := by
  have transport (a b p' q' : ℤ) (hp : a + 2 + s = p') (hq : b - 1 - s = q') :
      (X.d a b ≫ eqToHom (congrArg₂ X.E hp hq)) ≫ X.d p' q' = 0 := by
    subst p'
    subst q'
    simpa using X.d_comp_d a b
  exact transport (p - s - 2) (q + s + 1) p q (by omega) (by omega)

/-- The derived `E`-term is cycles modulo boundaries, represented by the
cokernel of the incoming differential lifted into the kernel of the outgoing one.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
noncomputable def derivedE (X : BigradedExactCouple C s) (p q : ℤ) : C :=
  cokernel (kernel.lift (X.d p q) (X.dInto p q) (X.dInto_comp_d p q))

/-- Inclusion of a derived `D`-term into the original `D`-term.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
noncomputable def derivedDInclusion (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derivedD p q ⟶ X.D p q :=
  image.ι (X.alpha (p + 1) (q - 1)) ≫ eqToHom (by congr 1 <;> omega)

/-- Projection from cycles onto the derived `E`-term.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
noncomputable def derivedEProjection (X : BigradedExactCouple C s) (p q : ℤ) :
    kernel (X.d p q) ⟶ X.derivedE p q :=
  cokernel.π (kernel.lift (X.d p q) (X.dInto p q) (X.dInto_comp_d p q))

/-- The map `g` factors through cycles.
Source: Stacks Project, Tag 0AMJ (blueprint: def-sp-exact-couple). -/
noncomputable def gToCycles (X : BigradedExactCouple C s) (p q : ℤ) :
    X.D p q ⟶ kernel (X.d (p + s) (q - s)) :=
  kernel.lift (X.d (p + s) (q - s)) (X.g p q) (X.g_comp_d p q)

/-- The maps of the derived couple are the restrictions and induced maps
described by Stacks. The three equalities state exactness at each term.
Source: Stacks Project, Tags 011R and 0AMJ (blueprint: def-sp-exact-couple). -/
structure DerivedMaps (X : BigradedExactCouple C s) where
  alpha : ∀ p q, X.derivedD p q ⟶ X.derivedD (p - 1) (q + 1)
  f : ∀ p q, X.derivedE p q ⟶ X.derivedD (p + 2) (q - 1)
  g : ∀ p q, X.derivedD p q ⟶ X.derivedE (p + (s + 1)) (q - (s + 1))
  alpha_f_zero : ∀ p q, f p q ≫ alpha (p + 2) (q - 1) = 0
  f_g_zero : ∀ p q, g p q ≫ f (p + (s + 1)) (q - (s + 1)) = 0
  g_alpha_zero : ∀ p q, alpha p q ≫ g (p - 1) (q + 1) = 0
  exact_alpha : ∀ p q,
    imageSubobject (f p q) = kernelSubobject (alpha (p + 2) (q - 1))
  exact_f : ∀ p q,
    imageSubobject (g p q) = kernelSubobject (f (p + (s + 1)) (q - (s + 1)))
  exact_g : ∀ p q,
    imageSubobject (alpha p q) = kernelSubobject (g (p - 1) (q + 1))
  alpha_comm : ∀ p q,
    alpha p q ≫ X.derivedDInclusion (p - 1) (q + 1) =
      X.derivedDInclusion p q ≫ X.alpha p q
  f_comm : ∀ p q,
    X.derivedEProjection p q ≫ f p q ≫ X.derivedDInclusion (p + 2) (q - 1) =
      kernel.ι (X.d p q) ≫ X.f p q
  g_comm : ∀ p q,
    factorThruImage (X.alpha (p + 1) (q - 1)) ≫ g p q =
      X.gToCycles (p + 1) (q - 1) ≫
        X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
        eqToHom (by congr 1 <;> omega)

/-- The induced maps exist, are well-defined, and give an exact couple of
type `s+1`. The restriction equations uniquely determine them: `alpha'`
commutes with the image inclusions, `f'` agrees with `f` on cycles, and `g'`
agrees with `g` after choosing a preimage under `alpha`.

Indeed, `f(ker d)` lies in `ker g = im alpha`, and `f(im d) = 0` because
`f ≫ g = 0`. Also `d(g(y)) = 0`, while changing a lift of an image element
by `ker alpha = im f` changes its `g`-image by a `d`-boundary. These
observations construct the three maps. The exactness of the derived triangle
then follows by the element chases of Stacks Lemma 12.21.2.
Source: Stacks Project, Tags 011R and 0AMJ (blueprint: def-sp-exact-couple). -/
theorem derivedMaps_exists (X : BigradedExactCouple C s) : Nonempty (DerivedMaps X) := by
  have hβ : ∀ p q, X.dInto p q ≫ X.f p q ≫ X.g (p + 2) (q - 1) = 0 :=
    X.dInto_comp_d
  have hβeq : ∀ p q, X.dInto p q =
      (X.f (p - s - 2) (q + s + 1) ≫
        X.g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
          eqToHom (by congr 1 <;> omega) := fun _ _ ↦ rfl
  let M := Classical.choice (derivedCoupleMapData_exists X.D X.E X.alpha X.f X.g
    X.dInto hβ X.f_g_zero X.exact_alpha X.exact_g hβeq)
  obtain ⟨hα, hf, hg⟩ := derivedCoupleMapData_exact X.D X.E X.alpha X.f X.g
    X.dInto hβ X.f_g_zero X.alpha_f_zero X.g_alpha_zero
    X.exact_alpha X.exact_f X.exact_g hβeq M
  refine ⟨{ alpha := M.alpha
            f := M.forward
            g := M.backward
            alpha_f_zero := ?_
            f_g_zero := ?_
            g_alpha_zero := ?_
            exact_alpha := hα
            exact_f := hf
            exact_g := hg
            alpha_comm := by
              simpa only [derivedDInclusion, Category.assoc] using M.alpha_comm
            f_comm := by
              simpa only [derivedDInclusion, derivedEProjection, d, Category.assoc]
                using M.f_comm
            g_comm := M.g_comm }⟩
  · intro p q
    apply (kernelSubobject_factors_iff (M.alpha (p + 2) (q - 1)) (M.forward p q)).mp
    rw [← hα p q]
    simpa using imageSubobject_factors_comp_self (M.forward p q) (𝟙 _)
  · intro p q
    apply (kernelSubobject_factors_iff
      (M.forward (p + (s + 1)) (q - (s + 1))) (M.backward p q)).mp
    rw [← hf p q]
    simpa using imageSubobject_factors_comp_self (M.backward p q) (𝟙 _)
  · intro p q
    apply (kernelSubobject_factors_iff (M.backward (p - 1) (q + 1)) (M.alpha p q)).mp
    rw [← hg p q]
    simpa using imageSubobject_factors_comp_self (M.alpha p q) (𝟙 _)

instance (X : BigradedExactCouple C s) (p q : ℤ) : Mono (X.derivedDInclusion p q) := by
  dsimp only [derivedDInclusion]
  infer_instance

instance (X : BigradedExactCouple C s) (p q : ℤ) : Epi (X.derivedEProjection p q) := by
  dsimp only [derivedEProjection]
  infer_instance

/-- The induced maps of the derived couple are unique:`alpha'` is determined by the mono
inclusion of the derived `D`-terms, `f'` by this inclusion and the epi projection from
cycles, and `g'` by the epi `D → im alpha`.
Source: Stacks Project, Tag 011R (blueprint: def-sp-exact-couple). -/
instance (X : BigradedExactCouple C s) : Subsingleton (DerivedMaps X) where
  allEq M N := by
    have hα : M.alpha = N.alpha := by
      funext p q
      exact (cancel_mono (X.derivedDInclusion (p - 1) (q + 1))).mp
        ((M.alpha_comm p q).trans (N.alpha_comm p q).symm)
    have hf : M.f = N.f := by
      funext p q
      refine (cancel_mono (X.derivedDInclusion (p + 2) (q - 1))).mp ?_
      exact (cancel_epi (X.derivedEProjection p q)).mp
        ((M.f_comm p q).trans (N.f_comm p q).symm)
    have hg : M.g = N.g := by
      funext p q
      exact (cancel_epi (factorThruImage (X.alpha (p + 1) (q - 1)))).mp
        ((M.g_comm p q).trans (N.g_comm p q).symm)
    cases M
    cases N
    dsimp only at hα hf hg
    subst hα hf hg
    rfl

/-- The derived couple. Its data comes from the maps whose existence and
exactness are stated in `derivedMaps_exists`; they are unique by the `Subsingleton`
instance on `DerivedMaps`.
Source: Stacks Project, Tags 011R and 0AMJ (blueprint: def-sp-exact-couple). -/
noncomputable def derived (X : BigradedExactCouple C s) : BigradedExactCouple C (s + 1) :=
  let M := Classical.choice X.derivedMaps_exists
  { D := X.derivedD
    E := X.derivedE
    alpha := M.alpha
    f := M.f
    g := M.g
    alpha_f_zero := M.alpha_f_zero
    f_g_zero := M.f_g_zero
    g_alpha_zero := M.g_alpha_zero
    exact_alpha := M.exact_alpha
    exact_f := M.exact_f
    exact_g := M.exact_g }

/-- The iterated exact couples, indexed so that the initial couple is page two.
Source: Stacks Project, Tags 011S and 0AMJ (blueprint: def-sp-exact-couple). -/
noncomputable def pageCouple (X : BigradedExactCouple C 0) :
    (n : ℕ) → BigradedExactCouple C n
  | 0 => X
  | n + 1 => (pageCouple X n).derived

/-- The `E_r` term for `r ≥ 2`, with `E₂ = E`.
Source: Stacks Project, Tag 011S (blueprint: def-sp-exact-couple). -/
noncomputable def page (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) : C :=
  (X.pageCouple (r - 2)).E p q

/-- The differential on page `r` has bidegree `(r,1-r)` when `r ≥ 2`.
Source: Stacks Project, Tags 011S and 0AMJ (blueprint: def-sp-exact-couple). -/
noncomputable def pageDifferential (X : BigradedExactCouple C 0) (r : ℕ)
    (p q : ℤ) : X.page r p q ⟶
      X.page r (p + 2 + ((r - 2 : ℕ) : ℤ)) (q - 1 - ((r - 2 : ℕ) : ℤ)) :=
  (X.pageCouple (r - 2)).d p q

end BigradedExactCouple
end CategoryTheory
