/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Construction of induced maps on images and cycle quotients

Source: Stacks Project, Lemma 12.21.2 (Tag 011R), Remark 12.21.5 (Tag 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

omit [Abelian C] in
private theorem transport_family {F G : ℤ → ℤ → C}
    (t : ∀ p q, F p q ⟶ G p q) {p q p' q' : ℤ} (hp : p = p') (hq : q = q') :
    eqToHom (congrArg₂ F hp hq) ≫ t p' q' =
      t p q ≫ eqToHom (congrArg₂ G hp hq) := by
  subst p'
  subst q'
  simp

/-- The restricted alpha map is an explicit composition of image maps.
Source: Stacks Project, Lemma 12.21.2, setup (4), Tag 011R
(blueprint: lem-sp-derived-map-construction). -/
noncomputable def derivedCoupleAlpha (D : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1)) (p q : ℤ) :
    image (a (p + 1) (q - 1)) ⟶ image (a ((p - 1) + 1) ((q + 1) - 1)) :=
  image.ι (a (p + 1) (q - 1)) ≫ eqToHom (by congr 1 <;> omega) ≫
    factorThruImage (a ((p - 1) + 1) ((q + 1) - 1))

/-- The explicit restricted alpha satisfies its defining equation.
Source: Stacks Project, Lemma 12.21.2, setup (4), Tag 011R
(blueprint: lem-sp-derived-map-construction). -/
theorem derivedCoupleAlpha_comm (D : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1)) (p q : ℤ) :
    derivedCoupleAlpha D a p q ≫ image.ι (a ((p - 1) + 1) ((q + 1) - 1)) ≫
      eqToHom (by congr 1 <;> omega) =
    image.ι (a (p + 1) (q - 1)) ≫ eqToHom (by congr 1 <;> omega) ≫ a p q := by
  dsimp only [derivedCoupleAlpha]
  simp only [Category.assoc, image.fac_assoc]
  have h := transport_family a
    (show (p - 1) + 1 = p by omega) (show (q + 1) - 1 = q by omega)
  rw [← h]
  simp only [← Category.assoc, eqToHom_trans]

private theorem lift_image_of_eq {A B T U : C} (a : A ⟶ B) (g : B ⟶ T)
    (h : imageSubobject a = kernelSubobject g) (u : U ⟶ B) (hu : u ≫ g = 0) :
    ∃ l : U ⟶ image a, l ≫ image.ι a = u := by
  let S := ShortComplex.mk a g ((kernelSubobject_factors_iff g a).mp (by
    rw [← h]
    simpa using imageSubobject_factors_comp_self a (𝟙 A)))
  have he : S.Exact := (S.exact_iff_image_eq_kernel).mpr h
  let l := KernelFork.IsLimit.lift' he.isLimitImage' u hu
  exact ⟨l.1, l.2⟩

/-- The forward map is obtained by restricting to cycles and descending the boundary.
Source: Stacks Project, Remark 12.21.5, Tag 0AMJ
(blueprint: lem-sp-derived-map-construction). -/
theorem derivedCoupleForward_exists (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (hgg : ∀ p q, imageSubobject (a p q) = kernelSubobject (g (p - 1) (q + 1)))
    (hβeq : ∀ p q, β p q =
      (f (p - s - 2) (q + s + 1) ≫ g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
        eqToHom (by congr 1 <;> omega)) (p q : ℤ) :
    ∃ l : cokernel (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q)) ⟶
        image (a ((p + 2) + 1) ((q - 1) - 1)),
      cokernel.π (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q)) ≫
        l ≫ image.ι (a ((p + 2) + 1) ((q - 1) - 1)) ≫
          eqToHom (by congr 1 <;> omega) =
        kernel.ι (f p q ≫ g (p + 2) (q - 1)) ≫ f p q := by
  let d := f p q ≫ g (p + 2) (q - 1)
  let b := kernel.lift d (β p q) (hβ p q)
  let u : kernel d ⟶ D ((((p + 2) + 1) - 1)) ((((q - 1) - 1) + 1)) :=
    kernel.ι d ≫ f p q ≫ eqToHom (by congr 1 <;> omega)
  have hu : u ≫ g ((((p + 2) + 1) - 1)) ((((q - 1) - 1) + 1)) = 0 := by
    have ht := transport_family g
      (show p + 2 = ((p + 2) + 1) - 1 by omega)
      (show q - 1 = ((q - 1) - 1) + 1 by omega)
    dsimp only [u]
    simp only [Category.assoc]
    rw [ht, ← Category.assoc (f p q), ← Category.assoc]
    change (kernel.ι d ≫ d) ≫ _ = 0
    rw [kernel.condition, zero_comp]
  obtain ⟨k, hk⟩ := lift_image_of_eq
    (a ((p + 2) + 1) ((q - 1) - 1))
    (g (((p + 2) + 1) - 1) (((q - 1) - 1) + 1)) (hgg _ _) u hu
  have hbf : β p q ≫ f p q = 0 := by
    rw [hβeq]
    have ht := transport_family f
      (show ((p - s - 2) + 2) + (s : ℤ) = p by omega)
      (show ((q + s + 1) - 1) - (s : ℤ) = q by omega)
    simp only [Category.assoc]
    rw [ht, ← Category.assoc (g ((p - s - 2) + 2) ((q + s + 1) - 1)), hg,
      zero_comp, comp_zero]
  have hbk : b ≫ k = 0 := by
    apply (cancel_mono (image.ι (a ((p + 2) + 1) ((q - 1) - 1)))).mp
    rw [Category.assoc, hk]
    simp only [u, b, kernel.lift_ι_assoc]
    rw [← Category.assoc, hbf, zero_comp, zero_comp]
  refine ⟨cokernel.desc b k hbk, ?_⟩
  rw [cokernel.π_desc_assoc, ← Category.assoc, hk]
  simp only [u, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

private theorem desc_image_of_eq {A B T U : C} (f : A ⟶ B) (a : B ⟶ T)
    (h : imageSubobject f = kernelSubobject a) (u : B ⟶ U) (hu : f ≫ u = 0) :
    ∃ l : image a ⟶ U, factorThruImage a ≫ l = u := by
  let S := ShortComplex.mk f a ((kernelSubobject_factors_iff a f).mp (by
    rw [← h]
    simpa using imageSubobject_factors_comp_self f (𝟙 A)))
  have he : S.Exact := (S.exact_iff_image_eq_kernel).mpr h
  let l := CokernelCofork.IsColimit.desc' he.isColimitImage u hu
  exact ⟨l.1, l.2⟩

private theorem desc_image_at_index (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (ha : ∀ p q, imageSubobject (f p q) = kernelSubobject (a (p + 2) (q - 1)))
    (p q r t : ℤ) (hp : p + 2 = r) (hq : q - 1 = t) {U : C} (u : D r t ⟶ U)
    (hu : f p q ≫ eqToHom (congrArg₂ D hp hq) ≫ u = 0) :
    ∃ l : image (a r t) ⟶ U, factorThruImage (a r t) ≫ l = u := by
  subst r
  subst t
  simp only [eqToHom_refl, Category.id_comp] at hu
  exact desc_image_of_eq (f p q) (a (p + 2) (q - 1)) (ha p q) u hu

/-- The backward map descends the cycle quotient map through the alpha image.
Source: Stacks Project, Remark 12.21.5 and its footnote, Tag 0AMJ
(blueprint: lem-sp-derived-map-construction). -/
theorem derivedCoupleBackward_exists (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (ha : ∀ p q, imageSubobject (f p q) = kernelSubobject (a (p + 2) (q - 1)))
    (hβeq : ∀ p q, β p q =
      (f (p - s - 2) (q + s + 1) ≫ g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
        eqToHom (by congr 1 <;> omega)) (p q : ℤ) :
    ∃ l : image (a (p + 1) (q - 1)) ⟶
        cokernel (kernel.lift
          (f (p + (s + 1)) (q - (s + 1)) ≫
            g ((p + (s + 1)) + 2) ((q - (s + 1)) - 1))
          (β (p + (s + 1)) (q - (s + 1))) (hβ _ _)),
      factorThruImage (a (p + 1) (q - 1)) ≫ l =
        kernel.lift (f ((p + 1) + s) ((q - 1) - s) ≫
          g (((p + 1) + s) + 2) (((q - 1) - s) - 1))
          (g (p + 1) (q - 1)) (by simp only [← Category.assoc, hg, zero_comp]) ≫
        cokernel.π (kernel.lift
          (f ((p + 1) + s) ((q - 1) - s) ≫
            g (((p + 1) + s) + 2) (((q - 1) - s) - 1))
          (β ((p + 1) + s) ((q - 1) - s)) (hβ _ _)) ≫
        eqToHom (by
          exact congrArg₂
            (fun p q ↦ cokernel (kernel.lift (f p q ≫ g (p + 2) (q - 1))
              (β p q) (hβ p q))) (by omega) (by omega)) := by
  let Q := fun p q ↦ cokernel
    (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q))
  let G : ∀ p q, D p q ⟶ Q (p + s) (q - s) := fun p q ↦
    kernel.lift (f (p + s) (q - s) ≫ g ((p + s) + 2) ((q - s) - 1))
      (g p q) (by simp only [← Category.assoc, hg, zero_comp]) ≫
    cokernel.π (kernel.lift (f (p + s) (q - s) ≫ g ((p + s) + 2) ((q - s) - 1))
      (β (p + s) (q - s)) (hβ _ _))
  have hGzero (r t : ℤ) : f r t ≫ G (r + 2) (t - 1) = 0 := by
    let x := (r + 2) + (s : ℤ)
    let y := (t - 1) - (s : ℤ)
    let B := kernel.lift (f x y ≫ g (x + 2) (y - 1)) (β x y) (hβ x y)
    have hb : f r t ≫ kernel.lift (f x y ≫ g (x + 2) (y - 1))
        (g (r + 2) (t - 1)) (by
          dsimp only [x, y]
          simp only [← Category.assoc, hg, zero_comp]) =
        eqToHom (show E r t = E (x - s - 2) (y + s + 1) by
          dsimp only [x, y]; congr 1 <;> omega) ≫ B := by
      apply (cancel_mono (kernel.ι (f x y ≫ g (x + 2) (y - 1)))).mp
      simp only [B, Category.assoc, kernel.lift_ι]
      rw [hβeq]
      have ht := transport_family (fun p q ↦ f p q ≫ g (p + 2) (q - 1))
        (show r = x - s - 2 by dsimp only [x]; omega)
        (show t = y + s + 1 by dsimp only [y]; omega)
      rw [← Category.assoc, ht]
      simp only [Category.assoc, eqToHom_trans, x, y, eqToHom_refl, Category.comp_id]
    dsimp only [G]
    rw [← Category.assoc, hb, Category.assoc]
    change eqToHom _ ≫ B ≫ cokernel.π B = 0
    rw [cokernel.condition, comp_zero]
  have ht := transport_family G
    (show ((p + 1) - 2) + 2 = p + 1 by omega)
    (show (((q - 1) + 1) - 1) = q - 1 by omega)
  have hu : f ((p + 1) - 2) ((q - 1) + 1) ≫
      eqToHom (by congr 1 <;> omega) ≫ G (p + 1) (q - 1) = 0 := by
    rw [ht, ← Category.assoc, hGzero, zero_comp]
  obtain ⟨k, hk⟩ := desc_image_at_index D E a f ha ((p + 1) - 2) ((q - 1) + 1)
    (p + 1) (q - 1) (by omega) (by omega) (G (p + 1) (q - 1)) hu
  refine ⟨k ≫ eqToHom (by
    exact congrArg₂ Q (by omega) (by omega)), ?_⟩
  rw [← Category.assoc, hk]
  simp only [G, Category.assoc]

/-- The two descended maps with their defining equations. The alpha restriction
is constructed explicitly; exactness is a separate theorem.
Source: Stacks Project, Tags 011R and 0AMJ
(blueprint: lem-sp-derived-map-construction). -/
structure DerivedCoupleMapData (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0) where
  forward : ∀ p q,
    cokernel (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q)) ⟶
      image (a ((p + 2) + 1) ((q - 1) - 1))
  backward : ∀ p q, image (a (p + 1) (q - 1)) ⟶
    cokernel (kernel.lift
      (f (p + (s + 1)) (q - (s + 1)) ≫
        g ((p + (s + 1)) + 2) ((q - (s + 1)) - 1))
      (β (p + (s + 1)) (q - (s + 1))) (hβ _ _))
  f_comm : ∀ p q,
    cokernel.π (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q)) ≫
      forward p q ≫ image.ι (a ((p + 2) + 1) ((q - 1) - 1)) ≫
        eqToHom (by congr 1 <;> omega) =
      kernel.ι (f p q ≫ g (p + 2) (q - 1)) ≫ f p q
  g_comm : ∀ p q,
    factorThruImage (a (p + 1) (q - 1)) ≫ backward p q =
      kernel.lift (f ((p + 1) + s) ((q - 1) - s) ≫
        g (((p + 1) + s) + 2) (((q - 1) - s) - 1))
        (g (p + 1) (q - 1)) (by simp only [← Category.assoc, hg, zero_comp]) ≫
      cokernel.π (kernel.lift
        (f ((p + 1) + s) ((q - 1) - s) ≫
          g (((p + 1) + s) + 2) (((q - 1) - s) - 1))
        (β ((p + 1) + s) ((q - 1) - s)) (hβ _ _)) ≫
      eqToHom (by
        have hp : (p + 1) + (s : ℤ) = p + ((s + 1 : ℕ) : ℤ) := by omega
        have hq : (q - 1) - (s : ℤ) = q - ((s + 1 : ℕ) : ℤ) := by omega
        exact congrArg₂
          (fun p q ↦ cokernel (kernel.lift (f p q ≫ g (p + 2) (q - 1))
            (β p q) (hβ p q))) hp hq)

namespace DerivedCoupleMapData

variable {D E : ℤ → ℤ → C}
    {a : ∀ p q, D p q ⟶ D (p - 1) (q + 1)}
    {f : ∀ p q, E p q ⟶ D (p + 2) (q - 1)}
    {g : ∀ p q, D p q ⟶ E (p + s) (q - s)}
    {β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q}
    {hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0}
    {hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0}

/-- Alpha is the explicit image restriction, independent of any choices.
Source: Stacks Project, Tag 011R (blueprint: lem-sp-derived-map-construction). -/
noncomputable def alpha (_M : DerivedCoupleMapData D E a f g β hβ hg) (p q : ℤ) :
    image (a (p + 1) (q - 1)) ⟶ image (a ((p - 1) + 1) ((q + 1) - 1)) :=
  derivedCoupleAlpha D a p q

/-- The defining equation for the explicit alpha restriction.
Source: Stacks Project, Tag 011R (blueprint: lem-sp-derived-map-construction). -/
theorem alpha_comm (M : DerivedCoupleMapData D E a f g β hβ hg) (p q : ℤ) :
    M.alpha p q ≫ image.ι (a ((p - 1) + 1) ((q + 1) - 1)) ≫
      eqToHom (by congr 1 <;> omega) =
    image.ι (a (p + 1) (q - 1)) ≫ eqToHom (by congr 1 <;> omega) ≫ a p q :=
  derivedCoupleAlpha_comm D a p q

end DerivedCoupleMapData

/-- The restriction equations determine all three maps uniquely.
Source: Stacks Project, Lemma 12.21.2 and Remark 12.21.5, Tags 011R and 0AMJ
(blueprint: lem-sp-derived-map-construction). -/
theorem derivedCoupleMapData_unique (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (M N : DerivedCoupleMapData D E a f g β hβ hg) : M = N := by
  have hf : M.forward = N.forward := by
    funext p q
    apply (cancel_epi
      (cokernel.π (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q)))).mp
    apply (cancel_mono (image.ι (a ((p + 2) + 1) ((q - 1) - 1)) ≫
      eqToHom (show D (((p + 2) + 1) - 1) (((q - 1) - 1) + 1) =
        D (p + 2) (q - 1) by congr 1 <;> omega))).mp
    simpa only [Category.assoc] using (M.f_comm p q).trans (N.f_comm p q).symm
  have hg' : M.backward = N.backward := by
    funext p q
    apply (cancel_epi (factorThruImage (a (p + 1) (q - 1)))).mp
    exact (M.g_comm p q).trans (N.g_comm p q).symm
  cases M
  cases N
  cases hf
  cases hg'
  rfl

/-- Construct the induced maps, without asserting exactness of the new triangle.
Source: Stacks Project, Lemma 12.21.2, Tag 011R, and Remark 12.21.5, Tag 0AMJ
(blueprint: lem-sp-derived-map-construction).

Proof. Restrict `a` to its incoming image: its composite with the next image
inclusion factors through that image, using the image factorization of the incoming
`a`. The restriction is unique because image inclusions are monomorphisms.
The restriction of `f` to `ker(f ≫ g)` lands in `ker g`, which is the incoming
image of `a` by `hgg` (after reindexing). Lift to that image. The lifted incoming
boundary is killed by this map: after composing with the mono image inclusion,
the composite is `f ≫ g ≫ f`, zero by `hg`. Thus descend through its cokernel.
This gives `forward` and its defining equation, uniquely by epi cancellation.
Finally `g` lands in cycles by `hg`. Its composite with the cycle quotient
kills `ker a = im f`: on that image it is the incoming differential, which the
quotient kills by `hβeq`. Every epi image factorization in an abelian category
is a cokernel of its kernel, so this map descends uniquely through the incoming
image epimorphism of `a`. This gives `backward` and its equation. The three
universal properties determine all maps uniquely; no arbitrary object is chosen. -/
theorem derivedCoupleMapData_exists (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (ha : ∀ p q, imageSubobject (f p q) = kernelSubobject (a (p + 2) (q - 1)))
    (hgg : ∀ p q, imageSubobject (a p q) = kernelSubobject (g (p - 1) (q + 1)))
    (hβeq : ∀ p q, β p q =
      (f (p - s - 2) (q + s + 1) ≫ g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
        eqToHom (by congr 1 <;> omega)) :
    Nonempty (DerivedCoupleMapData D E a f g β hβ hg) := by
  classical
  choose F hF using fun p q ↦ derivedCoupleForward_exists D E a f g β hβ hg hgg hβeq p q
  choose G hG using fun p q ↦ derivedCoupleBackward_exists D E a f g β hβ hg ha hβeq p q
  exact ⟨{ forward := F, backward := G, f_comm := hF, g_comm := hG }⟩

end CategoryTheory
