import Langlands.CategoryTheory.RenardImageFactorizationStatements

/-!
# Renard A.VI.2(1, 4–5): proofs of balancedness, images and factorization

Proves `Langlands.Renard.ImageFactorizationStatement C` for every abelian category
`C`. Every epi–mono factorization in an abelian category is a strong epi–mono
factorization, and the lifting property of a strong epimorphism against a
monomorphism gives both universal properties. The remaining clauses reuse
Mathlib's abelian image and coimage API. See the paired Markdown for the route.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

section General

variable {C : Type u} [Category.{v} C]

/-- A factorization `e ≫ m = f` with `e` a strong epimorphism has the image universal
property: the lifting property of `e` against a mono `m'` gives the comparison map. -/
theorem imageUniversalProperty_of_strongEpi {X Y I : C} {f : X ⟶ Y} {e : X ⟶ I}
    {m : I ⟶ Y} [StrongEpi e] (hf : e ≫ m = f) : ImageUniversalProperty f e m := by
  intro J e' m' _ hf'
  have sq : CommSq e' e m' m := ⟨by rw [hf, hf']⟩
  refine ⟨sq.lift, ⟨sq.fac_right, sq.fac_left⟩, fun t ht => ?_⟩
  rw [← cancel_mono m', ht.1, sq.fac_right]

/-- In a category where every epimorphism is strong, a factorization `e ≫ m = f` with
`m` a monomorphism has the coimage universal property: the lifting property of the
epimorphism `e'` of another factorization against `m` gives the comparison map. -/
theorem coimageUniversalProperty_of_mono {X Y I : C} [StrongEpiCategory C] {f : X ⟶ Y}
    {e : X ⟶ I} {m : I ⟶ Y} [Mono m] (hf : e ≫ m = f) : CoimageUniversalProperty f e m := by
  intro J e' m' _ hf'
  have : StrongEpi e' := strongEpi_of_epi e'
  have sq : CommSq e e' m m' := ⟨by rw [hf, hf']⟩
  refine ⟨sq.lift, ⟨sq.fac_left, sq.fac_right⟩, fun t ht => ?_⟩
  rw [← cancel_epi e', ht.1, sq.fac_left]

end General

section Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A.VI.2(1): in an abelian category a morphism is an isomorphism exactly when it is
mono and epi. -/
theorem isoIffMonoAndEpiStatement : IsoIffMonoAndEpiStatement C :=
  fun _ _ f => isIso_iff_mono_and_epi f

variable {C}

/-- In an abelian category every factorization `e ≫ m = f` with `e` epi has the image
universal property, since every epimorphism is strong. -/
theorem imageUniversalProperty_of_epi {X Y I : C} {f : X ⟶ Y} {e : X ⟶ I}
    {m : I ⟶ Y} [Epi e] (hf : e ≫ m = f) : ImageUniversalProperty f e m :=
  have : StrongEpi e := strongEpi_of_epi e
  imageUniversalProperty_of_strongEpi hf

variable (C)

/-- A.VI.2(4): the kernel of the cokernel is the image, the cokernel of the kernel is the
coimage, and the abelian image, coimage, comparison and `Limits.image` agree. -/
theorem abelianImageCoimageStatement : AbelianImageCoimageStatement C := by
  intro X Y f
  refine ⟨rfl, rfl, imageUniversalProperty_of_epi (Abelian.image.fac f),
    Abelian.imageIsoImage_hom_comp_image_ι f, ?_,
    coimageUniversalProperty_of_mono (Abelian.coimage.fac f), inferInstance, inferInstance,
    Abelian.image.fac f, inferInstance, inferInstance, Abelian.coimage.fac f, inferInstance,
    ?_, ?_⟩
  · rw [← cancel_mono (Limits.image.ι f), Category.assoc,
      Abelian.imageIsoImage_hom_comp_image_ι, Limits.image.fac]
    exact Abelian.image.fac f
  · simp [Abelian.coimageImageComparison]
  · ext
    simp [Abelian.coimageImageComparison]

/-- A.VI.2(5): epi–mono factorizations exist, are unique up to a unique compatible
isomorphism, and each is both an image and a coimage factorization. -/
theorem epiMonoFactorizationStatement : EpiMonoFactorizationStatement C := by
  intro X Y f
  refine ⟨⟨Abelian.image f, Abelian.factorThruImage f, Abelian.image.ι f, inferInstance,
    inferInstance, Abelian.image.fac f⟩, ?_, fun I e m _ _ hf =>
      ⟨imageUniversalProperty_of_epi hf, coimageUniversalProperty_of_mono hf⟩⟩
  intro I J e m e' m' _ _ _ _ hf hf'
  obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := imageUniversalProperty_of_epi hf J e' m' inferInstance hf'
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := imageUniversalProperty_of_epi hf' I e m inferInstance hf
  refine ⟨⟨t, s, ?_, ?_⟩, ⟨ht₂, ht₁⟩, fun φ hφ => ?_⟩
  · rw [← cancel_mono m, Category.assoc, hs₁, ht₁, Category.id_comp]
  · rw [← cancel_mono m', Category.assoc, ht₁, hs₁, Category.id_comp]
  · ext
    rw [← cancel_mono m', hφ.2]
    exact ht₁.symm

/-- Renard A.VI.2(1, 4–5) for every abelian category, with independent object and Hom
universes. -/
theorem imageFactorizationStatement : ImageFactorizationStatement C :=
  ⟨isoIffMonoAndEpiStatement C, abelianImageCoimageStatement C,
    epiMonoFactorizationStatement C⟩

end Abelian

end Langlands.Renard
