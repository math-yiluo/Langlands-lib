# Cancellation for a tensor of morphisms from the unit: proof

Authors: Worker 259, Worker 124 and Worker 370. Worker 124 supplied the
categorical derivation, which Worker 370 documented in the statement Markdown
and the proof task. Worker 259 wrote the Lean proof and this file.

The theorem `Langlands.CategoryTheory.Picard.unitTensorCancellation` proves exactly
the published proposition
`Langlands.CategoryTheory.Picard.UnitTensorCancellationStatement C`, imported
unchanged from `Langlands.CategoryTheory.Picard.UnitTensorCancellationStatement`.
Its complete type is

```lean
∀ (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C],
  UnitTensorCancellationStatement C
```

with independent object universe `u` and morphism universe `v`. No hypothesis
beyond the category, monoidal and braided structures of the target is used.
Neither morphism and neither target object is assumed invertible, and no
balancedness is used. The module also imports
`Langlands.CategoryTheory.Picard.TensorEquivalenceProof` and Mathlib's
`Mathlib.CategoryTheory.Functor.EpiMono`.

## The left factor

The auxiliary theorem
`Langlands.CategoryTheory.Picard.isIso_left_of_isIso_unitTensorHom` states: for
`s : 𝟙_ C ⟶ M` and `t : 𝟙_ C ⟶ N` with `IsIso (s ⊗ₘ t)` (an instance argument),
`s` is an isomorphism. Its proof has four steps.

1. *`N` is tensor-invertible.* The composite of the braiding
   `β_ N M : N ⊗ M ≅ M ⊗ N`, the inverse of `asIso (s ⊗ₘ t)`, and the left unitor
   `λ_ (𝟙_ C) : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C` is an isomorphism `e : N ⊗ M ≅ 𝟙_ C`. The
   Library theorem `tensorInvertibilityEquivalence C N` turns `⟨M, ⟨e⟩⟩` into
   `(tensorLeft N).IsEquivalence`.

2. *`s` is a split monomorphism.* The proof gives the retraction
   `(ρ_ M).inv ≫ M ◁ t ≫ inv (s ⊗ₘ t) ≫ (ρ_ (𝟙_ C)).hom` explicitly. Naturality
   of the inverse right unitor (`rightUnitor_inv_naturality`) rewrites
   `s ≫ (ρ_ M).inv` as `(ρ_ (𝟙_ C)).inv ≫ s ▷ 𝟙_ C`. Mathlib's `tensorHom_def`
   gives `s ▷ 𝟙_ C ≫ M ◁ t = s ⊗ₘ t`; this cancels against `inv (s ⊗ₘ t)`, and
   the unitors cancel. This is the "first factorization" of the statement
   Markdown, with the splitting through right tensoring by the unit written out.

3. *`s ▷ N` is an epimorphism.* Mathlib's `tensorHom_def'` gives
   `s ⊗ₘ t = 𝟙_ C ◁ t ≫ s ▷ N`. An isomorphism is an epimorphism, and the last
   factor of an epimorphic composite is an epimorphism (`epi_of_epi`).

4. *`s` is an epimorphism.* The axiom `BraidedCategory.braiding_naturality_right`
   gives `N ◁ s ≫ (β_ N M).hom = (β_ N (𝟙_ C)).hom ≫ s ▷ N`, so
   `(tensorLeft N).map s = N ◁ s` equals
   `((β_ N (𝟙_ C)).hom ≫ s ▷ N) ≫ (β_ N M).inv`. This is a composite of
   epimorphisms. The equivalence `tensorLeft N` is faithful, hence reflects
   epimorphisms; `Functor.epi_of_epi_map` then shows that `s` is an epimorphism.

Finally, Mathlib's `isIso_of_epi_of_isSplitMono` states that a split
monomorphism that is an epimorphism is an isomorphism, in any category.

This follows the derivation in the statement Markdown. One difference: the
statement Markdown reflects the epimorphism `s ▷ N` through right tensoring by
`N`. The Lean proof instead moves it by braiding to `N ◁ s` and reflects through
left tensoring by `N`, which is the equivalence given directly by the Library
theorem.

## The right factor and the main theorem

`unitTensorCancellation C` introduces `M`, `N`, `s`, `t` and the hypothesis
`IsIso (s ⊗ₘ t)`. The left factor is handled by
`isIso_left_of_isIso_unitTensorHom s t`. For the right factor, Mathlib's
naturality of the braiding (`BraidedCategory.braiding_naturality`),
`(s ⊗ₘ t) ≫ (β_ M N).hom = (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (t ⊗ₘ s)`, gives
`t ⊗ₘ s = (β_ (𝟙_ C) (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (β_ M N).hom`. This is a composite
of isomorphisms. Applying the auxiliary theorem to `t ⊗ₘ s`, with the roles of
`M` and `N` exchanged, shows that `t` is an isomorphism.

## Scope

This proves only the categorical cancellation statement. It does not construct
a local factorization of a sheaf pairing into morphisms from the unit. It also
does not prove the converse of Stacks Project Lemma 17.25.4 or any scheme or
ringed-space result. The source boundary is as described in the statement's
Markdown.
