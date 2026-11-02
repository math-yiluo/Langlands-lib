# Descent of finite presentation along a faithfully flat map on the source

Author: Worker 293.

This module proves the finite presentation case of Stacks Project, Descent,
Lemma 35.14.1 (Tag 02KK; Lemma 14.1 on p.42 of the registered PDF source
`stacks-descent-ed88ff78-2026`): for ring maps `R → A → B` with `A → B`
faithfully flat and of finite presentation, if `R → B` is of finite
presentation then so is `R → A`.

## Declarations

- `Langlands.Algebra.finitePresentation_of_faithfullyFlat_of_finitePresentation`
  is the lemma above in algebra form. The rings `R`, `A`, `B` are in one
  universe `u`, with `IsScalarTower R A B`, `Module.FaithfullyFlat A B`,
  `Algebra.FinitePresentation A B` and `Algebra.FinitePresentation R B`. The
  conclusion is `Algebra.FinitePresentation R A`.
- `Langlands.Algebra.finitePresentation_of_finitePresentation_cover` is the
  descent step. It assumes a flat finitely presented `A₀`-algebra `B₀` with
  `A ⊗[A₀] B₀ ≃ₐ[A] B`, elements `y : Fin n → A₀` such that every prime of
  `A₀` not containing some `y i` lies in the image of `Spec B₀ → Spec A₀`, and
  a finitely presented `R`-algebra `T` in scalar towers `R → T → A` and
  `A₀ → T → A` with `∑ i, x i * y i = 1` in `T`. It concludes
  `Algebra.FinitePresentation R A`.
- `Langlands.Algebra.finitePresentation_of_finitePresentation_cover_of_sum`
  builds such a `T` from a finitely presented `R`-algebra `S`, ring maps
  `ι : A₀ → S` and `χ : S → A` compatible with the maps from `R` and `A₀`, and
  elements `a : Fin n → A` with `∑ i, a i * y i = 1` in `A`.

## Proof

The Lean proof does not follow the Stacks proof of 02KK, which uses the
colimit criterion for finite presentation. It follows the shape of the
Stacks proof of the finite type case (Lemma 35.14.2, Tag 0367), adapted
to finite presentation.

1. The Library theorem `Langlands.Algebra.exists_flat_finitePresentation_model`
   gives a subring `A₀ ⊆ A` of finite type over `ℤ` and a flat finitely
   presented `A₀`-algebra `B₀` with `A ⊗[A₀] B₀ ≃ₐ[A] B`. Since `ℤ` is
   Noetherian, `A₀` is finitely presented over `ℤ`.
2. The Library theorem `Langlands.Algebra.exists_sum_eq_one_of_faithfullyFlat`
   gives `y : Fin n → A₀` and `a : Fin n → A` with `∑ aᵢ yᵢ = 1` in `A`, where
   each basic open `D(yᵢ)` of `Spec A₀` lies in the open image of `Spec B₀`.
3. Put `S = R ⊗[ℤ] A₀`. It is finitely presented over `R` by base change.
   The maps are `ι = includeRight : A₀ → S` and `χ = productMap` of
   `R → A` and the inclusion `A₀ → A`.
4. Put `T = S[X₁, …, Xₙ] / (∑ Xᵢ yᵢ - 1)`. It is finitely presented over `R`,
   being a quotient of a polynomial ring over `S` by one element. The map
   `T → A` sends `Xᵢ` to `aᵢ` and is induced by `χ`. It is well defined by
   step 2. In `T` the classes `xᵢ` of `Xᵢ` satisfy `∑ xᵢ yᵢ = 1`.
5. Descent step. The Library theorem
   `Langlands.Algebra.faithfullyFlat_tensorProduct_of_sum_eq_one` shows that
   `Q = T ⊗[A₀] B₀` is faithfully flat over `T`. Since `∑ xᵢ yᵢ = 1`, every
   prime of `T` omits some `yᵢ`, so its contraction to `A₀` lies in `D(yᵢ)`,
   inside the image of `Spec B₀`.
   `Algebra.TensorProduct.cancelBaseChange` and the model isomorphism give
   `A ⊗[T] Q ≃ₐ[A] B`. The composite `R → T → Q` is of finite type and the
   composite `R → Q → A ⊗[T] Q ≃ B` is the finitely presented map `R → B`.
   So `RingHom.FinitePresentation.of_comp_finiteType` makes
   `includeRight : Q → A ⊗[T] Q` of finite presentation. Mathlib's
   `RingHom.FinitePresentation.codescendsAlong_faithfullyFlat` (finite
   presentation descends along faithfully flat base change) then makes
   `T → A` of finite presentation. Composing with `R → T` gives the claim.

## Provenance

The statement is the finite presentation case of Stacks 02KK. The three
Library results used in steps 1, 2 and 5 are already published. The rest
is internal derived content.
