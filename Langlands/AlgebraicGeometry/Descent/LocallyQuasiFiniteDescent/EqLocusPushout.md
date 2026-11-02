# Flat base change of an equalizer of two ring maps

Module `Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.EqLocusPushout`, namespace
`Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent`. This is a commutative-algebra helper for
the proof of `Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement`
(Stacks Tag 02W8 in sheaf form). It is internal: Stacks has no tag for this exact statement.
It is the algebra behind descending the ring of global functions of a quasi-affine scheme along
a flat map. The ingredient used is the standard fact that tensoring with a flat module preserves
the kernel of a linear map.

## Statements

- `isPushout_eqLocus_of_flat`. Let `r : R → A` be a flat ring map and `a : A → C` a ring map.
  Suppose:
  - `D` is the pushout of `C ← R → A`, with coprojections `i₁ : C → D` and `s : A → D`;
  - `E` is the pushout of `D ← R → A`, where `R → D` is `s ∘ r`, with coprojections
    `e₁ : D → E` and `e₂ : A → E`;
  - `i₂ : C → D` and `q₁ q₂ : D → E` are ring maps with `q₁ ∘ i₁ = e₁ ∘ i₁`,
    `q₂ ∘ i₁ = e₁ ∘ i₂`, `q₁ ∘ s = q₂ ∘ s = e₂`, `i₂ ∘ a = s` and `q₁ ∘ i₂ = q₂ ∘ i₂`;
  - `i₂` is injective.

  Let `B = {c ∈ C | i₁ c = i₂ c}` (`RingHom.eqLocus`). Then `R → C` lands in `B`, and the
  square with sides `R → B`, `r`, the inclusion `B → C` and `a` is a pushout in
  `CommRingCat`. In other words, `C` is the base change of `B` along `r`.
- `exists_isPushout_eqLocus` is the same statement for morphisms of `CommRingCat`. It gives
  `B`, `R ⟶ B` and `ι : B ⟶ C` with `IsPushout rB r ι a` and `ι ≫ i₁ = ι ≫ i₂`.

In the application, `C` is the ring of global functions of the base change of a quasi-affine
scheme along an fppf chart `Spec A → Spec R`. `i₁` and `i₂` come from the two projections of
the double overlap.

## Proof

The proof makes `C`, `D` and `E` into `R`-algebras. It identifies `D` with `C ⊗[R] A` and `E`
with `D ⊗[R] A` (`Algebra.IsPushout.equiv`). The inclusion `ι : B → C` is the kernel of the
`R`-linear map `i₁ - i₂ : C → D`. Since `A` is flat over `R`, `ι ⊗ A` is injective and is the
kernel of `(i₁ - i₂) ⊗ A` (`Module.Flat.rTensor_exact`,
`Module.Flat.rTensor_preserves_injective_linearMap`).

Let `m : B ⊗[R] A → C` be the multiplication map `b ⊗ x ↦ b · a(x)`. Two identities are checked
on pure tensors:
- `i₂ ∘ m` equals `ι ⊗ A` read in `D`;
- `(i₁ - i₂) ⊗ A` read in `E` equals `q₁ - q₂`.

The first identity and the injectivity of `ι ⊗ A` show that `m` is injective. For
surjectivity, take `c ∈ C`. The element `i₂ c` of `D = C ⊗[R] A` is killed by
`(i₁ - i₂) ⊗ A`, because `q₁ (i₂ c) = q₂ (i₂ c)`. By exactness it comes from some `z ∈ B ⊗[R] A`.
Then `i₂ (m z) = i₂ c`, so `m z = c` because `i₂` is injective. Hence `m` is a linear
equivalence. This gives `IsBaseChange` and the pushout square
(`CommRingCat.isPushout_iff_isPushout`).
