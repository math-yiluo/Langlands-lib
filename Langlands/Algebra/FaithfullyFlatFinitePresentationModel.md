# Faithfully flat finitely presented models

Author: Worker 1103.

This helper module proves the algebra half of the finite-type branch of
Stacks Project Lemma 35.14.3 (Tag 02KL). It derives Stacks Tag 0367 from a
flat, finitely presented model at a finite type stage (Stacks Algebra,
Lemma 10.168.1(1), Tag 02JO). That model is supplied as an explicit hypothesis here.
The module adds no axioms, and its declarations live in `Langlands.Algebra`.

## Provenance

- Stacks Project, Algebra, Lemma 10.168.2 (Tag 034Y): for ring maps
  `R → A → B` with `A → B` faithfully flat of finite presentation, `A → B`
  is the base change of a faithfully flat, finitely presented map
  `A₀ → B₀`, where `R → A₀` is of finite presentation.
  `exists_faithfullyFlat_finitePresentation_model_of_flat_model` is the
  weaker form needed for Tag 0367. It starts from the flat model of
  Lemma 10.168.1(1) and produces a faithfully flat model over a subalgebra
  `A₁ ⊆ A` of finite type over `R`. Finite presentation of `A₁` over `R` is
  neither claimed nor needed. The proof follows the Stacks argument
  (openness of the image, `I₀ A = A`, enlarging `A₀` by the coefficients).
  Stacks first works over `ℤ` and then tensors with `R`, whereas the Lean
  proof adjoins the generators of `A₀` over `R` inside `A` directly.
- Stacks Project, Descent, Lemma 35.14.2 (Tag 0367): if `R → A → B` with
  `A → B` faithfully flat and finitely presented and `R → B` of finite type,
  then `R → A` is of finite type. `finiteType_of_faithfullyFlat_of_flat_model`
  proves this. It takes the conclusion of Lemma 10.168.1(1) for `A → B` as a
  hypothesis instead of assuming finite presentation of `A → B` directly.
  The Stacks proof enlarges `A₀` until `B₀ → B` is surjective and concludes
  from faithful flatness that `A₀ → A` is surjective. The Lean proof instead
  applies Mathlib's faithfully flat descent of finite type along the base
  change `B₁ → B₁ ⊗[A₁] A`.

The first two lemmas below are internal steps of the Stacks proof of
Tag 034Y, stated separately for reuse.

## Declarations and Lean proofs

`mem_range_comap_tensorProduct`: for `R`-algebras `S` and `T`, a prime `P` of
`S` lies in the image of `Spec (S ⊗[R] T) → Spec S` if its contraction `p` to
`R` lies in the image of `Spec T → Spec R`. The proof uses Mathlib's
characterisation `PrimeSpectrum.nontrivial_iff_mem_rangeComap`: a prime lies
in the image exactly when the fibre algebra `κ(p) ⊗[R] T` is nontrivial.
Here `κ(P) ⊗[κ(p)] (κ(p) ⊗[R] T)` is nontrivial because `κ(p) → κ(P)` is an
injective map of fields
(`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right`).
Two `cancelBaseChange` isomorphisms identify this ring with
`κ(P) ⊗[S] (S ⊗[R] T)`.

`exists_sum_eq_one_of_faithfullyFlat`: let `A → B` be faithfully flat and let
`e : A ⊗[A₀] B₀ ≃ₐ[A] B` for a flat, finitely presented `A₀`-algebra `B₀`.
Then `1 = ∑ aᵢ yᵢ` in `A`, with `aᵢ ∈ A`, `yᵢ ∈ A₀`, and every basic open
`D(yᵢ)` of `Spec A₀` contained in the image `U` of `Spec B₀`. In Lean, `U` is
open by `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`
(Chevalley's theorem plus going down for flat maps). Write its complement as
`V(I)`. Every prime of `A` lifts to `B`, which is faithfully flat over `A`,
so its contraction to `A₀` factors through `B₀` and lies in `U`. Hence no
maximal ideal of `A` contains `I A`, so `I A = A`. A representation of `1` in
the span of the image of `I` gives the elements `aᵢ` and `yᵢ ∈ I`.

`faithfullyFlat_tensorProduct_of_sum_eq_one`: under this conclusion, for any
`A₀`-algebra `A₁` in which `1 = ∑ aᵢ yᵢ` holds, `A₁ ⊗[A₀] B₀` is faithfully
flat over `A₁`. It is flat by base change. By
`Module.FaithfullyFlat.of_comap_surjective` it suffices that every prime `P`
of `A₁` is in the image of `Spec`. Some `yᵢ` lies outside `P`, since
otherwise `1 ∈ P`. Then the contraction of `P` to `A₀` lies in `D(yᵢ) ⊆ U`,
and `mem_range_comap_tensorProduct` applies.

`exists_faithfullyFlat_finitePresentation_model_of_flat_model` (Tag 034Y,
upgrade step): let `A` be an `R`-algebra, `A → B` faithfully flat, and
`e : A ⊗[A₀] B₀ ≃ₐ[A] B` with `A₀ : Subalgebra ℤ A` of finite type and `B₀`
flat and finitely presented over `A₀`. Then there are `A₁ : Subalgebra R A`
of finite type over `R` and a faithfully flat, finitely presented
`A₁`-algebra `B₁` with `A ⊗[A₁] B₁ ≃ₐ[A] B`. The proof takes a finite
generating set `t` of `A₀` over `ℤ` and the coefficients `aᵢ` from
`exists_sum_eq_one_of_faithfullyFlat`. It sets
`A₁ = Algebra.adjoin R (t ∪ {aᵢ})`, which contains `A₀`, and
`B₁ = A₁ ⊗[A₀] B₀`. Finite presentation holds by base change, and faithful
flatness follows from `faithfullyFlat_tensorProduct_of_sum_eq_one`. The
equivalence is `Algebra.TensorProduct.cancelBaseChange` followed by `e`.

`finiteType_of_faithfullyFlat_of_flat_model` (Tag 0367): let `R → A → B` be
a scalar tower with `A → B` faithfully flat and `B` of finite type over `R`.
Suppose `B` has a model as in Lemma 10.168.1(1): `A₀ : Subalgebra ℤ A` of
finite type, and `B₀` flat and finitely presented over `A₀` with
`A ⊗[A₀] B₀ ≃ₐ[A] B`. Then `A` is of finite type over `R`. The proof applies
the previous theorem to get `A₁` and `B₁`. `B` is of finite type over `A₁`
because it is of finite type over `R ⊆ A₁`
(`Algebra.FiniteType.of_restrictScalars_finiteType`). Transported along
`e'` and the tensor commutativity map, `B₁ ⊗[A₁] A` is of finite type over
`A₁`, hence over `B₁`. Mathlib's
`Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`, for
faithfully flat `B₁` over `A₁`, gives that `A` is of finite type over `A₁`.
Composing with finite type of `A₁` over `R` proves the claim. Finite
presentation of `A → B` is not used here; it enters only through the flat
model.
