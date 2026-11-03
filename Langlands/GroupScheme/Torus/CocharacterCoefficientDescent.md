# Descent of group-algebra elements along field extensions

Module `Langlands.GroupScheme.Torus.CocharacterCoefficientDescent`, namespace
`Langlands.GroupScheme.CocharacterDescent`. It imports only Mathlib.

Throughout, `Λ` is an additive monoid and `A[Λ]` is Mathlib's
`AddMonoidAlgebra A Λ`. For an algebra map `f : A →ₐ[R] B`,
`AddMonoidAlgebra.mapAlgHom Λ f : A[Λ] →ₐ[R] B[Λ]` applies `f` to every
coefficient. The module states when an element of `L[Λ]` comes from `F[Λ]`
along `Algebra.ofId F L`.

## Statements

- `exists_mapAlgHom_ofId_eq`. Let `F` be a commutative semiring and `L` an
  `F`-algebra. If every coefficient `x.coeff γ` of `x : L[Λ]` lies in the
  range of `algebraMap F L`, then
  `x = mapAlgHom Λ (Algebra.ofId F L) y` for some `y : F[Λ]`.
- `exists_mapAlgHom_ofId_eq_of_isGalois` (Galois descent). Let `N / k` be a
  finite Galois field extension. If `x : N[Λ]` satisfies
  `mapAlgHom Λ σ x = x` for every `σ : N ≃ₐ[k] N`, then `x` comes from `k[Λ]`.
- `mem_range_algebraMap_of_tmul_one_eq_one_tmul`. Let `F` be a field and `L` a
  nonzero commutative `F`-algebra. If `ℓ : L` satisfies
  `ℓ ⊗ₜ[F] 1 = 1 ⊗ₜ[F] ℓ` in `L ⊗[F] L`, then `ℓ` lies in the range of
  `algebraMap F L`.
- `exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight` (equalizer
  descent). Let `F` be a field and `L` a nonzero commutative `F`-algebra. If
  `x : L[Λ]` has the same image under the two coefficient maps
  `includeLeft, includeRight : L →ₐ[F] L ⊗[F] L`, then `x` comes from `F[Λ]`.

## Proofs

1. `exists_mapAlgHom_ofId_eq`. Mathlib's `AddMonoidAlgebra.range_map`
   identifies the range of the coefficient map `AddMonoidAlgebra.map` with
   the elements all of whose coefficients lie in the range of the underlying
   additive map. This gives `y` with `map (algebraMap F L) y = x`. The two
   coefficient maps agree coefficientwise (`coeff_mapAlgHom`), so
   `mapAlgHom Λ (Algebra.ofId F L) y = x`.
2. Galois descent. Taking the `γ`-coefficient of `mapAlgHom Λ σ x = x` gives
   `σ (x.coeff γ) = x.coeff γ` for every `σ`. By Mathlib's
   `IsGalois.mem_range_algebraMap_iff_fixed`, each coefficient lies in the
   image of `k`. Then apply step 1.
3. Tensor criterion. A nonzero module over a field is free, hence faithfully
   flat. Mathlib's `Algebra.IsEffective.of_faithfullyFlat` says the sequence
   `F → L → L ⊗[F] L` with second map `s ↦ s ⊗ₜ 1 - 1 ⊗ₜ s` is exact. The
   hypothesis says `ℓ` is in the kernel of the second map, so `ℓ` is in the
   image of `F`.
4. Equalizer descent. Taking the `γ`-coefficient of the hypothesis gives
   `x.coeff γ ⊗ₜ 1 = 1 ⊗ₜ x.coeff γ`. Step 3 puts each coefficient in the
   image of `F`, and step 1 finishes.

## Provenance

These are standard facts: the fixed field of the Galois group of a finite
Galois extension is the base field, and the sequence `F → L → L ⊗[F] L` is
exact for a faithfully flat algebra. The Lean proofs apply Mathlib's versions
of both facts coefficientwise. The statements are derived internal helpers,
not quoted from a source. They were written for Worker 1001's torus cocharacter
detection, which descends a cocharacter datum from an extension field to the
base field. That application is in a separate module; this module states only
the coefficient facts above.
