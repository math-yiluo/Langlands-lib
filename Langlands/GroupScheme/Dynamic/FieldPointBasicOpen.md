# Spectra of algebras over a field, and rational points in opens of `Spec (B ⊗ L)`

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It supplies the
point-set input for the step where a point is translated by an element of
`G(k)`. Everything is derived here from Mathlib (prime spectra, pullbacks of
schemes, residue fields) and from the Corepresented point API; no external
statement is quoted.

`k` is a field throughout.

## Spectra of `k`-algebras

- `algOver k A`: `Spec A` as an object of `Over (Spec k)`, via
  `Spec (algebraMap k A)`.
- `algOverHom φ : algOver k A' ⟶ algOver k A`: the spectrum of a `k`-algebra map
  `φ : A → A'`. `specMap_comp_specMap_algebraMap` gives its compatibility with
  the structure maps.
- `algOverHom_comp` and `algOverHom_id`: functoriality.
- `exists_eq_algOverHom`: every morphism `algOver k A' ⟶ algOver k A` is
  `algOverHom φ` for a `k`-algebra map `φ` (`Spec` is fully faithful).
- `algOverHom_comp_ofAlgHom`: for a corepresented group `G = Spec B`,
  precomposing the point `ofAlgHom ψ` with `algOverHom φ` gives
  `ofAlgHom (φ ∘ ψ)`.

## Field points in an open of an affine scheme

- `exists_ne_zero_range_subset O hO hne`: for a commutative ring `R` and a
  nonempty open `O` of `Spec R`, there is a nonzero `f ∈ R` such that for every
  field `L` and every ring map `φ : R → L` with `φ f ≠ 0`, the image of
  `Spec L → Spec R` lies in `O`. Proof: the basic opens form a basis, so some
  `D(f)` containing a point of `O` lies inside `O`, and `f ≠ 0` because `D(0)` is
  empty. The image of `Spec φ` is the prime `ker φ`, since the only prime of `L`
  is `0`. It lies in `D(f)` exactly when `φ f ≠ 0`.
- `evalMap L a : L ⊗[k] B → L` for a `k`-algebra `B`, a field extension `L` and a
  `k`-point `a : B → k` is `l ⊗ b ↦ l · a(b)`. `evalMap_tmul` records the
  formula. `evalMap_apply` writes it as `L ⊗ a` followed by
  `L ⊗[k] k ≅ L` (`TensorProduct.rid`).

## Lifting a field point along a surjection

- `exists_lift_of_surjective q x`: let `q : Y ⟶ Q` be a morphism over `Spec k`
  with surjective underlying map, and `x : Spec L ⟶ Q` with `L` a nonzero
  `k`-algebra. Then there are a field `K'` with a `k`-algebra structure, a
  `k`-algebra map `β : L → K'` and a point `y : Spec K' ⟶ Y` with
  `x ∘ Spec β = q ∘ y`. Proof: choose a point of `Spec L`. The first projection
  of `Spec L ×_Q Y` is surjective (`Scheme.Pullback.range_fst`), so the point
  has a preimage `v`. Take `K'` the residue field at `v`, with the
  `k`-structure induced by `Spec κ(v) → Spec L → Spec k`. `β` is the ring map of
  the first projection composed with `Spec κ(v) → Spec L ×_Q Y`, and `y` is the
  second projection composed with the same map. The equation is the pullback
  square.
