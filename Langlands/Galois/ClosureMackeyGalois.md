# One Mackey double coset for absolute Galois groups

This module supplies the Galois-theoretic hypotheses of Mackey's formula with
a single double coset, for restriction along explicit closure embeddings
(`restrictionAlongClosure`). It also supplies the normal subgroup used for
irreducibility.

## Transported copies and normal images

- `exists_eq_of_normal`: two `E`-embeddings of a normal extension `D/E` into
  a field have the same image.
- `transportedEmbedding ι : E → K̄` for an algebraic extension `E/K` and a closure
  embedding `ι : K̄ → Ē`. It is the copy of `E` in `K̄` given by `ι⁻¹`, and
  `ι` is bijective by `closureEmbedding_bijective`.
  `mem_range_restrictionAlongClosure_iff`: the image of the restriction along `ι` is
  the subgroup of `Gal(K̄/K)` that fixes this copy pointwise.
- `range_restrictionAlongClosure_normal`: if `D/E` is normal, the image of the
  absolute group of `D` is normal in that of `E`. Conjugation moves the copy
  of `D` to another embedding of `D`, which has the same image.

## Product decomposition

`exists_mul_of_galois_mul`: let `E'/E` be algebraic, and let `E'` and `D` lie
in a normal extension `L/E` with `D/E` normal and `L/E'` algebraic. Suppose
every element of `Gal(L/E)` is a product `a b` with `a` fixing `D` and `b`
fixing `E'`. Then every element of the absolute group of `E` is a product
`r h` with `r` in the image `R` of the absolute group of `D` (along `eD`) and
`h` in the image `H` of the absolute group of `E'` (along `e`).

For the proof, extend the copy of `E'` in `Ē` to an `E`-embedding `λ` of `L`.
Restrict `g` to `σ ∈ Gal(L/E)` through `λ`, decompose `σ = a b`, and lift `a`
and `b` to `â, b̂ ∈ Gal(Ē/E)` (`AlgEquiv.liftNormal`). Then `â` fixes the copy
of `D`, because `λ(D)` is that copy by normality. The element
`k = (â b̂)⁻¹ g` fixes `λ(L)`, so `b̂ k` fixes the copy of `E'`, and
`g = â · (b̂ k)`.

## The comparison element

For a compositum situation with towers `E ⊆ D ⊆ M` and `E ⊆ E' ⊆ M` and
closure embeddings `e : Ē → Ē'`, `eD : Ē → D̄`, `eM : D̄ → M̄` and
`ej : Ē' → M̄`, `mackeyElement e eD eM ej` is the element `x` of `Gal(Ē/E)`
with `ej ∘ e ∘ x = eM ∘ eD` (`closureChange`).

- `mackeyElement_conj`: `x · r_D(r_M(y)) · x⁻¹ = r_{E'}(r_j(y))` for `y` in
  the absolute group of `M`. This follows from `closureChange_intertwines` and
  `restrictionAlongClosure_comp`.
- `fixes_closureCopy_of_conj_mem` and `mem_range_of_conj_mem`: if
  `x · r_D(ℓ) · x⁻¹ ∈ H`, then `ℓ` fixes the copy of the image of `E'` in `D̄`.
  If moreover `D`-algebra maps out of `M` are determined on `E'`, then `ℓ`
  lies in the image of the absolute group of `M`.

## Cosets

`exists_mul_mul_of_mul_cover`: in a group `G` with subgroup `H` and a
homomorphism `ι : Γ → G` with normal image, if `G = ι(Γ) · H`, then every
element of `G` lies in `H · x · ι(Γ)` for every `x`. So there is one double
coset.

## The normal subgroup from a normal extension

For a tower `D ⊆ M ⊆ L` with `L/D` normal and closure embeddings
`eM : D̄ → M̄` and `κ' : M̄ → L̄`, `closureThroughM eM κ'` is the composite
`D̄ → L̄`.

- `closureTransport eM κ' g` transports `g ∈ Gal(D̄/D)` to an automorphism of
  `L̄` over `D`. `restrictedTransport eM κ' g` is its restriction to the normal
  extension `L`.
- `transportConj eM κ' g x` is the conjugate of `x ∈ Gal(L̄/L)` by the
  transported automorphism, and
  `conj_restrictionAlongClosure_closureThroughM` gives
  `g⁻¹ · r(x) · g = r(transportConj g x)`.
- `range_restrictionAlongClosure_closureThroughM_normal`: the image of the
  absolute group of `L` in that of `D` is normal.
  `range_closureThroughM_le`: it lies in the image of the absolute group of
  `M`.
- `mem_range_of_restrictedTransport_fixes`: if the restricted transport of `g`
  fixes `M` pointwise, then `g` comes from the absolute group of `M`.

These are the group-theoretic facts used to restrict the monomial
representation over `D` to the absolute group of `L` in the proof of
Harris 1998, Proposition 4.8 (`harris-1998-local-langlands`, pp. 202–203).
