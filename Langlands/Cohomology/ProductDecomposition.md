# Low-degree cohomology of a product decomposition

Author: Worker 226.

This module proves that cohomology in degrees one and two commutes with products, in the
following form. Let `k` be a commutative ring, `G` a group, and `A`, `B i` (`i : ι`, any index
type) representations of `G` over `k`, all in one universe `u`. Let `p i : A ⟶ B i` be morphisms
such that:

- `hinj`: an element `a` with `(p i).hom a = 0` for every `i` is `0` (joint injectivity);
- `hsurj`: for every family `b : ∀ i, B i` there is `a` with `(p i).hom a = b i` for every
  `i` (joint surjectivity).

So `A` is the product of the `B i`, possibly infinite. Cohomology is Mathlib's ordinary
`groupCohomology`.

## Definitions and statements

- `productMap p n : groupCohomology A n → ∀ i, groupCohomology (B i) n` sends a class `c` to
  the family of its images under `groupCohomology.map (MonoidHom.id G) (p i) n`.
- `productMap_bijective_one hinj hsurj` and `productMap_bijective_two hinj hsurj`:
  `productMap p 1` and `productMap p 2` are bijective.
- `productEquiv hinj hsurj n hn`, for `n = 1 ∨ n = 2`, is the resulting equivalence
  `groupCohomology A n ≃ ∀ i, groupCohomology (B i) n`.

Supporting lemmas: `exists_H1π_eq` and `exists_H2π_eq` (every class is the class of a
cocycle); `compCocycles₁`, `compCocycles₂` (composing a cocycle with a morphism);
`map_H1π`, `map_H2π` (the induced map on classes is the class of the composite, from
Mathlib's `H1π_comp_map` and `H2π_comp_map`); `eq_of_forall_hom_eq`.

## Proofs

Injectivity (degree one). If the image of the class of a cocycle `x` vanishes in every
factor, then each `p i ∘ x` is a coboundary `g ↦ g • b i - b i`. Joint surjectivity gives
`a` with `(p i).hom a = b i`. Then `g • a - a` and `x g` have the same image in every factor,
so they are equal by joint injectivity, and `x` is a coboundary. Injectivity of the additive
map `productMap p 1` follows from triviality of its kernel.

Surjectivity (degree one). Given classes `c i`, choose cocycles `y i` representing them. For
each `g`, joint surjectivity gives `x g` with `(p i).hom (x g) = y i g`. The cocycle identity
for `x` holds because it holds after applying every `p i`. The class of `x` maps to `c`.

Degree two is the same with cochains `G → B i` and the differential
`(g, h) ↦ g • f h - f (g * h) + f g` (`d₁₂_hom_apply`); joint surjectivity is applied
pointwise in `g` (resp. `(g, h)`).

## Cardinalities

For a family of types `X i`:

- `restrictPi s` restricts a dependent function to a finite set `s` of indices. It is
  bijective when every `X i` is nonempty and `X i` is a subsingleton for `i ∉ s`
  (`restrictPi_bijective`).
- `natCard_pi_eq_prod`: in that situation `Nat.card (∀ i, X i) = ∏ i ∈ s, Nat.card (X i)`.
- `finite_pi`: if moreover `X i` is finite for `i ∈ s`, the product is finite.

These apply to the cohomology groups, which are nonempty (they contain `0`).

## Provenance

This is internal infrastructure. It is the low-degree case of the standard fact that group
cohomology commutes with products of modules. Artin–Tate (*Class Field Theory*, 2009, source
`artin-tate-2009-class-field-theory`, Chapter V §2, printed p.12, PDF p.21) uses it as
`Hʳ(U) ≈ ∏_p Hʳ(G_p, U_p)` for the product of the semilocal unit groups. The proof here is
an explicit cocycle argument; it does not use Mathlib's categorical products.
