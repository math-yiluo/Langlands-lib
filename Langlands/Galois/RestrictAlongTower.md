# Restriction of Galois groups along a scalar tower

Let `K → F → L` be a tower of fields and let `N` be a normal intermediate field of `L/K`.
The homomorphism considered here is the composite of `AlgEquiv.restrictScalarsHom K`
and `AlgEquiv.restrictNormalHom N`, from `Gal(L/F)` to `Gal(N/K)`.

- `Langlands.FieldTheory.continuous_restrictNormalHom_of_tower` proves continuity when `L/F`
  is algebraic. The basic neighborhoods of the identity in `Gal(N/K)` are fixing subgroups
  of finite extensions `E/K` in `N`. Choose a finite set of generators of `E/K`. Their images
  generate a finite extension of `F` inside `L`, whose fixing subgroup restricts into the
  given neighborhood.
- `Langlands.FieldTheory.restrictNormalHom_surjective_of_separableClosure_eq_bot` assumes
  that `L/F` and `N/K` are Galois and that `K` is relatively separably closed in `F`. The image
  of restriction is compact and therefore closed in the Hausdorff Krull topology. An element
  of `N` fixed by the image is fixed by `Gal(L/F)`, so it comes from `F`. Its preimage in `F`
  is separable over `K`, hence comes from `K`. The infinite Galois correspondence identifies
  the image with the whole group `Gal(N/K)`.
- `Langlands.FieldTheory.restrictNormalHom_injective_of_adjoin_eq_top` proves injectivity when
  `F` and `N` generate `L`. An element of the kernel fixes `N` pointwise and consequently
  fixes the field it generates over `F`.
- `Langlands.FieldTheory.isHomeomorph_restrictNormalHom_of_tower` combines these facts using
  compactness of `Gal(L/F)` and the Hausdorff property of `Gal(N/K)`.

These are consequences of Mathlib's Krull neighborhood basis and infinite Galois
correspondence, applied to the restriction homomorphism in the given tower.
