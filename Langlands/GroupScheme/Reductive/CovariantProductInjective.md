# Injectivity of products of left-covariant coordinates

Worker 1330 derives this internal result from standard Hopf-algebra
identities. It is an algebraic criterion for the injectivity of multiplication
of left-covariant coordinates. Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, third enlarged edition (1994), Appendix to Chapter 1, Section A,
printed p.192, asserts that the torus-invariant regular functions form an
increasing union of *copies* of tensor squares of section modules. That page
does not argue why the relevant multiplication maps are injective. The
reconstruction below is the author's own and is not taken from that page. In it
the section modules are modelled by left-covariant coordinate subspaces, and the
geometric input is an explicit hypothesis: the coordinate comorphism of
`(p, q) ↦ i(p) i'(q)⁻¹` is injective. For a Borel subgroup and its opposite, this
hypothesis expresses the standard density of the big cell. The file assumes no
Borel subgroup, opposite cell, line bundle, irreducibility or exhaustion
statement, and it proves none of these.

## Setting

Let `k` be a field and `A` a commutative Hopf algebra over `k`; it plays the
role of the coordinate algebra of an affine group `G`. Let `C`, `D` and `R` be
commutative `k`-algebras. A `k`-algebra map `A → R` is an `R`-valued point.
Mathlib's convolution product `toConv f * toConv g`, applied to `a`, sums
`f(a₁) g(a₂)` over the coproduct of `a`. It is the pointwise product of points.

## Convolution identities

- `id_convMul_antipodeAlgHom` states `id * S = 1`: the convolution of the
  identity map of `A` with the antipode algebra map `S`, in that order, is the
  convolution unit. Thus `S` is a right convolution inverse of the identity.
  Mathlib's `AlgHom.antipode_id_cancel` gives the other order, `S * id = 1`.
  This lemma follows from Mathlib's linear identity
  `LinearMap.id_mul_antipode`.
- `comp_convOne` states that composing an algebra map `f : A → R` with the
  convolution unit gives the convolution unit.
- `antipode_convMul_self` and `self_convMul_antipode` state that `f ∘ S`, with
  `S` the antipode, is a left and a right convolution inverse of `f`. Both
  apply `f` to one of the two identities above, using Mathlib's
  `AlgHom.comp_convMul_distrib`.
- `self_convMul_antipode_convMul` states the cancellation
  `f * ((f ∘ S) * g) = g`.
- `map_comp_comulAlgHom` states that `(f ⊗ g) ∘ Δ`, for `f : A → C` and
  `g : A → D`, is the convolution of `f` and `g` after including them into
  `C ⊗ D`. `productMap_comp_comulAlgHom` states that the multiplication map of
  `f, g : A → R` composed with `Δ` is their convolution. Both are checked on
  pure tensors.

## Covariance splits off the weight

For an algebra map `r : A → C` and `χ ∈ C`, the existing
`leftCovariantSubspace r χ` consists of the `f` with `(r ⊗ id)(Δ f) = χ ⊗ f`.
For points this means `f(i(p) z) = χ(p) f(z)`.
`convMul_apply_of_mem_leftCovariantSubspace` states the algebraic form: for such
`f`, every algebra map `p : C → R` and every point `w : A → R`, the convolution
of `p ∘ r` and `w`, applied to `f`, equals `p(χ) · w(f)`. The proof writes
`(p ∘ r) ⊗ w` as `(p ⊗ w) ∘ (r ⊗ id)` and substitutes the covariance equation.

## Shear maps

`shearComorphism : A ⊗ A → A ⊗ A` is the multiplication map of `Δ` and the
right inclusion. It is the comorphism of `(a, y) ↦ (a y, y)`.
`unshearComorphism` is the multiplication map of `ι₁ * (ι₂ ∘ S)` and `ι₂`,
where `ι₁` and `ι₂` are the two inclusions and `*` is convolution. It is the
comorphism of `(x, y) ↦ (x y⁻¹, y)`. `unshear_comp_shear` states that
`unshearComorphism ∘ shearComorphism` is the identity. On `a ⊗ b` it uses
`ι₁ * (ι₂ ∘ S) * ι₂ = ι₁`. Hence `shearComorphism_injective`.

## The difference comorphism and the main theorem

For algebra maps `r : A → C` and `s : A → D`,
`differenceComorphism r s : A → C ⊗ D` is `(r ⊗ (s ∘ S)) ∘ Δ`. It is the
comorphism of `(p, q) ↦ i(p) i'(q)⁻¹` when `r` and `s` are restrictions to
subgroups through `i` and `i'`. Its injectivity says that the products
`i(p) i'(q)⁻¹` are schematically dense in `G`.

`coordinateProduct_injective` takes subspaces `V ≤ leftCovariantSubspace r χ`
and `W ≤ leftCovariantSubspace s ψ`, with `χ ∈ C` and `ψ ∈ D` arbitrary, and
assumes that `differenceComorphism r s` is injective. It concludes that the
existing multiplication map `coordinateProduct V W : V ⊗ W → A` is injective.

The proof works in `(C ⊗ D) ⊗ A`. It uses the two points `p_C ∘ r` and
`p_D ∘ s`, where `p_C` and `p_D` include `C` and `D`, and the inclusion
`Z : A → (C ⊗ D) ⊗ A`. Write `Q' = p_D ∘ s ∘ S` and `Y = Q' * Z`. Let `E` be
`(differenceComorphism r s ⊗ id) ∘ shearComorphism`.

1. `(differenceComorphism r s ⊗ id) ∘ Δ` equals `(p_C ∘ r) * Y`, by
   `map_comp_comulAlgHom`, `AlgHom.comp_convMul_distrib` and associativity.
2. `Z = (p_D ∘ s) * Y`, by `self_convMul_antipode_convMul`.
3. For `v ∈ V` and `w ∈ W`, `E(v ⊗ w)` is the product of the first map at `v`
   and `Z(w)`. By the covariance lemma applied to steps 1 and 2, this equals
   `p_C(χ) p_D(ψ) Y(v w)`. Pointwise, this is the identity
   `F(i(p) i'(q)⁻¹ z, z) = χ(p) ψ(q) (Σ f_j f'_j)(i'(q)⁻¹ z)`.
4. Hence `E` composed with `V ⊗ W → A ⊗ A` equals multiplication by
   `p_C(χ) p_D(ψ)` after `Y ∘ coordinateProduct V W`.
5. If `coordinateProduct V W` sends `F` to `0`, then `E` kills the image of
   `F` in `A ⊗ A`. Over a field every module is flat. Mathlib's
   `TensorProduct.map_injective_of_flat_flat` therefore makes
   `differenceComorphism r s ⊗ id` injective, using the hypothesis, and also
   makes `V ⊗ W → A ⊗ A` injective. With `shearComorphism_injective`, this
   gives `F = 0`.

## Scope

The theorem is purely algebraic. It is stated for an abstract commutative Hopf
algebra and algebra maps, not for actual group schemes. It does not show that
the difference comorphism is injective for any particular subgroups, such as a
Borel subgroup and its opposite. That geometric input, and any statement about
the image of the multiplication map, are left to later units.
