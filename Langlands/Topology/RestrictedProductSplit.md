# Splitting a cofinite restricted product along a predicate on the indices

This internal construction splits Mathlib's cofinite restricted product
`Πʳ i, [R i, A i]` along a decidable predicate `p` on the index type `ι`. The
result is the product of the cofinite restricted products over the subtype
`{i // p i}` and over the subtype `{i // ¬ p i}`. When only finitely many
indices satisfy `p`, the first factor is the full product `Π i : {i // p i}, R i`.

## Construction

- `restrictSubtype R A q` restricts a family to the indices of `{i // q i}`. It
  is Mathlib's `RestrictedProduct.mapAlong` along the injective map
  `Subtype.val`, so preimages of finite sets are finite. The coordinate maps are
  identities.
- `glueSubtype R A p x y` glues a family `x` over `{i // p i}` and a family `y`
  over `{i // ¬ p i}`. At `i` it takes the value `x ⟨i, h⟩` if `h : p i` and
  `y ⟨i, h⟩` otherwise. The indices where it lies outside `A i` form a subset
  of the union of the images of two finite sets, so they are finitely many. The lemmas `glueSubtype_apply_of_pos` and
  `glueSubtype_apply_of_neg` give its coordinates.
- `splitEquiv R A p` is the equivalence
  `Πʳ i, [R i, A i] ≃ Πʳ (i : {i // p i}), [R i, A i] × Πʳ (i : {i // ¬ p i}), [R i, A i]`.
  It sends `x` to its two restrictions, and its inverse is `glueSubtype`.
  `splitEquiv_apply_fst`, `splitEquiv_apply_snd` and `splitEquiv_symm_apply`
  describe it. `forall_mem_iff_splitEquiv` says that a family lies in every
  `A i` exactly when both of its parts do.

## Topology

The topology on each restricted product is Mathlib's.

- `continuous_restrictSubtype` is `RestrictedProduct.mapAlong_continuous`.
- `continuous_glueSubtype` assumes that every `A i` is open. It uses Mathlib's
  universal properties with parameters, `continuous_dom_prod_right` and
  `continuous_dom_prod_left`. These reduce continuity of gluing to its
  restriction to `Πʳ [R i, A i]_[𝓟 S] × Πʳ [R i, A i]_[𝓟 T]` for cofinite sets `S`
  of `{i // p i}` and `T` of `{i // ¬ p i}`. There the glued family lies in
  `Πʳ i, [R i, A i]_[𝓟 U]`, where `U` is the set of indices whose subtype point
  lies in `S` or in `T`. This set `U` is cofinite. Continuity into the principal
  restricted product is checked coordinatewise with
  `continuous_rng_of_principal_iff_forall`. Each coordinate is a coordinate
  evaluation composed with a product projection. Finally Mathlib's continuous
  `inclusion` takes the result into the cofinite restricted product.
- `splitHomeomorph R p hA` bundles `splitEquiv` as a homeomorphism, under the
  hypothesis `hA : ∀ i, IsOpen (A i)`.
- `finiteHomeomorph R A` assumes `[Finite ι]`. It is the homeomorphism
  `Πʳ i, [R i, A i] ≃ₜ Π i, R i` given by coercion to functions. Its inverse
  composes Mathlib's `homeoBot` with `inclusion` along `cofinite_eq_bot`.
- `splitFiniteHomeomorph R p hA` assumes `[Finite {i // p i}]` and open `A i`. It
  is the homeomorphism
  `Πʳ i, [R i, A i] ≃ₜ (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, A i]`,
  obtained by composing `splitHomeomorph` with `finiteHomeomorph` on the first
  factor. Its coordinates and those of its inverse are given by the `apply_fst`,
  `apply_snd`, `symm_apply_of_pos` and `symm_apply_of_neg` lemmas.

## Monoids and groups

Let `B i` be submonoids, or more generally members of a `SubmonoidClass`, of
monoids `R i`. Multiplication on the restricted products is pointwise, as in
Mathlib.

- `splitMulEquiv R B p` is `splitEquiv` as a multiplicative equivalence.
- `splitContinuousMulEquiv R B p hB` is `splitEquiv` as an isomorphism of
  topological monoids, when every `B i` is open.
- `finiteContinuousMulEquiv R B` assumes `[Finite ι]`. It is `finiteHomeomorph`
  as an isomorphism of topological monoids.
- `splitFiniteContinuousMulEquiv R B p hB` assumes `[Finite {i // p i}]` and open
  `B i`. It is the isomorphism of topological monoids
  `Πʳ i, [R i, B i] ≃ₜ* (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i]`.

Each of these has `apply` lemmas, and the splittings have `symm_apply_of_pos`
and `symm_apply_of_neg` lemmas for the inverse. For groups and subgroups these
are isomorphisms of topological groups. In every case multiplicativity holds
by definition, because both sides multiply coordinatewise.

## Scope and provenance

The construction is internal and derived from Mathlib's restricted-product API.
It uses `mapAlong`, `inclusion`, `homeoBot`, `continuous_inclusion`,
`continuous_eval`, `continuous_dom_prod_right`, `continuous_dom_prod_left`,
`continuous_rng_of_principal_iff_forall` and `mapAlong_continuous`. Mathlib
does not provide this splitting at the pinned commit. The only hypotheses are
openness of the restricting subsets for the topological statements and
finiteness of `{i // p i}` for the finite forms. No local compactness,
compactness or countability is assumed. The module is purely topological and
group-theoretic. Its adelic use is the module
`Langlands.Global.FiniteAdelicGL.SplitAtPlaces`.
