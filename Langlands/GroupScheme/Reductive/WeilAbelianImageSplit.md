# Homomorphisms from a Weil restriction over split test algebras

Namespace `Langlands.GroupScheme.WeilAbelianImage`. This internal module is the third step of the
proof of `WeilAbelianImageTrivialityStatement`. It shows that a homomorphism `c` with commuting
values from `H = R_{B/A}(G')` is trivial over every `T`-algebra `X` for which `B ⊗[A] X` has a
complete orthogonal family of graph idempotents.

## The graph of an algebra map

`T` is an `A`-algebra, `X` a `T`-algebra and `φ : B →ₐ[A] X` an algebra map.

- `graphUnder X φ` (definition): `X` as a `(B ⊗[A] T)`-algebra through `b ⊗ t ↦ φ b * t`.
- `graphIsoHom X φ`, `graphIsoInv X φ` (definitions): the identity of the underlying ring, from and
  to the `A`-algebra underlying `graphUnder X φ` (its `A`-structure is `A → B → X`, equal to that of
  `X` because `φ` is an `A`-algebra map). `graphIsoInv_hom`: they compose to the identity.
- `graphUnderHom X φ` (definition): `graphIsoHom`, as a map of `T`-algebras
  `underA (graphUnder X φ) ⟶ X`.
- `lT_eq_of_isGraphIdempotent`: for an algebra map `χ : T₁ ⟶ T₂` and algebra maps
  `φ₁ : B → T₁`, `φ₂ : B → T₂` with `χ ∘ φ₁ = φ₂`, `id_B ⊗ χ` sends the graph idempotent of `φ₁` to
  that of `φ₂` (`IsGraphIdempotent.map`, `IsGraphIdempotent.unique`).

## Killing components

Assume `B` is finite, projective and étale over `A`, `G'` is an affine group scheme of finite type
over `Spec B`, reductive with semisimple geometric fibres, and the values of `c` commute.

- `app_eq_one_of_retract`: let `Z` be a `(B ⊗[A] T)`-algebra, `u : underA Z ⟶ X` a map of
  `T`-algebras and `v` a map of `A`-algebras from `X` to the `A`-algebra underlying `Z` with
  `v ≫ u = 𝟙`. If the image of a point `x` over `Z` lies in the factor cut out by the graph
  idempotent of the structure map `B → Z` (`snd` of it is `1`), then `c.app X x = 1`. Proof: that
  image `h` satisfies `h = embNat (projNat h)` (`embNat_projNat_of_snd`), so `c` kills it
  (`app_embNat_eq_one`, module `WeilAbelianImageTransfer`); `x` is the image of `h` along `u`, and
  `c` is natural.
- `app_proj_graph_eq_one`: if `e` is the graph idempotent of `φ : B → X`, then `c` kills the point
  of `H` over `X` whose image in `G'(B ⊗[A] X)` is the component `proj G' e` of the image of `x`.
  This is `app_eq_one_of_retract` with `Z = graphUnder X φ`, `u = graphUnderHom`, `v = graphIsoInv`:
  `id ⊗ v` carries `e` to the graph idempotent of the structure map of `Z`
  (`lT_eq_of_isGraphIdempotent`), and the projections commute with algebra maps (`proj_map`,
  `snd_proj`).
- `app_eq_one_of_split`: **split case.** If `B ⊗[A] X` has graph idempotents `e₁, …, eₙ` of algebra
  maps `φᵢ : B → X` that are pairwise orthogonal and sum to `1`, then `c.app X x = 1` for every
  point `x`. Apply `IdempotentPoints.map_eq_one_of_family` (module `IdempotentPointsFamily`) to `c`
  composed with the inverse of `AffineWeil.pointsEquiv`, using `app_proj_graph_eq_one` for each `i`.

## Provenance

Internal. Suppose `B ⊗_A X ≅ X^n`, with `φᵢ : B → X` the composite of this isomorphism with the
`i`-th coordinate projection; equivalently, `Spec(B ⊗_A X)` is the disjoint union of `n` copies of
`Spec X`, the `i`-th one mapping to `Spec B` by `Spec φᵢ`. Then the Weil restriction `H_X` is the
product over `i` of the pullbacks `(Spec φᵢ)^* G'` of `G'` along these maps. These pullbacks can
be different groups: over `B = X × X`, a group `G'` that is `PGL₂` on one component and `PGL₃` on
the other gives `H_X = PGL₂ × PGL₃`. This is the split computation in Conrad, *Reductive group
schemes* (2014), proof of Proposition 6.4.4, p. 232: for `S' = ∐_{i ∈ I} S` and `G' = ∐ Gᵢ`, one
has `R_{S'/S}(G') = ∏ Gᵢ`. Remark 6.4.5 (p. 233) applies the same argument in the adjoint case.

The Lean proof does not form this product decomposition. For each `i` separately, it puts the
`B`-algebra structure `φᵢ` on `X` (`graphUnder X (φ i)`) and identifies the component of a point
at the graph idempotent of `φᵢ` with a diagonal-factor point for that structure
(`app_proj_graph_eq_one`). The diagonal factor is treated in `WeilAbelianImageTransfer`. Then a
point is the product of its components (`IdempotentPoints.map_eq_one_of_family`).
