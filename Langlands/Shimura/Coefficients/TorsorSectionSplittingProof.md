# Geometric torsor splitting of arbitrary module-sheaf sections

Author: Worker 310.

`Langlands.Shimura.Coefficients.etaleTorsorSectionSplitting` proves exactly the
published proposition
`Langlands.Shimura.Coefficients.EtaleTorsorSectionSplittingStatement.{u}`.
The theorem retains every quantifier and the unrestricted universe `u`: an
actual scheme `X`, group `G`, action `Y` on `X.Etale`, the existing
`IsFiniteGeometricTorsor X Y`, an arbitrary commutative ring `R`, an arbitrary
`R`-module sheaf `F`, and any `U : Over Y.V`.

Writing `p = U.hom`, restriction along
`γ(g) = prod.lift (p ≫ Y.ρ g) (𝟙 U.left)` gives the bijection

```text
F(Y.V × U.left) → (G → F(U.left)).
```

The deck parameter is `g` itself. The categorical product is in `X.Etale`,
so its underlying scheme is a product over `X`. The proof imports the target
without changing its Lean/Markdown pair or any imported declaration. It does
not assume a decomposition, action-map isomorphism, section-splitting witness,
or associated-sheaf trivialization.

The implemented proof has four steps.

1. The private `etale_prod_hom_ext` transports the binary-product universal
   property through `Scheme.Etale.forget`, which preserves finite limits.
   Consequently, scheme maps into the underlying product agree whenever
   their two projections agree.
2. The private `torsor_graphs_cover` constructs a geometric point above each
   point of the product using the separable closure of its residue field.
   Projecting to `U` and then to `Y`, and separately projecting directly to
   `Y`, gives two geometric points over the same point of `X`. Existence in
   the torsor's unique-transport condition supplies `g`. The product
   universal property shows that the original geometric point factors
   through `γ(g)`. Evaluating this equality on the point of the field's
   spectrum proves joint surjectivity of the graphs. Mathlib's
   `Scheme.ofArrows_mem_smallEtaleTopology_iff` makes this a covering family.
3. The private `torsor_overlap_index_eq` considers maps from a test object
   `W` into two graphs with equal composites. The second projection makes
   the maps to `U` equal. If `W` has any point, its separably closed geometric
   lift and the first-projection equality exhibit two group elements with
   the same transport. Uniqueness in the torsor condition makes those
   elements equal. Thus distinct graphs can overlap only on a test scheme
   with empty underlying space.
4. The forgetful functor from `ModuleCat.{u} R` to `Type u` is shown privately
   to be corepresentable by the module `R`: an `R`-linear map from `R` is
   determined by its value at `1`. Mathlib's corepresentable-functor sheaf
   composition result therefore gives the underlying sheaf of sets without
   imposing larger coefficient universes. The private
   `etale_sections_eq_of_empty` applies separatedness for the empty covering
   family to show that sections over an empty test scheme are equal. Every
   group-indexed family is now compatible on the graphs: equal indices have
   equal restriction maps, while distinct indices have empty overlap.
   `Presieve.isSheafFor_arrows_iff` supplies a unique amalgamation, which
   `Function.bijective_iff_existsUnique` identifies with the required
   bijectivity.

The geometric argument uses the unique-transport conjunct of the published
predicate; its finiteness and surjectivity conjuncts remain in the theorem's
unchanged hypothesis but are not needed in this argument. No global deck
parameter is chosen on an arbitrary disconnected test scheme. The proof
works by gluing across the full graph covering family, including the empty
scheme case.

This is a derived internal proof of the existing Library target. Its
provenance is that target and the named Mathlib results; no direct claim of
following a proof from the original literature is made. The target's
connection to the associated coefficient-sheaf construction is recorded in
`TorsorSectionSplittingStatement.md`. The associated-sheaf natural
isomorphism is outside this module's claim.

Formal environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The additional direct import is
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`. The proof
uses ordinary kernel-checked terms and no new axioms or proof holes.
