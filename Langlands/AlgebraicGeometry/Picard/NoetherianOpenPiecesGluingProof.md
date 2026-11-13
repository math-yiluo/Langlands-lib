# Proof of the gluing of a Zariski sheaf from quasi-projective open pieces

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluingProof` proves

```lean
theorem noetherianOpenPiecesGluing : NoetherianOpenPiecesGluingStatement.{u}
```

Let `A` be a noetherian ring, `S = Spec A`, and let `F` be a Zariski sheaf on `Over S` with
opens `V T ξ c m`, schemes `Q c m` and maps `β c m` satisfying the five hypotheses of the
statement. The proof glues the `Q c m` along open immersions into one `S`-scheme `P`, glues their
universal elements into an element `ξP` of `F(P)`, and shows that `g ↦ F(g)(ξP)` is a bijection
`Hom_S(T, P) → F(T)` for every locally noetherian `T`. It follows the statement's sources
(Stacks 01JJ; Kleiman, *The Picard scheme*, pp.28–29, citing EGA 0 4.5.4), but uses Mathlib's
colimits of locally directed diagrams of open immersions (`Mathlib.AlgebraicGeometry.Gluing`)
in place of gluing data. All auxiliary declarations live in the namespace
`Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluing`.

## Indexing and bundled data

- `Idx κ` is `κ × ℕ` with the preorder `(c, m) ≤ (c', m')` iff `c = c'` and `m ≤ m'`;
  `Idx.mk c m` is the index `(c, m)`. As a category it is thin and small.
- The structure `Data A` bundles the hypotheses (`F`, `hF`, `κ`, `V`, `Q`, `β`, `base`,
  `shape`, `imm`, `rep`) verbatim. `QI i = Q i.1 i.2` and `VI T ξ i = V T ξ i.1 i.2`.

## The pieces

- Each `Q i` admits an immersion into `ℙⁿ_A` over `A`, so its structure map is locally of finite
  type (`locallyOfFiniteType_hom`), hence locally of finite presentation over the noetherian
  base; `Q i` is locally noetherian (`isLocallyNoetherian_QI`); and `Q i` has finite affine
  neighbourhoods by the Library lemma
  `PointTopology.hasFiniteAffineNeighborhoods_of_projectiveImmersion`.
- `x i ∈ F(Q i)` is the element corresponding to `β i` under `uliftYonedaEquiv`. Then
  `β i` sends `g : T ⟶ Q i` to `F(g)(x i)` (`β_app`). Hypothesis `rep` translates into:
  for locally noetherian `T`, `g ↦ F(g)(x i)` is injective (`map_x_injective`), and `ξ ∈ F(T)`
  is of this form iff `VI T ξ i = ⊤` (`exists_map_x`, `V_map_x`). In particular
  `VI (Q i) (x i) i = ⊤` (`V_x_self`), and by monotonicity in `m` (`V_mono`),
  `VI (Q i) (x i) j = ⊤` whenever `i ≤ j` (`V_x_of_le`).

## Transition maps

For `i ≤ j`, `τ h : Q i ⟶ Q j` is the map chosen with `F(τ h)(x j) = x i` (`map_τ_x`); it
exists by `V_x_of_le`. Injectivity gives `τ_id` and `τ_comp`, so `diagram : Idx κ ⥤ Over S` is
a functor.

`isOpenImmersion_τ`: `(τ h).left` is an open immersion. Let `W = VI (Q j) (x j) i`, an open of
`Q j`, viewed as an `S`-scheme `Wτ h` with inclusion `ιWτ h`.

1. By `base` and `map_τ_x`, `(τ h)⁻¹ W = VI (Q i) (x i) i = ⊤` (`preimage_τ`), so `τ h`
   factors as `g' ≫ ιWτ h` through `W` (`IsOpenImmersion.lift`).
2. By `base`, the restriction `y` of `x j` to `W` has `VI W y i = ⊤` (`VI_Wτ`), so `y = F(k)(x i)`
   for some `k : W ⟶ Q i`.
3. Injectivity gives `k ≫ τ h = ιWτ h` and then `g' ≫ k = 𝟙`; since `ιWτ h` is a monomorphism,
   `k ≫ g' = 𝟙`. So `g'` is an isomorphism and `(τ h).left = g'.left ≫ W.ι` is an open immersion.

## The glued scheme

- `G = diagram ⋙ Over.forget S` is a diagram of open immersions (`isOpenImmersion_G`). It is
  locally directed (`isLocallyDirected`): if `x_i`, `x_j` have the same image in `Q k`, then
  `i`, `j`, `k` share the first coordinate, and the smaller of `i`, `j` (in `m`) works because
  the transition maps are injective on points.
- Mathlib then gives `colimit G`, with open immersions `colimit.ι G i`, an open cover
  `Scheme.IsLocallyDirected.openCover G` by these maps, the point criterion `ι_eq_ι_iff` and
  joint surjectivity `ι_jointly_surjective`.
- `cocone` is the cocone of structure maps `(Q i).hom` to `S`;
  `P = Over.mk (colimit.desc G cocone)` and `ι i : Q i ⟶ P` has underlying map `colimit.ι G i`.
  `τ_ι` records `τ h ≫ ι j = ι i`. If `colimit.ι G i yi = colimit.ι G j yj` then
  `i.1 = j.1` (`le_of_ι_eq`).

## Agreement

`agree`: let `O` be locally noetherian and `h₁ : O ⟶ Q i`, `h₂ : O ⟶ Q j` with
`F(h₁)(x i) = F(h₂)(x j)`. Then `h₁ ≫ ι i = h₂ ≫ ι j`.

- If `i.1 = j.1`, take `k = (i.1, max i.2 j.2)`. Injectivity at `k` gives
  `h₁ ≫ τ = h₂ ≫ τ`, and `τ_ι` concludes.
- If `i.1 ≠ j.1`, the common element `ζ` has `VI O ζ i = ⊤ = VI O ζ j`. By the disjointness in
  `shape`, `O` is empty (`isEmpty_of_ne`), and maps out of an empty scheme are equal.

## The glued element

- `eq_of_isEmpty`: `F(Z)` has at most one element when `Z.left` is empty. The empty sieve covers
  an empty scheme (`Scheme.bot_mem_grothendieckTopology`), and the sheaf condition separates.
- `isSheafFor_ofArrows`: a family `π i : Z i ⟶ T` whose underlying maps generate a Zariski
  covering sieve of `T.left` satisfies the sheaf condition for `F`. By `mem_over_iff` and
  `Sieve.overEquiv_ofArrows` this is the hypothesis `hF`.
- `compatible_x`: the family `x` is compatible along the `ι i`. If `gi ≫ ι i = gj ≫ ι j` and
  `i.1 = j.1`, cancel the monomorphism `ι k` for `k = (i.1, max)` and use `map_τ_x`. If
  `i.1 ≠ j.1`, `le_of_ι_eq` shows that `Z.left` has no points, and `eq_of_isEmpty` applies. No
  noetherian hypothesis on `Z` is needed here.
- The maps `ι i` form a Zariski covering of `P` (Mathlib's
  `ofArrows_ι_mem_zariskiTopology_of_isColimit`), so `isSheafFor_arrows_iff` gives
  `ξP ∈ F(P)` with `F(ι i)(ξP) = x i` (`map_ι_ξP`).

## Bijectivity on locally noetherian tests

For an open `U` of `T.left`, `res T U` is `U` over `S` and `resι T U` its inclusion.

- `exists_factor` and `map_x_of_factor`: if `U ⊆ g⁻¹(range ι i)` for `g : T ⟶ P`, then
  `g` restricted to `U` factors as `a ≫ ι i`, and `F(a)(x i)` is the restriction of
  `F(g)(ξP)` to `U`.
- `map_ξP_injective`: if `F(g₁)(ξP) = F(g₂)(ξP)` with `T` locally noetherian, then `g₁ = g₂`.
  By `Scheme.hom_ext_of_forall` it suffices to compare them near each point `y`. Choose `i`, `j`
  with `g₁ y ∈ range ι i` and `g₂ y ∈ range ι j`, and let `U` be the intersection of the two
  preimages. Both maps factor through the pieces on `U`, and `agree` (with `U` locally
  noetherian) shows that their restrictions to `U` coincide.
- `exists_map_ξP`: every `ξ ∈ F(T)` with `T` locally noetherian is `F(g)(ξP)` for some `g`. The
  opens `U i = VI T ξ i` cover `T` (by `shape`, using `iSup_prod`). On `U i`, the restriction of
  `ξ` has `VI = ⊤` by `base`, so it is `F(k i)(x i)` for some `k i : U i ⟶ Q i`. The maps
  `k i ≫ ι i` agree on the overlaps `U i ×_T U j`, which are locally noetherian (`agree`, using
  `pullback.condition`). They glue (`Scheme.Cover.glueMorphisms`) to `g₀ : T.left ⟶ P.left`.
  `g₀` is a morphism over `S` by `Scheme.Cover.hom_ext`, giving `g : T ⟶ P`. Finally
  `F(g)(ξP)` and `ξ` have the same restriction to every `U i` (`map_x_of_factor`), so they are
  equal because `F` is separated for this cover.

## The remaining properties of `P`

- `locallyOfFinitePresentation_P`: being locally of finite presentation is local on the source
  (`HasRingHomProperty.instIsZariskiLocalAtSource`). On the cover by the `colimit.ι G i`, the
  composite with `colimit.desc` is `(Q i).hom` (`colimit.ι_desc`), which is locally of finite
  presentation.
- `hasFiniteAffineNeighborhoods_P`: for `c : κ` let `Uc c = ⨆ m, range (ι (c, m))`. These opens
  cover `P` (`ι_jointly_surjective`) and are pairwise disjoint (`le_of_ι_eq`), so the Library
  lemma `PointTopology.hasFiniteAffineNeighborhoods_of_disjoint_openCover` reduces to each
  `Uc c`. Inside `Uc c`, the preimages of `range (ι (c, m))` increase with `m`
  (`opensRange_mono`, from `τ_ι`) and cover, so
  `PointTopology.hasFiniteAffineNeighborhoods_of_directed_openCover` reduces to each of them.
  Each preimage maps to `Q (c, m)` by an open immersion: the lift through `ι (c, m)`, which is
  an open immersion by `IsOpenImmersion.of_comp`. So it has finite affine neighbourhoods by
  `PointTopology.hasFiniteAffineNeighborhoods_of_isOpenImmersion`.

## Conclusion

`bijective_app`: for a noetherian affine test `T`, `IsNoetherian T.left` gives
`IsLocallyNoetherian T.left`. So the map `ULift (T ⟶ P) → F(T)`, `g ↦ F(g)(ξP)`, is bijective
by the two previous lemmas. `isoNoeth` assembles these bijections into a natural isomorphism
`(noetherianAffineOverι S).op ⋙ yoneda.obj P ⋙ uliftFunctor ≅ (noetherianAffineOverι S).op ⋙ F`
(`NatIso.ofComponents`). Naturality is functoriality of `F`. The theorem
`noetherianOpenPiecesGluing` packages the hypotheses as `Data A` and returns `P` with
`locallyOfFinitePresentation_P`, `hasFiniteAffineNeighborhoods_P` and `isoNoeth`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
