# Support subquotients of `r_Q^G ∘ i_P^G` for represented parabolics (Renard VII.3.2)

Author: Worker 6. Module `Langlands.Representation.Intertwining.PQSupportGradedStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. The module contains one **statement**: the closed `Prop`-valued definition `PQSupportGradedStatement` (universe parameters `u, v`). It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated **9 July 2026**:

- VII.3.2 "Filtrations", the four support subspaces, their images, the inclusions, the two isomorphisms of subquotients and the identity case, printed p.233 / PDF p.239;
- VII.3.1, the Bruhat order and the total order `⪯` refining it, printed pp.232–233 / PDF pp.238–239;
- VI.5.1, the geometric lemma, from printed p.161 / PDF p.167.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 6 read PDF pages 238–239.

`P` and `Q` are two parabolic subgroups of `G` with the same Levi factor `M`, and `⪯` is a total order on the double cosets that refines the Bruhat order `w̄ ≤ w̄'` (`P w̄ Q ⊂ closure (P w̄' Q)`). For a smooth representation `(ρ, W)` of `M`, Renard defines four subspaces of `i_P^G(W)`: `F̃^{⪯w̄}_{PQ}(W)` and `F̃^{≺w̄}_{PQ}(W)`, the functions whose support does not meet `⋃_{w̄' ⪯ w̄} P w̄' Q`, respectively `⋃_{w̄' ≺ w̄} P w̄' Q`; `F̃^{<w̄}_{PQ}(W)`, those with `Supp(f) ∩ closure (P w̄ Q) ⊂ P w̄ Q`; and `F̃^{≤w̄}_{PQ}(W)`, those with `Supp(f) ∩ closure (P w̄ Q) = ∅`. Their images in `r_Q^G i_P^G(W)` are `F^{⪯w̄}_{PQ}`, `F^{≺w̄}_{PQ}`, `F^{<w̄}_{PQ}`, `F^{≤w̄}_{PQ}`. Renard then states:

- "Remarquons que l'on a alors toujours : `F̃^{⪯w̄} ⊂ F̃^{≺w̄}`, `F̃^{≺w̄} ⊂ F̃^{<w̄}`, `F̃^{≤w̄} ⊂ F̃^{<w̄}`."
- "Il est clair que `F^{≺w̄}/F^{⪯w̄} ≃ F^{<w̄}/F^{≤w̄}` et lemme géométrique se reformule en `F^{≺w̄}/F^{⪯w̄} ≃ i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{w·Q∩M}`."
- "Pour l'élément `1̄`, ceci donne `F^{≺1̄}/F^{⪯1̄} ≃ F^{<1̄}/F^{≤1̄} ≃ Id_{M(M)}`", the identity functor of the category of smooth representations of `M`. In other words, `ρ` appears as a subquotient of `r_Q^G ∘ i_P^G(ρ)`.

## Published objects used

From [PQRegularity](PQRegularity.md) (module `Langlands.Representation.Intertwining.PQRegularity`):

- `parabolicDoubleCosets p q`, the actual double cosets `P(F) \ G(F) / Q(F)`, and `identityParabolicDoubleCoset p q`, Renard's `1̄`;
- `Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o`, which says that the linear order `o` extends the Bruhat relation (closure containment of double cosets);
- the subfunctors of `i_P^G(-)` restricted to `Q(F)`: `initialVanishingSubfunctor … o w` (`F̃^{⪯w}`), `strictInitialVanishingSubfunctor … o w` (`F̃^{≺w}`), `boundaryVanishingSubfunctor … w` (`F̃^{<w}`) and `closureVanishingSubfunctor … w` (`F̃^{≤w}`), written as vanishing conditions on `⋃_{w' ⪯ w} P w' Q`, `⋃_{w' ≺ w} P w' Q`, `closure (P w Q) \ P w Q` and `closure (P w Q)`;
- their images in `r_Q^G ∘ i_P^G`: `initialSupportImage … o w`, `strictInitialSupportImage … o w`, `boundarySupportImage … w` and `closureSupportImage … w`, subfunctors (`RepSubfunctor`) of the published `leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ`, which goes from `SmoothRep.{0, u, v} ℂ (rationalPoints M)` to `Rep.{max u v} ℂ (rationalPoints M)`.

From [Definitions](../Filtration/Definitions.md) (module `Langlands.Representation.Filtration.Definitions`), for subfunctors `S` and `T`: `S.quotientFunctor T` is the successive-quotient functor whose value at `W` is `S.quotientObj T W`, the quotient of `T(W)` by `S(W) ∩ T(W)`. `S.quotientMap T f` is the map induced on these quotients by a morphism `f`. So `(initialSupportImage … o w).quotientFunctor (strictInitialSupportImage … o w)` is Renard's `F^{≺w}/F^{⪯w}`, and `(closureSupportImage … w).quotientFunctor (boundarySupportImage … w)` is his `F^{<w}/F^{≤w}`.

From [RepresentedGeometricLemmaStatement](../Geometric/RepresentedGeometricLemmaStatement.md): `GeometricLemmaIntersectionDatum p l r … q lQ rQ … z`, the intersection data at a point `z` of `G(F)`, and its `pieceFunctor`. With `L = M` the piece is `i^M_{Q'} ∘ ι ∘ r^M_{P'}` with `P' = M ∩ z·Q` and `Q' = M ∩ z⁻¹·P`. This is Renard's `i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{w·Q∩M}` for `w = z`. It has the same source and target as `leviJacquetInductionFunctor`.

From [Basic](../Category/Basic.md): `SmoothRep`, its `representation`, and `SmoothRep.hom f`, the equivariant linear map underlying a morphism `f`.

## Lean statement

`PQSupportGradedStatement` quantifies over:

- a nonarchimedean local field `k : Type u` (`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`) and a connected reductive `G` over `Spec k`, with the canonical topology on `G(F)`, and `[LocallyCompactSpace (rationalPoints G)]`, `[NonarchimedeanGroup (rationalPoints G)]`;
- represented parabolics `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`) and `Q = MU` (`q`, `lQ`, `rQ` with `hq`, `hlQ`, `hrQ`, `hmulQ`) that share the Levi scheme `M`;
- a proof of `l ≫ p = lQ ≫ q`: the two Levi embeddings of `M` in `G` agree, so `M` is a common Levi factor of `P` and `Q`, as in Renard.

The topology on `M(F)` is the published `leviPointTopology l hl`. The conclusion has two conjuncts.

**First conjunct.** For every linear order `o` on `parabolicDoubleCosets p q` with `IsBruhatRefinement … o`, and every double coset `w`, three things hold:

1. **Inclusions.** At every `W : SmoothRep.{0, u, v} ℂ (rationalPoints M)`, as subrepresentations: `F̃^{⪯w}(W) ≤ F̃^{≺w}(W)`, `F̃^{≺w}(W) ≤ F̃^{<w}(W)` and `F̃^{≤w}(W) ≤ F̃^{<w}(W)`.
2. **Comparison of subquotients.** `Nonempty (F^{≺w}/F^{⪯w} ≅ F^{<w}/F^{≤w})`, a natural isomorphism of functors to `Rep.{max u v} ℂ (rationalPoints M)`.
3. **Reformulated geometric lemma.** For every `z : rationalPoints G` with `DoubleCoset.mk (pointImage p) (pointImage q) z = w` and every intersection datum `D` at `z`, `Nonempty (F^{≺w}/F^{⪯w} ≅ D.pieceFunctor)`.

**Second conjunct (identity case).** Write `1̄` for `identityParabolicDoubleCoset p q`. There is a family `e`, assigning to every `W` an equivariant linear equivalence `(F^{<1̄}/F^{≤1̄})(W) ≃ W` (a `Representation.Equiv` from the `ρ` of the quotient object to `W.representation`). The family is natural: for every morphism `f : W ⟶ W'` and every `x`, `e W' ((F^{<1̄}/F^{≤1̄})(f) x) = SmoothRep.hom f (e W x)`.

## Provenance and departures from the source

The provenance is derived. The statement follows the claims of VII.3.2 one by one, with these differences.

- **Double cosets.** Renard indexes the double cosets by `W_M \ W_G / W_M` and orders that set. The statement works with the actual double cosets `P(F) \ G(F) / Q(F)` and the closure relation of [PQRegularity](PQRegularity.md), as the definitions do. The identification through V.4.5/V.4.7 is not formalized.
- **The order.** Renard fixes one total order `⪯` refining the Bruhat order. The statement holds for every such order. It does not assert that one exists.
- **Representatives and intersection data.** Renard's reformulation uses his representative `w` of `w̄`. The statement asserts it for every representative `z` and every intersection datum `D` at `z`. If there is no datum at `z`, the quantification over `D` is empty and part 3 says nothing for that `z`. A datum records that `M ∩ z·M` contains a maximal split torus of `G`. So the Levi factors `M` of `P` and `z·M` of `z·Q` contain a common maximal split torus, which is the property of Renard's representatives used in the proof of VI.5.1. Part 3 does not assert that representatives with data exist. That is a conclusion of the published [RepresentedGeometricLemmaStatement](../Geometric/RepresentedGeometricLemmaStatement.md), and this module does not use it.
- **The identity case.** Renard writes `F^{<1̄}/F^{≤1̄} ≃ Id_{M(M)}`. The functor `F^{<1̄}/F^{≤1̄}` is valued in `Rep.{max u v} ℂ (rationalPoints M)` and the identity in `SmoothRep.{0, u, v} ℂ (rationalPoints M)`, so the two are not functors between the same categories. The statement therefore asks for equivariant linear equivalences `(F^{<1̄}/F^{≤1̄})(W) ≃ W` that are natural in `W`. For `w = 1̄` part 2 also gives `F^{≺1̄}/F^{⪯1̄} ≅ F^{<1̄}/F^{≤1̄}`, so the identity case covers both sides of Renard's display. Since `F^{<1̄}(W)/F^{≤1̄}(W)` is a subquotient of `r_Q^G ∘ i_P^G(W)`, the second conjunct also says that `ρ` is a subquotient of `r_Q^G ∘ i_P^G(ρ)`.
- **Support conditions.** The subspaces `F̃` are the published vanishing subfunctors. [PQRegularity](PQRegularity.md) explains why a smooth induced function satisfies Renard's support conditions exactly when it vanishes on the corresponding set.
- **Stability and subfunctors.** Renard remarks that the four subspaces are `Q`-stable and that the four images are subfunctors of `r_Q^G ∘ i_P^G`. In the Library these are part of the definitions (`RepSubfunctor`), so they are not stated here.
- **Order of the subquotient.** `S.quotientFunctor T` divides `T` by `S ∩ T`. Part 1 states the inclusions at the level of the `F̃`. Their images then satisfy the same inclusions, so the intersections are Renard's denominators, although the statement does not need this.
- **Standard Levi.** Renard assumes `M` standard and `P`, `Q` semi-standard, and says that this restriction is "aucunement essentielle, mais de pure commodité". The statement does not assume it.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Intertwining.PQRegularity` | `parabolicDoubleCosets`, `identityParabolicDoubleCoset`, `Geometric.IsBruhatRefinement`, the four vanishing subfunctors and the four support images; through it, `leviJacquetInductionFunctor`, `GeometricLemmaIntersectionDatum`, `pieceFunctor` and `RepSubfunctor.quotientFunctor`, `quotientObj`, `quotientMap` |
| `Langlands.Representation.Category.Basic` | `SmoothRep`, `SmoothRep.representation`, `SmoothRep.hom` |
