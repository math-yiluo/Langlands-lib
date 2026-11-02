# Quotients of schemes by finite locally free equivalence relations

Authors: Worker 934 wrote the Lean statement and this Markdown.

The module
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationQuotientStatement`
defines one proposition in namespace `Langlands.AlgebraicGeometry`:

- `FiniteLocallyFreeEquivalenceRelationQuotientStatement.{u}`.

It states the existence part of Stacks Proposition 66.14.1 in the case where
the equivalence class of every point lies in an affine open. It is a
Prop-valued definition for every universe `u`. This module supplies no proof.

## Original source

The registered source is
`stacks-obtaining-a-scheme-07S5-07S6-07S7-html-2026-11-02`: The Stacks
Project Authors, *The Stacks Project*, Chapter 66 "Properties of Algebraic
Spaces", Section 66.14 "Obtaining a scheme". It is a folder of official
HTML pages fetched on 2 November 2026, with content SHA-256
`4dc968da6b54d8c676e8a5d303b200b8daf982cf28d1b98587343b0ee50373f8`.
Its file `07S6.html` is
[Tag 07S6](https://stacks.math.columbia.edu/tag/07S6), Proposition 66.14.1,
together with its footnote 1, its proof and its comments.

Proposition 66.14.1 considers a groupoid scheme `(U, R, s, t, c)` over a
scheme `S` and assumes:

1. `s, t : R → U` are finite locally free;
2. `j = (t, s)` is an equivalence relation;
3. every nonempty closed subset `Z` of `U` contains a point `u` whose
   `R`-equivalence class `t(s⁻¹({u}))` is contained in an affine open of `U`.

It concludes that there is a finite locally free morphism `U → M` of schemes
over `S` with `R = U ×_M U` such that `M` represents the quotient sheaf `U/R`
in the fppf topology. Footnote 1 lets `E ⊆ U` be the set of points `u` whose
class `t(s⁻¹({u}))` lies in an affine open. It notes that condition (3) holds
if `E = U`. Comments #10063 and #10562 of 2025 led to the current wording of
condition (3). Comment #10063 observes that the case where every point has
the property was already fine. The page has no other errata affecting that
case.

The proof of Proposition 66.14.1 covers `U` by `R`-invariant affine opens
`U_i`, using Groupoids Lemma 39.24.1 (Tag 03JE). It applies Groupoids
Proposition 39.23.9 (Tag 03BM) to each restriction `R|_{U_i}` and glues the
resulting affine quotients. The Library states both cited results in
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements`.

## Hypotheses

The Lean module imports Mathlib's scheme limits and its morphism-property
modules for finite, flat and locally finitely presented morphisms. Mathlib is
pinned at commit `5ed2965256430c3649e86755f9576b54eca72435` in the prepared
environment.

The proposition quantifies over arbitrary schemes `U R : Scheme.{u}` and
morphisms `t s : R ⟶ U`. Its first ten hypotheses are exactly the common
hypotheses of the two propositions in
`Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements`,
in the same order and form:

- `Mono (prod.lift t s)`: the map `(t, s)` into the categorical product
  `U × U` is a monomorphism.
- For every scheme `T : Scheme.{u}`, every `a : T ⟶ U` lifts to a diagonal
  related pair; every `r : T ⟶ R` has a reversed pair; and every pair
  `r r' : T ⟶ R` with `r ≫ s = r' ≫ t` has a composite pair with endpoints
  `r ≫ t` and `r' ≫ s`.
- Each of `t` and `s` is `IsFinite`, `Flat` and
  `LocallyOfFinitePresentation`. Together these express finite local
  freeness, as in condition (1) of the source.

The Markdown of that Library module explains why these conditions express
condition (2), an equivalence relation in the sense of Groupoids
Definition 39.3.1 (Tag 022P). By Yoneda, they also recover the groupoid
structure `c` of the source, which is unique when `j` is a monomorphism. The
same Markdown explains the absolute setting. Here schemes are considered over
`Spec ℤ`, so `U × U` is the categorical product of schemes. A relative
equivalence relation over any base `S` gives one of these absolute relations
after forgetting its base, because `U ×_S U → U × U` is a monomorphism.

The last hypothesis is

```lean
∀ u : U, ∃ W : U.Opens, IsAffineOpen W ∧ ∀ r : R, s r = u → t r ∈ W
```

For a point `u`, the points `t r` with `s r = u` form the set
`t(s⁻¹({u}))`, the `R`-equivalence class of `u` in the source. So the
hypothesis says that every point of `U` lies in the set `E` of footnote 1,
that is, `E = U`. It implies condition (3) of the source: every nonempty
closed subset contains a point, and every point lies in `E`. The given affine
opens `W` need not be `R`-invariant.

No Noetherian, separatedness, quasi-compactness or base-field hypothesis is
added. The universe `u` is unrestricted, and every test scheme in that
universe is quantified over. This hypothesis is weaker than affineness of `U`:
if `U` is affine, take `W = ⊤` for every point.

## Conclusion

The proposition concludes that there exist `M : Scheme.{u}` and `q : U ⟶ M`
with

- `IsPullback t s q q`;
- `IsFinite q`, `Flat q`, `LocallyOfFinitePresentation q` and
  `Surjective q`.

The pullback condition includes `t ≫ q = s ≫ q`. It says that the square with
top `t`, left `s` and both other arrows `q` is a pullback, so `(t, s)`
identifies `R` with `U ×_M U`. This is the equality `R = U ×_M U` of the
source. The first three morphism properties say that `q` is finite locally
free, as in the source.

The source does not state surjectivity of `q` separately. It follows from
the representability clause. The map `U → U/R` is a surjection of fppf
sheaves, since `U/R` is the sheafification of the presheaf quotient. Given a
point `m` of `M`, the morphism `Spec κ(m) → M` therefore lifts to `U` after
an fppf covering `{T_k → Spec κ(m)}`. Some `T_k` is nonempty, and the image
in `U` of any of its points maps to `m`. In the proof of the source,
surjectivity can also be seen locally: each affine quotient `U_i → M_i` is
surjective by Groupoids Lemma 39.23.6 (Tag 03BL), and the `M_i` cover `M`.

The Lean conclusion omits two parts of the source. It does not record that
`M` represents the fppf quotient sheaf `U/R`, and it does not record that
`M` is a scheme over `S`. Its only data are the scheme `M`, the morphism `q`,
the pullback square and the four morphism properties. None of these
conclusions is assumed as a hypothesis. Unlike
`FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement`, the conclusion
does not assert that `M` is affine. A proof must establish the stated
conclusion from the displayed hypotheses.
