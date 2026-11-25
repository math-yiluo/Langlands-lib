# Statement: fibre products in `Qét(X(G))` and `Ét(X(G))`

This module states, without proof, that the categories `Qét(X(G))` and
`Ét(X(G))` of a `G`-space `X` have fibre products, computed on underlying
analytic spaces with the diagonal action. There are two propositions in
`Langlands.Analytic.SaturatedAtlasPresentation`:

- `EquivariantQuasiEtalePullbacksStatement`, for `Qét(X(G))`
  (`EquivariantQuasiEtaleSite X`);
- `EquivariantEtalePullbacksStatement`, for `Ét(X(G))`
  (`EquivariantEtaleSite X`).

They are the prerequisite of the conditional proof of
`RestrictionSiteMorphismStatement` in the module
`RestrictionSiteMorphismReduction`.

## Statements

`EquivariantQuasiEtalePullbacksStatement : Prop`. For every complete
ultrametric normed field `K : Type u`, every group with a topology
`G : Type z`, every `G`-space `X : GSpace.{u, v, v} K G`, and all morphisms
`f₁ : U₁ ⟶ U₃` and `f₂ : U₂ ⟶ U₃` of `EquivariantQuasiEtaleSite X`, there are
an object `W` of `EquivariantQuasiEtaleSite X` and morphisms `p₁ : W ⟶ U₁`,
`p₂ : W ⟶ U₂` of `EquivariantQuasiEtaleSite X` such that

```
IsPullback (GSpace.forget.map p₁.left) (GSpace.forget.map p₂.left)
  (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left)
```

holds in the Library's category of analytic spaces
`LocalizedCategory.{u, v, v} (K := K)`.

`EquivariantEtalePullbacksStatement : Prop` is the same statement with
`EquivariantEtaleSite X` in place of `EquivariantQuasiEtaleSite X`.

In words: `W` is a `G`-space whose structure morphism `W → X` is
quasi-étale (resp. étale), `p₁` and `p₂` are `G`-morphisms over `X`, and the
square of underlying analytic spaces

```
W  --p₁-->  U₁
|           |
p₂          f₁
v           v
U₂ --f₂-->  U₃
```

is a pullback square, that is, `W = U₁ ×_{U₃} U₂` as analytic spaces
(Mathlib's `IsPullback`: the square commutes and its cone is a limit cone).
The statement does not prescribe the action on `W`. Since `p₁` and `p₂` are
`G`-morphisms, the uniqueness part of the universal property shows that each
`g ∈ G` acts on `W` as the morphism induced by the actions of `g` on `U₁` and
`U₂`: the action on `W` is necessarily the diagonal action.

The statement asks for one such square for each cospan. It does not ask
that every pullback of analytic spaces carry such a structure.

## Original sources

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p. 3. After defining `Qét(X(G))` and `Ét(X(G))`, Berkovich
asserts that a morphism `φ : X′(G′) → X(G)` gives morphisms of both sites and
of their topoi. The direct image of a sheaf `F′` on `X′(G′)`, evaluated at
`U(G)` over `X(G)`, is given by evaluating `F′` at `(X′ ×_X U)(G′)`. Here
`F′` denotes the source sheaf; the manuscript's left-hand side prints
`φ_*F` rather than `φ_*F′`.

Berkovich's base-change formula motivates the statement but has a different
scope. For a fixed ground field, restrict the actions on `X` and `U` along
`G′ → G`. If `X′ → X` is itself an object of the corresponding site over
`X` with `G′`-action, the cospan `X′ → X ← U` belongs to that site and its
underlying fibre-product square is an instance of the statement. The
formula, in contrast, also allows `X′ → X` that are neither quasi-étale nor
étale and regards the resulting object as lying over `X′`. The restriction
proof uses pullbacks of cospans already in a single site over `X`, not the
general base-change formula.

The underlying facts about analytic spaces are:

- Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, Publ.
  Math. IHÉS 78 (1993), registered as `berkovich-1993-etale-cohomology`:
  The opening of the proof of Proposition 1.4.1 (printed p. 29) establishes
  existence of fibre products in the fixed-field category `k-𝒜n`; the
  proposition itself is stated for `Φ_k-𝒜n`. Corollary 3.3.8 (printed p. 63)
  gives stability of étale morphisms under composition and base change.
  Corollary 3.3.9 and the remark after it (printed pp. 63–64) give
  étaleness of arrows in `Ét(X)`.
- Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115
  (1994), registered as `berkovich-1994-vanishing-cycles-formal-schemes`:
  Lemma 3.1(i) (printed p. 544) gives stability of quasi-étale morphisms
  under composition and base change; part (ii) gives quasi-étaleness of
  every `X`-morphism between spaces quasi-étale over `X`.

Together these give, for `f₁ : U₁ → U₃` and `f₂ : U₂ → U₃` over `X`, the
fibre product `U₁ ×_{U₃} U₂` and the quasi-étale (resp. étale) morphism
`U₁ ×_{U₃} U₂ → U₂ → X`. The equivariant part (the diagonal action is again
a `G`-space structure) is not stated in these sources.

## Provenance

Derived. The formulation is the Library's: `G`-spaces are objects of
`GSpace.{u, v, v} K G` (module `ContinuousAnalyticAction`: Hausdorff
underlying space and continuous action), the sites are the Library's
`EquivariantQuasiEtaleSite` and `EquivariantEtaleSite`, and analytic spaces
and fibre products are those of `LocalizedCategory.{u, v, v}`. The field may
have the trivial valuation, and `G` is a group with an arbitrary topology,
as in the Library's sites. Requiring the underlying square to be a pullback
of analytic spaces, and not only a pullback in `Qét(X(G))`, is the form in
which the fibre product is used: any functor between such sites that does
not change the underlying analytic spaces, such as restriction along a
continuous homomorphism `H → G`, then preserves it.

The Library proves underlying pullback existence along a quasi-étale leg
(`exists_localizedPullback_of_quasiEtale`) and along an étale leg
(`exists_localizedPullback_of_etale`) in `LocalizedCategory.{u, v, v}`.
With a quasi-étale first leg, the Hausdorffness conjunct of
`hasCompactPairPreimages_of_quasiEtale` (`LocalizedPullbackCompactPreimages`)
applies to any supplied pullback of Hausdorff factors, and
`isContinuousAction_of_isPullback_of_quasiEtale`
(`LocalizedQuasiEtalePullbackAction`) supplies continuity of the induced
action for a cospan of equivariant maps. These results do not show that
an arrow in either site has the required property, nor that the projection
parallel to it is quasi-étale or étale. Those steps use the over-morphism
and base-change properties described above. The remaining composite to `X`
uses composition stability, already proved for étale arrows as `etale_comp`
(`LocalizedEtaleComposition`).

This is a `lean.statement`: nothing is proved here.
