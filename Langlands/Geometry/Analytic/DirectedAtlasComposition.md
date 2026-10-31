# Strong composition through directed original charts

This module constructs composition of arbitrary `StrongHom` maps on supplied
actual affinoid atlas presentations when the intermediate and final atlases have
pairwise directed original chart domains. The result supplies bounded algebra
pullbacks on every admissible source/final-chart pair, together with their
spectrum squares and two-variable restriction equations. It proves identities
and associativity for the complete strong maps and constructs the category
`DirectedAtlasPresentation K`.

The coefficient field has `NormedField`, `IsUltrametricDist` and `CompleteSpace`
instances. Field, underlying-space and chart-index universes are independent
`u`, `v` and `w`; the presentations in a given construction share this triple.
The imported chart algebras are actual presented affinoid algebras built from
finite positive-polyradius Tate algebras and closed ideals. The construction
retains their bounded algebra maps, including information on nonreduced
algebras.

## Source and provenance

The original reference is Vladimir G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, with source SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Definition 1.2.3 and Remark 1.2.4(i), printed page 16 / PDF page 13, supply
affinoid atlases, their actual affinoid-domain restriction maps and the
composition equation for restrictions. Definition 1.2.7, printed page 18 /
PDF page 15, requires a continuous strong map, a containing target chart for
each source chart and compatible affinoid morphisms at every admissible pair.
The composition discussion following Proposition 1.2.8 on the same page
constructs general strong composition using extended atlases and finite
affinoid gluing.

The construction here is derived infrastructure with an additional directedness
hypothesis on the original intermediate and final atlases. Common original
upper charts replace the need to extend the atlas for this restricted
construction. Actual domain factorization then constructs each required
bounded pullback. This module does not claim the source's general composition,
Proposition 1.2.8 or the analytic category obtained by localization.

## Admissible chains and their bounded maps

Write `U_i`, `V_j` and `W_k` for the ranges of charts of `A`, `B` and `C`.
For strong maps `f : StrongHom A B` and `g : StrongHom B C`, an admissible chain
consists of containments `f(U_i) ⊆ V_j` and `g(V_j) ⊆ W_k`.
`comp_admissible` proves `(g ∘ f)(U_i) ⊆ W_k`.
`chainPullback` is the actual bounded algebra homomorphism

```text
algebra_C(k) --g.pullback--> algebra_B(j) --f.pullback--> algebra_A(i).
```

`chainPullback_chart` proves its spectrum square by applying the two original
strong-map chart equations. `chainPullback_naturality` proves its restriction
equation when the source, intermediate and final charts are enlarged
simultaneously. The proof uses the two strong-map restriction equations and
associativity of bounded algebra composition.

`chainPullback_commonUpper` compares two admissible chains with the same source
chart and unrelated intermediate or final charts. Directedness of `B` puts the
two intermediate charts in a common original chart `b`. The target-existence
field of `g` supplies a chart containing `g(V_b)`. Directedness of `C` puts this
chart and both original final charts in a common original chart `r`. The
preceding naturality equation identifies both chain pullbacks after
precomposition with their actual restrictions from `algebra_C(r)`.

No monotone choice of intermediate targets is required. Spectrum equality is
used for image conditions and chart squares; it is never used to infer equality
of bounded algebra maps.

## Constructing every composite pullback

For any admissible final pair `(i,k)`, `compPullback_existsUnique` proves unique
existence of a bounded map `ψ : algebra_C(k) → algebra_A(i)` satisfying the
following equation for every admissible chain `(i,j,q)` whose final chart
contains `W_k`:

```text
ψ.comp (restriction_C k q) = chainPullback f g i j q.
```

For existence, choose a target chart for `f` at `i`, a target chart for `g` at
that intermediate chart, and a common final upper chart also containing `W_k`.
The chain spectrum square and admissibility of `(i,k)` verify the image
condition in `C.atlas.restriction_universal`, applied to the actual test algebra
`A.atlas.algebra i`. This universal property produces `ψ`.

For its equation at any other chain, `chainPullback_commonUpper` supplies an
actual chart where the two chain maps agree. Restriction composition and
`restriction_hom_ext` then cancel the upper restriction. The same algebraic
cancellation proves uniqueness. Thus the bounded map is independent of the
chains and upper charts used in its construction.

`compPullback` chooses this proved unique map.
`compPullback_comp_restriction` gives its defining equation at every containing
chain. `compPullback_chart` derives the spectrum square from this equation and
the chart square of the final restriction. `compPullback_naturality` proves
two-variable naturality: choose a chain for the larger source chart and a final
upper chart containing the larger requested target chart, use the two
factorization equations and chain naturality, and cancel that final
restriction.

`compOfDirected` assembles these data into `StrongHom A C`. Its continuous map
is exactly `g.baseMap.comp f.baseMap`; its target-existence witness comes from
successive witnesses for `f` and `g`. No missing local pullbacks or output
affinoid algebras are supplied as additional assumptions.
`compOfDirected_pullback` proves that, at every admissible chain `(i,j,k)`, the
new bounded pullback is exactly
`(f.pullback i j).comp (g.pullback j k)`.

## Equality, category laws and comparisons

`ext_of_directed` proves that strong maps into a directed target are equal if
their continuous maps agree and, for each source chart, one admissible target
chart has equal bounded pullbacks. To compare an arbitrary target chart with
that witness, take a common upper chart. Strong naturality transports both
pullbacks there, and `restriction_hom_ext` cancels the actual restriction. Full
`StrongHom.ext` then identifies the complete families.

`id_compOfDirected` and `compOfDirected_id` apply this criterion to a target
witness of the original map, using the exact chain formula and identity
restrictions. The former requires directed source and target atlases; the
latter requires only the directed target atlas.
`compOfDirected_assoc` assumes directed intermediate and final atlases `B`,
`C` and `D`. It chooses one successive chain through all four presentations,
uses the exact chain formula on both parenthesizations and concludes with
bounded algebra associativity. These are equalities of full strong maps.

`compOfDirected_eq_compOfTopCharts` compares the result with the imported
greatest-chart composition. The exact chain formulas agree at the supplied
greatest intermediate and final charts; directed extensionality gives equality
on every admissible pair. `ofDirected_comp` similarly proves that extending a
composite chosen map agrees with composing the two directed strong extensions.
The proof compares the original selected bounded composites and then uses
directed extensionality.

`DirectedAtlasPresentation K` consists of a supplied
`AffinoidAtlasPresentation K` and a proof of `HasDirectedCharts`. Its morphisms
are the entire `StrongHom` families, with the constructed composition. The
proved full strong-map laws give its category instance.
`baseMap_id` and `baseMap_comp` record the exact underlying continuous maps;
`spaceFunctor` retains the actual spaces as objects of `TopCat.{v}`.

`ofTopChart` gives a directed presentation on the same supplied greatest-chart
atlas. `topChartFunctor` retains all strong maps, and the composition comparison
proves its functor law. `topChartFullyFaithful` has the identity inverse on Hom;
it yields the `Full` and `Faithful` instances.
`topChartFunctor_spaceFunctor` proves exact equality of the two underlying-space
functors. No faithfulness of the underlying-space functor is asserted.

## Scope

The inputs are supplied actual affinoid atlases with their net, domain
factorization and bounded restriction data. `HasDirectedCharts` requires every
two original chart ranges to lie in a common original chart; it supplies
neither a greatest chart nor a monotone target assignment for each strong map.
`compOfDirected` needs no directedness of its source atlas. The bundled category
uses directed presentations so that its composition is always available.

General atlas extension, finite affinoid gluing, composition without these
directedness hypotheses and localization at atlas refinements remain separate
obligations. This module constructs no structure sheaf, étale or quasi-étale
site, equivariant analytic site, or Harris tower.
