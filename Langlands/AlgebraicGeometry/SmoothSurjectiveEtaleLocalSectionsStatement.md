# Etale local sections of smooth surjective scheme morphisms

`SmoothSurjectiveEtaleLocalSectionsStatement.{u}` is the following proof
obligation. For arbitrary actual schemes `W T : Scheme.{u}` and a smooth
surjective morphism `f : W ⟶ T`, there are an actual scheme `V : Scheme.{u}`,
an etale surjective morphism `e : V ⟶ T`, and a morphism `s : V ⟶ W` with
`s ≫ f = e`. Equivalently, the pullback of `f` along `e` has a section.
There is no quasi-compactness, separatedness, finite-type, reducedness, or
field hypothesis. In particular, `e` is not required to be quasi-compact.
The proposition is defined here; its unconditional proof is supplied by
[SmoothSurjectiveEtaleLocalSections](SmoothSurjectiveEtaleLocalSections.md).

The source is the registered original
`stacks-055U-smooth-etale-local-sections-2026-11-02`, file `055U.html`,
More on Morphisms, Lemma 37.38.6 (Tag 055U), which cites EGA IV,
Corollaire 17.16.3 (ii). Its folder fingerprint is
`8e72c81439f682b3c78d993bb45443d09505d9bf46efd87cc441ee6ca1789598`.
The original statement and both proofs give an etale neighborhood mapping
to `W` over `T` through every point in the image of a smooth morphism.
For a surjective morphism every point of `T` qualifies. Choosing one such
neighborhood for each point and taking their disjoint union gives the single
surjective etale morphism used here. This last packaging is a derived
consequence, rather than the literal wording of the source. The indexing
type is the point type of `T`, so the disjoint union remains in the same
scheme universe `u`. The retained comments correct old diagram notation
and a formula in the second proof, and add the slogan and EGA reference;
they do not change the local-sections conclusion.

The rest of the module proves two consequences conditional on that precise
scheme statement. They do not supply a proof of the statement itself.

`AlgebraicSpace.isLocallySurjective_smooth_schemeYoneda_map` treats a smooth
surjective scheme morphism in the full slice `Over S`. Apply the statement
to its underlying scheme morphism and give the etale cover its composite
structure map to `S`. The resulting map of represented presheaves factors
through the original morphism. The published
`isLocallySurjective_etale_schemeYoneda_map` makes this factorization locally
surjective for `Scheme.etaleTopology.over S`; cancellation of a locally
surjective composite proves the desired local surjectivity.

`AlgebraicSpace.isLocallySurjective_etale_of_isSmooth_isSurjective` treats
an arbitrary transformation `a : F ⟶ G` whose represented base-change
projections are smooth and surjective in the existing `IsSmooth` and
`IsSurjective` senses. For every test scheme `T` and every section
`x : G(T)`, use the complete represented pullback along the map classified
by `x`. The preceding consequence makes its projection to `T` locally
surjective. Each local lift gives a section of `F` through the first
pullback projection, and commutativity of the square proves that it maps
to the restriction of `x`. Thus its covering image sieve is contained in
the image sieve for `a`, which is covering as well.

These conditional consequences use all schemes and morphisms in `Over S`,
with the Library's actual lifted Yoneda presheaves. They quantify over
every target section; neither a global family representative nor a
restriction to geometric points is used. They require no sheaf condition
on `F` or `G`. The geometric statement concerns etale local sections
for arbitrary smooth surjections, distinct from etale slicing of an
equivalence relation and from descent of smoothness along a source map.
