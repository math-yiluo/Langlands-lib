# Etale slices of smooth equivalence relations on schemes

`SmoothEquivalenceRelationEtaleSliceStatement` states that every equivalence
relation on a scheme with smooth projections can be sliced to an etale one.

## Statement

For every universe `u`, all schemes `U` and `R` in `Scheme.{u}` and all
morphisms `t s : R ⟶ U` the following holds. Assume that
`AlgebraicSpace.AtlasRelation.IsEquivRel t s` holds and that `t` and `s` are
smooth. Then there exist a scheme `U'` in `Scheme.{u}` and a morphism
`g : U' ⟶ U` such that

1. `g` is locally of finite type, and
2. the composite `pullback.snd g t ≫ s : U' ×_{g, U, t} R ⟶ U` is etale and
   surjective.

Here `IsEquivRel t s` is the published absolute equivalence-relation condition:
`prod.lift t s : R ⟶ U × U` is a monomorphism, and for every scheme `T` the
`T`-points of `R`, viewed through `t` and `s`, form a reflexive, symmetric and
transitive relation on the `T`-points of `U`. These are exactly the fields of
`EtaleEquivalenceRelation` without the etaleness of the projections. All schemes
are arbitrary. There is no base scheme, so `U × U` is the absolute product,
that is, the product over `Spec ℤ`. In the notation of the Stacks Project,
`pullback.snd g t ≫ s` is the morphism
`h = s ∘ pr : U' ×_{g, U, t} R → R → U`.

## Provenance

The statement is derived from the Stacks Project. Take the base scheme
`S = Spec ℤ`, so that `U ×_S U = U × U`, and let `j = (t, s) : R → U × U`.

1. *The quotient is an algebraic space.* The equivalence relation `j` defines a
   groupoid scheme `(U, R, s, t, c)` whose projections are smooth, hence flat
   and locally of finite presentation. By Theorem 80.10.1 (tag 04S6), case (2),
   the fppf quotient `X = U/R` is an algebraic space.
2. *`U → X` is smooth and surjective, and `R = U ×_X U`.* These steps are carried
   out in the proof of Lemma 80.12.3 (Section 80.12, tag 076L) and use only the
   equivalence relation. Lemma 80.11.6 shows that `U → X` is surjective, flat
   and locally of finite presentation. Groupoids in Spaces, Lemma 78.19.5,
   together with the injectivity of `j`, gives `R = U ×_X U`, with `t` and `s`
   the two projections. Descent on Spaces, Lemma 74.11.26, then shows that
   `U → X` is smooth and surjective, because its base changes `s, t : R → U`
   are smooth and surjective.
3. *An etale atlas and local sections.* By the definition of an algebraic space
   (Definition 65.6.1, tag 025Y) there are a scheme `V` and a surjective etale
   morphism `V → X`. The diagonal of `X` is representable, so `U ×_X V` is a
   scheme, and its projection to `V` is smooth and surjective by base change. By
   More on Morphisms, Lemma 37.38.6 (tag 055U; EGA IV, Corollaire 17.16.3 (ii)),
   every point `v ∈ V` has an etale neighbourhood `V_v → V` with a `V`-morphism
   `V_v → U ×_X V`. Let `U'` be the disjoint union of the `V_v`. Then
   `U' → V` is etale and surjective. Let `g` be the composite
   `U' → U ×_X V → U`.
4. *The conclusions.* The morphism `U ×_X V → U` is etale as a base change of
   `V → X`. The morphism `U' → U ×_X V` is locally of finite type because its
   composite with `U ×_X V → V` is etale, by the cancellation property of
   morphisms locally of finite type. So `g` is locally of finite type. Under
   `R = U ×_X U`, with `t` the first projection, `U' ×_{g, U, t} R` is
   `U' ×_X U`. The morphism `h` is its second projection to `U`, which is the
   base change along `U → X` of the etale surjective composite `U' → V → X`.
   So `h` is etale and surjective.

The disjoint union in step 3 is indexed by the points of `V`, so `U'` lies in the
same universe as `U` and `R`.

## Use

This statement is intended for the slicing step in a reduction of
`SmoothRelationQuotientStatement` to
`EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement`. There one restricts
the smooth relation to `U'`, shows that the restriction is an etale equivalence
relation, and identifies its algebraic-space quotient with the canonical etale
quotient of the smooth relation. None of this is part of the present statement.
