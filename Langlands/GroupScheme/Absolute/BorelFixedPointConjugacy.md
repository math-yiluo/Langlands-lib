# Actual Borel conjugacy data from a fixed quotient point

Worker 1293.

This internal construction starts with two actual Borel embeddings
`i : B ⟶ G` and `i' : B' ⟶ G` over an algebraically closed field of arbitrary
characteristic and universe. A supplied morphism `q : G.X ⟶ Q` is locally of
finite type and surjective and has the exact right-coset fibers for `i'`
on every relative scheme test. An actual `SchemeAction G Q` is supplied
together with its lifted-coset equation
`a.act g (h ≫ q) = (g * h) ≫ q`.

Given an actual rational point `x` of `Q` that is fixed, on every relative
test and refinement, by the action restricted along `i`,
`IsBorelSubgroup.conjugatingDataOfFixedPoint` constructs a rational point
`g` of `G` and an actual isomorphism `φ : B ≅ B'`, with the exact equation
`i ≫ (G.innerIso g).hom = φ.hom ≫ i'`.

The implementation reuses the published general theorem
`Langlands.exists_point_lift_of_locallyOfFiniteType_surjective` to choose a
lift `g₀` of `x`. The structure-morphism equation makes this lift a morphism
over the field. All-test fixedness and the lifted-coset action equation say
that the coset represented by `g₀` is fixed by `B`. The published
`factorOfFixedCoset` then gives an actual homomorphism `B ⟶ B'` whose
composite with `i'` is `i` conjugated by `g₀⁻¹`. The published
`conjugatingIsoOfFactor` uses Borel maximality to make that homomorphism an
isomorphism. The returned conjugating point is `g₀⁻¹`, so the conclusion
has precisely the convention used by `BorelConjugacyStatement`.

The provenance is internal composition of rational point lifting, the
all-test fixed-coset factorization and Borel transport. Classical choice is
used only to select the rational lift. This construction assumes the fixed
point and quotient/action inputs; their existence, quotient properness and
the general Borel conjugacy theorem remain separate obligations.
