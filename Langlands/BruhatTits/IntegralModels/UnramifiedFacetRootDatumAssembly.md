# A descended facet root datum from exact quotient-root comparison

This derived construction isolates the remaining geometric input for the
descended derivative root datum at arbitrary universe `u`. It takes a supplied
parahoric datum `P` over a nonarchimedean local field `F`, its apartment axioms
and root-reflection property, a maximal-unramified building `C`, an equivariant
map `e`, an unramified zero datum `E`, a rational point `g`, and an arbitrary
apartment subset `Fa`. The supplied component model `D` satisfies

```
D.neutral.baseChangeUnramified.integralPoints =
  E.zeroPoints ∩ C.pointwiseFixer (e '' (P.translatedApartmentMap g '' Fa)).
```

The construction also takes a supplied special-fibre quotient `Q` satisfying
`Q.IsReductiveQuotient`, a supplied integral torus `T` with generic inclusion
`P.i ≫ (G.innerIso g).hom` satisfying `T.IsClosedSplit`, and arbitrary relative
root reflection data `Droot` for `P.i`.

The additional hypothesis `hroots` is the exact equivalence, for every character
`χ` of `T.specialFibre`, between actual root membership for
`T.specialFibreInclusion ≫ Q.projection` and membership of the inverse canonical
character specialization of `χ` in `facetDerivativeRoots P Fa`. This equivalence
is assumed. This module does not prove it from the model characterization.

`unramifiedFacetRootDatumOfRootComparison` constructs a root datum on the actual
quotient-root subtype and the character and cocharacter lattices of the actual
special torus. It proves `IsRootDatumOf` for the actual composite inclusion and
equality of the entire graph of root-coroot pairs with
`apartmentDerivativeRootCorootGraph`. Both specialization maps pass through
the same supplied integral torus.

The proof obtains connected reductivity from the quotient validity predicate
and closedness of the special-torus inclusion from
`IntegralTorusData.isClosedSubgroup_quotientTorus`. For each generic derivative
root, `facetReflectionQuotientRepresentative` constructs an actual rational
point of the quotient and an actual automorphism of the special torus. They
satisfy the normalizer square and the full specialized character reflection
formula with the prescribed `Droot` coroot. Thus the reflection input of
`apartmentDerivativeRootDatumOfRootComparison` is supplied by these constructed
representatives. Applying that construction gives the stated root datum and
paired graph equality.

`hasApartmentDerivativeRootDatum_of_unramifiedRootComparison` packages this datum
with finiteness of the actual relative-root subtype into the existing
`HasApartmentDerivativeRootDatum` predicate. It concludes the predicate for
every proof that the integral torus is split; proof irrelevance identifies
that proof with the splitness component used in the construction.

This unit is derived from `FacetRootDatumAssembly`, `FacetTorusQuotient` and
`UnramifiedFacetReflections`. It needs no facet condition or smoothness of `D`
beyond the hypotheses of those constructions. It is a conditional assembly
step toward `UnramifiedFacetRootDatumStatement`, whose remaining exact root
comparison and complete universally quantified theorem are still open.
