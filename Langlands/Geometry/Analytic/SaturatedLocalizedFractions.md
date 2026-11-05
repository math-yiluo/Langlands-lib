# Actual fractions in the saturated atlas localization

This is an internal construction from the proved right calculus for actual
saturated strong atlas maps and the previously constructed localization.
The general existence and equality results are imported from Mathlib's
`CategoryTheory/Localization/CalculusOfFractions.lean`. No new assertion from
an original geometric source is attributed here.

## Objects and hypotheses

Work over a complete ultrametric normed field `K : Type u`. The category is
`SaturatedAtlasPresentation.{u,v,w} K`, with independent ambient-space and
chart-index universes `v` and `w`. An object contains an actual affinoid atlas
presentation and proved full-domain closure: every actual local full domain
has the locus of an original chart. The existing saturation construction
supplies such objects from actual atlas presentations.

A morphism is a complete strong map, retaining its continuous ambient map
and bounded algebra pullbacks at every admissible original-chart pair.
The chart algebras are actual finite positive-polyradius Tate quotients.
Composition is the existing saturated strong composition. The property
`quasiIsomorphisms` means an ambient homeomorphism and the complete
`Represents` predicate for every admissible chart pullback. In particular,
its unique bounded factorization tests range over every presented-affinoid
coefficient algebra. No chart directedness or upper-cofinality premise is
introduced in this unit.

Write `Q := localizationFunctor` and `W := quasiIsomorphisms`. The category
`LocalizedCategory` and functor `Q` already exist as the actual
path-and-relations localization, with their proved universal property.
The right-calculus instance used here is proved by the constructed Ore
source refinement and complete bounded-test cancellation. It is not a
hypothesis specifying the desired fraction representation.

## Actual representatives

A Mathlib `W.RightFraction A B` contains an actual saturated presentation
`S := φ.X'`, a complete strong map `s := φ.s : S → A`, its full
quasi-isomorphism proof `φ.hs`, and a complete numerator `f := φ.f : S → B`.
The definition `localizedRightFraction` interprets these data as

```text
(Q(s))⁻¹ ≫ Q(f) : Q(A) → Q(B).
```

The inverse is the previously constructed `localizedQuasiIso` inverse.
`localizedRightFraction_eq_map` identifies this definition with Mathlib's
right-fraction interpretation, definitionally.

`exists_localizedRightFraction` specializes Mathlib's representation theorem
using the proved right calculus: every `h : Q(A) → Q(B)` equals the
interpretation of an actual fraction. `rightFractionRepresentative` chooses
such a fraction by classical choice from this proved existence theorem.
`localizedRightFraction_representative` proves that its interpretation is
exactly `h`. This choice has no asserted canonical or computational property.
Its source, denominator and numerator are actual objects and morphisms in
the constructed saturated atlas category.

## Equality and the hom-set quotient

The Prop-valued definition `FractionCommonRefinement φ ψ` means that there
are an actual saturated presentation `T` and complete strong maps
`a : T → φ.X'` and `b : T → ψ.X'` for which

```text
a ≫ φ.s = b ≫ ψ.s,
a ≫ φ.f = b ≫ ψ.f,
(a ≫ φ.s).IsQuasiIso.
```

Both equations are equalities of entire strong maps, including every
bounded pullback. The condition requires a full quasi-isomorphism for the
common denominator; it does not separately require that `a` and `b` are
quasi-isomorphisms.

`localizedRightFraction_eq_iff` states that the two interpreted arrows are
equal if and only if this common refinement exists. The definition matches
Mathlib's `RightFractionRel`, and the theorem is the right-fraction equality
theorem specialized to `Q` and `W`.

`rightFractionSetoid A B` uses the proved equivalence relation on fractions.
Its transitivity uses the right calculus. `rightFractionQuotientMap` descends
fraction interpretation to this quotient: the equality criterion proves
well-definedness. The same criterion proves injectivity by quotient
induction, and representation of every localized arrow proves surjectivity.
`rightFractionHomEquiv` is the resulting actual equivalence

```text
Quotient (rightFractionSetoid A B) ≃ (Q(A) → Q(B)).
```

The theorem `rightFractionHomEquiv_mk` records that the equivalence sends the
class of `φ` to its interpreted arrow. This computes a hom set of the
existing localization; it does not introduce a replacement category.

For original `f g : A → B`, `localizationFunctor_map_eq_iff` further states
that `Q(f) = Q(g)` precisely when there are an actual saturated `T` and full
quasi-isomorphism `s : T → A` such that `s ≫ f = s ≫ g`. This is equality
after source refinement. No claim that `Q` is faithful follows here from the
previously proved cancellation after postcomposition by quasi-isomorphisms.

## Underlying continuous maps

The earlier `localizedSpaceFunctor` extends the literal space functor and
sends a formal quasi-isomorphism inverse to its ambient inverse
homeomorphism. `localizedSpaceFunctor_map_rightFraction` proves the exact
continuous-map formula

```text
localizedSpaceFunctor.map (localizedRightFraction φ)
  = TopCat.ofHom (φ.f.baseMap.comp φ.hs.inverseBaseMap).
```

Thus a point first passes through the denominator's inverse homeomorphism,
then through the numerator's actual continuous map. The proof applies
functoriality to the fraction composite and substitutes the two already
proved map formulas by congruence of composition. The target equality
retains the continuous topology, rather than only the underlying function.
`localizedSpaceFunctor_map_representative` gives the same formula for any
localized arrow using its chosen representative and its proved interpretation
identity.

## Remaining scope

This unit computes representatives, equality and underlying continuous maps
in the actual saturated presentation localization. It does not identify
that category with an independently defined Berkovich analytic-space
category, construct etale, quasi-etale or equivariant sites, implement compact
or distinguished domains, or specialize to Harris towers. Those remain
obligations of the surrounding analytic-space and site task. Independent
review and publication of the preceding Ore and right-calculus units remain
their own gates.
