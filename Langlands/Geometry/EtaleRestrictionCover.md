# Restriction to a covering family of small-etale objects

This is an internal construction extending `EtalePullback` and
`EtalePullbackAdjunction`. It constructs the actual functor restricting a sheaf
to each member of an etale family and proves that a covering family detects
isomorphisms. For module coefficients the functor preserves and reflects
limits of the stated sizes. It does not assume an inverse-image exactness or
base-change theorem.

## The family restriction functor

Let `X : Scheme.{u}`, let `ι : Type v`, and let `U : ι → X.Etale`.
The coefficient category `A : Type uA` has morphisms in an independent universe
`vA`. The construction
`Langlands.Geometry.EtaleRestrictionCover.restrictionFamily U A`
has source `Sheaf X.smallEtaleTopology A` and target
`∀ i, Sheaf (U i).left.smallEtaleTopology A`. It is `Functor.pi'` applied to
the existing actual etale restriction functors. Thus its object and morphism
components are precisely restriction along `(U i).hom`; no substitute sheaf
or supplied equivalence is used.

For an arrow `b : W ⟶ V` in `X.Etale`, `arrowDomain b` is the actual
small-etale object over `V.left` with underlying scheme `W.left` and structure
map `b.left`. This map is etale because its composite with `V.hom` is `W.hom`
and both original structure maps are etale. `arrowDomainIso b` identifies its
image under composition with the original object `W`, by the identity
isomorphism of the underlying scheme.

## Detecting isomorphisms

The covering hypothesis is the actual Grothendieck-topology condition
`X.smallEtaleTopology.CoversTop U`: the sieve of objects admitting an arrow
to some `U i` covers every object of the small-etale site.

For a sheaf morphism `a`, `isIso_app_of_restriction` shows that if restriction
to `V.left` makes `a` an isomorphism, then the component of `a` at every
object `W` mapping to `V` is an isomorphism. It evaluates the restricted
morphism at `arrowDomain b` and transports along `arrowDomainIso b` using
Mathlib's `NatTrans.isIso_app_iff_of_iso`.

Consequently each Mathlib over-site restriction of `a` to `U i` is an
isomorphism. `isIso_of_restrictionFamily` applies the existing sheaf
gluing result `CategoryTheory.Sheaf.isIso_of_coversTop` from
`Mathlib/CategoryTheory/Sites/LocalProperties.lean`. That result constructs
and glues the local inverses using the sheaf condition.
`restrictionFamilyReflectsIsomorphisms` packages the conclusion as
`Functor.ReflectsIsomorphisms` for the actual product restriction functor.
The proof obtains each component isomorphism by the actual `Pi.eval` functor.
There is no finiteness or nonemptiness hypothesis on the indexing family.

`coversTop_of_jointlySurjective` supplies the site covering condition from
the explicit geometric hypothesis
`∀ x : X, ∃ i y, (U i).hom y = x`.
The proof checks the sieve at the terminal identity object, using Mathlib's
`GrothendieckTopology.coversTop_iff_of_isTerminal` and the existing
`EtaleAutomorphism.mem_smallEtaleTopology_iff` characterization by point
lifts. `coverObjects` turns a genuine
`X.Cover (Scheme.precoverage (@Etale))` into the corresponding family of
small-etale objects; `coverObjects_coversTop` uses the cover's proved joint
surjectivity (`Scheme.Cover.exists_eq`).

## Limits of module sheaves

For a commutative ring `R : Type u`, coefficients remain
`ModuleCat.{u} R`. The family functor preserves limits of shapes with objects
and morphisms in universe `u`, as recorded by
`restrictionFamily_preservesLimits : PreservesLimitsOfSize.{u,u} ...`.
The proof uses the actual extension/restriction adjunction from
`EtalePullbackAdjunction` in each component. It constructs a limiting lift
component by component; factorization and uniqueness are the corresponding
properties of those component limit cones. The family index universe `v`
remains independent. This does not claim existence or preservation of
arbitrarily larger limits of `ModuleCat.{u} R`.

For a covering family, `restrictionFamilyReflectsLimits` proves reflection
of limits of those same sizes. The module-sheaf source category has these
limits, the family functor preserves them, and it reflects isomorphisms.
Mathlib's `reflectsLimits_of_reflectsIsomorphisms` therefore applies.
The final instance and theorem also expose preservation and reflection of
finite limits without a fixed diagram universe. None of these results
asserts a descent equivalence of categories or general-base exactness of the
separately constructed inverse image.
