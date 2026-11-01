# Equivariance of arbitrary-sieve locally constant gluing

Author: Worker 56.

This internal companion combines the actual domain-section pair action from
`ChosenAtlasLocallyConstantAction` with the target-sieve pullback construction
from `ChosenAtlasLocallyConstantSievePullback`. It constructs pairs for the
literal target glue and for the source glue of its full pulled-back matching
family. Transport identifies the complete pairs, and restriction recovers
each complete original target local pair. Specializing to `Action.ρAut g`
proves these facts for the actual induced algebraic group action.

## Provenance and hypotheses

This is an internal construction from the existing interfaces, rather than
a new theorem attributed to the literature.
`OriginalDomainLocallyConstantSheaf` constructs the full locally constant
section presheaf and its glue for every compatible family on every covering
sieve. Its restrictions precompose with literal domain inclusions.
`OriginalDomainLocallyConstantLocalization` supplies coefficient
postcomposition and its compatibility with the constructed glue.
`ChosenAtlasLocallyConstantSievePullback` constructs the complete pulled-back
family through the actual chosen domain equivalence, proves its compatibility
and covering, and identifies its source glue with pullback of the literal
original target glue. Its inverse comparison recovers the original target
glue and every original target local value. The present module uses those
constructed functions and the complete domain-section pairs of
`ChosenAtlasLocallyConstantAction`.

The field `K : Type u` is a complete ultrametric normed field. Presentations
have point universe `v` and chart-index universe `w`. Coefficients
`D, E : Type z` and the group `G : Type t` have independent arbitrary
universes. No coefficient topology or coefficient action is assumed.
The general comparison takes a full isomorphism `e : A ≅ B` in the chosen
bounded atlas category, an original-chart domain `S` of `A`, and any sieve
`R` on its actual image `isoOriginalDomain e S` in `B`.

The input `p` is the entire `Presieve.FamilyOfElements` in the target
locally constant presheaf. Its `Compatible` hypothesis is matching along
all commuting restriction squares. `IsCovering R` is the full existing
quasinet covering condition: its finite local families have union a relative
neighborhood. The pullback construction derives this covering condition
on `R.functorPullback (isoOriginalDomainEquivalence e).functor`.
Point coverage alone does not replace that hypothesis.

## Glue as a complete domain-section pair

`OriginalDomainSection.sieveGlue p hp hR` is the pair

\[
  \bigl(S,\operatorname{locallyConstantSieveGlue}(p,hp,hR)\bigr).
\]

The section is the existing actual function constructed from the local
values, with local constancy proved by the quasinet criterion.
`sieveGlue_domain` exposes its actual domain. For every sieve member
`f : T ⟶ S`, `sieveGlue_restrict` proves that restricting this entire pair
to `T` gives exactly the original local pair `(T, p f hf)`.
The proof applies pair extensionality with identical domains and then the
source glue's original local value equation.

For every coefficient function `φ : D → E`, `sieveGlue_map` proves that
postcomposing this pair's section equals gluing the complete
coefficient-mapped matching family. Pair extensionality reduces this to
evaluation of the existing `locallyConstantSieveGlue_map` equation. The
mapped compatibility proof is derived by `Compatible.map`.

## Transport of arbitrary target-sieve gluing

`OriginalDomainSection.pullbackSieveGlue e p hp hR` constructs a pair over
the original source domain `S`. Its function is the glue of the entire
functorially pulled-back family
`isoOriginalDomainLocallyConstantPullbackFamily e p`, using the already
derived compatibility and covering proofs.

Write `T_e` for the complete pair transport from the action module. It
moves a domain by the actual forward base map and precomposes its section
with the inverse restricted homeomorphism. Then
`transport_pullbackSieveGlue` proves

\[
 T_e\bigl(\operatorname{pullbackSieveGlue}(e,p,hp,hR)\bigr)
   = \operatorname{sieveGlue}(p,hp,hR).
\]

Both pairs have the literal image domain. Pair extensionality reduces
their section equation to evaluation of
`isoOriginalDomainLocallyConstantPullbackGlue_descend`, which identifies
inverse transport of the constructed source function with the literal
target-site glue. No separate glue or comparison object is an input.

`transport_pullbackSieveGlue_restrict` recovers the full original local
pair for every target sieve member `f : T ⟶ isoOriginalDomain e S`.
Its proof evaluates the predecessor's target recovery equation at each
point of `T` and applies pair extensionality. The domain `T` is any target
original-chart domain; it need not be supplied as a direct image of a
source domain. `pullbackSieveGlue_map` proves coefficient compatibility
of the complete constructed source pair by evaluating the predecessor's
source glue coefficient equation.

## The actual induced group action and gluing

Let `X : Action (AffinoidAtlasPresentation K) G`. For each `g : G`,
`X.ρAut g` is the full chosen isomorphism constructed from the original
action arrow and its inverse-group-element arrow. The action on pairs
is exactly `OriginalDomainSection.transport (X.ρAut g)`.

`ChosenAtlasSectionAction.action_pullbackSieveGlue` applies the general
pair comparison to this full isomorphism. It states that the actual action
arrow at `g` sends the constructed pullback glue to the literal target
glue, as equality of complete pairs.
`action_pullbackSieveGlue_restrict` recovers each complete original
target local pair, and `action_pullbackSieveGlue_apply` exposes each
original local value at its literal target inclusion.
These are specializations of the general transport and target recovery
equations to the exact underlying function of the action arrow.

`coefficientMap_pullbackSieveGlue` applies the actual equivariant
coefficient morphism to the constructed source glue and identifies the
result with the source glue of the full coefficient-mapped target family.
`action_pullbackSieveGlue_map` proves that acting and then applying this
coefficient morphism gives the literal target glue of that mapped family.
The first is the general source-pair coefficient equation; the second
rewrites by the action-glue comparison and applies `sieveGlue_map`.
Identity and multiplication of the action are those already proved on
all pairs in `ChosenAtlasLocallyConstantAction`.

## Scope

There is no default coefficient value or inhabitedness assumption. Empty
domains, coefficient sets and sieves are retained precisely when the
supplied complete matching family and covering hypotheses exist. The
construction concerns full locally constant function sets on the
fixed-original-chart sites and full chosen atlas isomorphisms, including
their bounded algebra maps. It does not derive analyticity from an
arbitrary homeomorphism or invariance under arbitrary refinement.

The induced group action is algebraic. No group topology, continuity or
smoothness is asserted. The module proves compatibility of this concrete
action with arbitrary-sieve gluing; it does not construct a general
equivariant sheaf category, an analytic or etale site, or the Harris tower.
