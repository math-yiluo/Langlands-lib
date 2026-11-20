# Additivity and global sections of ordinary restriction

The [ordinary restriction](Conditional.md) takes explicit
`hOpen : EtaleOpenDomainStatement X`. It is additive for any preadditive
coefficient category, including `ModuleCat.{max u (v + 1) uL} R` for a
commutative ring `R : Type (max u (v + 1) uL)`. On sheaf morphisms it
evaluates the original natural transformations at the opposites of the
open-domain objects. `TopCat.Sheaf` inherits the canonical pointwise
addition of sheaves on the open-set site. The additivity proof is the
resulting pointwise equality under precomposition.
When sheafification supplies the abelian structure on `TopCat.Sheaf`, the
same proof gives an instance for its inherited addition.

`openEtaleToSelf` is the canonical inclusion of an open analytic domain as an
arrow to the étale identity object. For the whole space it is an isomorphism.
Its inverse is the lift of the identity into the full open domain. The
composite into the domain is the identity by uniqueness of the lift. The
composite into the identity object is the identity by the equation for a
morphism over `X`.

`etaleUnderlyingGlobalNatIso` identifies evaluation by `etaleSections` at
`etaleSelf X` with evaluation of the restricted sheaf at `⊤` by
`sheafSectionsModule`. A component applies the original presheaf to the
opposite of the full-domain isomorphism. Naturality is the sheaf morphism's
naturality on the opposite of the full-domain inclusion. Composing the
component with ordinary restriction to `U` is the original restriction along
`openEtaleToSelf X hOpen U`, since the inclusions commute over `X`.

The conditional full-domain identification generalizes the Library's
pointwise comparison and uses the Library section functors. Its source setting
is Berkovich's open-subset functor in *Étale cohomology for non-Archimedean
analytic spaces* (1993), §4.2, printed p. 87. The ordinary restriction used
here is the one in the definition of softness and in Lemma 3.2 of his
*Vanishing cycles for formal schemes* (1994), §3, printed p. 544.
