# Gluing group schemes over an arbitrary disjoint decomposition

This internal construction glues a family of group schemes over the
components of a disjoint decomposition of a base scheme, for an arbitrary
index type. It generalizes the Library's `Descent.DisjointGroupAssembly`,
which requires a finite index type. The construction is motivated by the
same source as that module: the disjoint-union presentation in Brian Conrad,
*Reductive group schemes* (2014), Proposition 6.4.4 and Remark 6.4.5,
pp.232–233 (`conrad-2014-reductive-group-schemes`). It was written for the
proof of Conrad's Proposition B.3.8 (groups of multiplicative type are closed
subgroups of tori), which needs index types that need not be finite.

## Setting

The index type `I : Type u` is arbitrary; it may be infinite or empty. The
base decomposition is given by morphisms `p i : Z i ⟶ S` such that the induced
morphism `Sigma.desc p : ∐ Z ⟶ S` is an isomorphism. `H i` is a group scheme
over `Z i`. No affineness, finiteness or flatness is assumed.

## Declarations

- `underlying p H : Over S` is the coproduct of the underlying schemes of the
  `H i`, with the morphism to `S` induced by the composites
  `(H i).X.hom ≫ p i`.
- `underlying_hom` states that this structure morphism equals
  `Sigma.map (fun i => (H i).X.hom) ≫ Sigma.desc p`.
- `component_isPullback i` states that the square with the coproduct
  inclusion of the `i`-th component, `(H i).X.hom`, the structure morphism of
  `underlying p H` and `p i` is a pullback square.
- `componentUnderlyingIso i` identifies the slice pullback of
  `underlying p H` along `p i` with `(H i).X`.
- `familyGrpObj H` and `familyGroup H` are the pointwise group object on the
  family `fun i => (H i).X` in the product category `∀ i, Over (Z i)`.
  `family_essImage` and `familyGroup_essImage` state that the family and the
  family group lie in the essential image of component restriction and of the
  restriction functor on group objects.
- `group p H : GroupScheme S` is a chosen group object over `S` whose
  restriction is `familyGroup H`. `familyIso` is the chosen isomorphism.
- `componentIso i : (baseChange (p i)).obj (group p H) ≅ H i` is an
  isomorphism of group schemes over `Z i`, compatible with the unit and the
  multiplication.
- `underlyingIso : (group p H).X ≅ underlying p H` identifies the underlying
  relative scheme of the glued group with the coproduct over `S`. This is an
  isomorphism over `S`, not a definitional equality. `group_X_hom` restates
  this as a factorization of the structure morphism of `group p H`.
- An instance states that `(group p H).X.hom` is an affine morphism whenever
  every `(H i).X.hom` is affine.

## Proof

The group-object part is the argument of `Descent.DisjointGroupAssembly`,
with the Library's arbitrary-index `Descent.DisjointComponentHoms` in place of
the finite one. Component restriction `DisjointComponents.restriction p` is
fully faithful (`DisjointComponents.restrictionFullyFaithful`). Hence its
induced functor on group objects reflects the essential image
(`Functor.essImage_mapGrp`). So it suffices that the underlying family is
in the essential image, which `componentUnderlyingIso` gives.
`componentIso` and `underlyingIso` are read off from `familyIso`. They use
the full faithfulness for the underlying-object identification.

The finite version obtains the pullback squares from the van Kampen property
of finite coproducts (`FinitaryExtensive.isVanKampen_finiteCoproducts`). Here `component_isPullback` is obtained by pasting two
pullback squares instead:

1. The flip of `isPullback_sigmaι_sigmaMap` from the Library module
   `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap`
   (an Apache-2.0 port from the Anthropic Lean formalisation of Fermat's Last
   Theorem). For a family of morphisms `f i : X i ⟶ Y i` indexed by an
   arbitrary small type, this square has the inclusion `X j ⟶ ∐ X`, `f j`,
   `Sigma.map f` and the inclusion `Y j ⟶ ∐ Y`. Here `f i = (H i).X.hom`.
2. The square with the inclusion `Z i ⟶ ∐ Z`, the identity of `Z i`, the
   isomorphism `Sigma.desc p` and `p i`. It is a pullback by
   `IsPullback.of_vert_isIso`.

Vertical pasting and `underlying_hom` give the stated square.

For the affineness instance, `solution` from the same FLT port module shows
that `Sigma.map` of a family of morphisms with a Zariski-local-at-target
property has that property. Affineness is such a property. Composing with the
isomorphism `Sigma.desc p` (via `underlying_hom`) and with `underlyingIso`
(via `group_X_hom`) preserves affineness. The finite version instead states
that the total scheme is affine when every component scheme is affine; that
statement fails in general for infinite index types and is not included here.
