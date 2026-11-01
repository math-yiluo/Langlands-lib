# Coherence of constructed small-etale inverse images

This module proves both identity laws and the associativity law for the
constructed inverse-image comparisons in `EtaleImageFunctoriality`.
It constructs the triple comparison and proves equality with the route
that combines the other adjacent pair first.

All schemes have universe `u`; the commutative ring `R : Type u` and
the module carriers also have universe `u`. Every base morphism is
arbitrary. There is no etaleness, finiteness, finite-type, Noetherian,
field, coefficient-freeness or local-constancy assumption.

This is internal categorical infrastructure derived from the actual
inverse/direct-image adjunctions, the geometric direct-image comparisons
and their proved coherence, and Mathlib's conjugation of adjunctions.
It makes no new external-literature claim.

## Identifying the actual adjoint comparisons

Write `L_f := inverseImage f R`, `D_f` for geometric direct image
with coefficients in `ModuleCat.{u} R`, and `A_f` for the actual
constructed adjunction `L_f ⊣ D_f`. The inverse-image comparisons
were constructed by transporting or composing these adjunctions
and applying uniqueness of left adjoints.

Mathlib's `conjugateEquiv a b` is a bijection from natural
transformations between the left adjoints, in reverse order,
to transformations between the right adjoints. A private general
lemma computes it on precisely that construction: given actual
adjunctions `a : L ⊣ G`, `b : L' ⊣ G'` and `e : G ≅ G'`, the
conjugate under `b` and `a` of
`(a.ofNatIsoRight e).leftAdjointUniq b` is `e.inv`.

The proof applies injectivity of the inverse Hom correspondence of
`a` at each component. The counit formula for conjugation and
the counit equation for uniqueness of left adjoints reduce the
claim to the actual transported counit. No comparison or
compatibility is supplied as an assumption.

`conjugate_inverseImageId`, `conjugate_inverseImageCongr` and
`conjugate_inverseImageComp` specialize this lemma to the existing
identity, equality and composition comparisons. Their conjugates
are exactly the inverses of `directImageId`, `directImageCongr`
and `directImageComp`, respectively.

## The two identity equations

For `f : Z ⟶ X`, `inverseImageComp_id_target` proves that the
following two routes from `L_(𝟙 X) ⋙ L_f` to `L_f` agree:

- Compose by `inverseImageComp R (𝟙 X) f`, then transport through
  the equality `f ≫ 𝟙 X = f`.
- Apply `inverseImageId R X` to the first factor, then the left
  unitor of `L_f`.

`inverseImageComp_id_source` proves the analogous equation from
`L_f ⋙ L_(𝟙 Z)`: compose and transport through
`𝟙 Z ≫ f = f`, or apply the identity comparison to the second
factor and then the right unitor.

Both proofs use injectivity of conjugation. Mathlib's composition,
whiskering and unitor formulas for conjugation, followed by the
three computed conjugates, reduce the desired equation to the
corresponding already proved geometric direct-image identity
equation. Evaluation at a sheaf and cancellation of inverse
comparisons finish the proof.

## Associativity and the triple comparison

For `f : Z ⟶ X`, `g : V ⟶ Z` and `h : W ⟶ V`,
`inverseImageComp_assoc` compares the two routes from
`(L_f ⋙ L_g) ⋙ L_h` to `L_(h ≫ (g ≫ f))`:

- First combine `f` and `g`, then combine `g ≫ f` with `h`.
- Apply the functor associator, first combine `g` and `h`,
  combine `f` with `h ≫ g`, and then transport through
  `(h ≫ g) ≫ f = h ≫ (g ≫ f)`.

The proof again applies injectivity of conjugation. Its
composition, whiskering and associator laws reduce the claim
to an equation between inverse direct-image comparisons.
The existing forward direct-image associativity equation
is packaged as an equality of composite isomorphisms.
Taking their inverses and cancelling the equality comparison
gives exactly the required equation. Every functor associator
and base-map equality comparison is retained.

`inverseImageTripleComp` constructs the first of these routes
as a natural isomorphism.
`inverseImageTripleComp_eq` proves that this isomorphism equals
the full alternative composite in the second route. Equality
of isomorphisms follows from the proved equality of their
forward transformations.

These laws concern ordinary module sheaves and arbitrary
base morphisms. Arbitrary-map finite-limit preservation,
exactness, comparison with associated torsor coefficients
or algebraic-closure base change, equivariant and smooth
sheaf adapters, support and derived comparisons, and Harris
specialization remain separate obligations.
