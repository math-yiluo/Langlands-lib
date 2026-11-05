# Coherent action transport for repeated Harris test restriction

This internal deduction constructs the canonical composite Harris action
comparison and proves composition laws for the literal integral action
and the underlying rational maps of the canonical Harris action comparisons.
It imports the unchanged `HarrisIntegralCMLevelRestriction` module and uses the
published Cartier restriction, abelian pullback and rationalization constructions.
There is no additional literature claim.

The arithmetic data, schemes and abelian family are in universe zero. Fix the
Harris signature charts `C`, the associated full integral order and its published
integer basis, an abelian scheme `B` over `S`, three objects `T`, `T'`, `T''` of
`Over S`, morphisms `f : T' ⟶ T` and `g : T'' ⟶ T'`, and an action `a` of that
order on `B` pulled back along `T.hom`. The two public lemmas do not require
polarization data, geometric points, quasi-separatedness or torsion hypotheses.

`harrisIntegralCMRestrictionAction_comp` proves equality of ring homomorphisms

```
(relativeEndRestrict B g).comp ((relativeEndRestrict B f).comp a)
  = (relativeEndRestrict B (g ≫ f)).comp a.
```

The proof specializes the published actual Cartier `restrict_comp` law to
endomorphisms, obtains equality of the restriction ring homomorphisms by
extensionality, and composes that equality with the original action `a`.

For a morphism `k` and the appropriate integral action `b`, write `c(k,b)` for
the underlying rational homomorphism of the published
`relativeIntegralActionRationalComparisonIso B
(D.harrisHodgePELIntegralBasis C) k b`. Write `p` for the forward homomorphism
of `rationalBaseChangeCompIso f.left g.left` on `B` pulled back along `T.hom`.
`harrisIntegralCMCompositeRestrictionComparisonIso` constructs an equivariant
rational isomorphism from the action restricted along `g ≫ f` to the successive
ordinary pullback of the original rationalized action. It composes the relative
integral-action comparison for `g ≫ f` with the published equivariant ordinary
pullback composition comparison. Its underlying homomorphism is
`c(g ≫ f,a) ≫ p`. The source uses the literal composite-restricted integral
action, rationally extended using the original integer basis.

`harrisIntegralCMRestrictionRationalComparison_comp` identifies the underlying
homomorphism of this defined isomorphism with the successive comparisons:

```
c(g ≫ f,a) ≫ p
  = c(g,(relativeEndRestrict B f).comp a) ≫ g.left*(c(f,a)).
```

Here `g.left*` is the actual rational pullback map `rationalBaseChangeHom`.
The Lean statement writes the right-hand composition using `comp0` with explicit
abelian-scheme sources and targets. Both sides run from `B` pulled back along
`T''.hom` to the successive ordinary pullback along `T.hom`, `f.left`, and
`g.left`. This is an equality of underlying rational homomorphisms; it does not
assert an equality of bundled equivariant isomorphisms with different source
action expressions.

The implemented proof first establishes the corresponding private equality
of integral family comparisons. It compares the inverses of the two composite
isomorphisms, reduces to morphisms of schemes over `T''.left`, and uses the two
projections of the defining pullback. Published projection formulas for ordinary
and relative pullback comparisons and for pullback of a morphism prove the first
projection identity. The structure-morphism equation proves the second.
Rationalizing this equality proves the public theorem: the underlying action
comparison is definitionally the rationalization of the family comparison,
ordinary rational pullback sends integral homomorphisms to the pullback of those
homomorphisms, and `comp0_homToHom0` preserves their composition.

Composition of the original raw level restrictions, compatibility under test
precomposition, and the natural comparison on the full normalized moduli
presheaf remain open. This pair supplies no representing scheme, admissibility,
smoothness or projectivity result for `DivisionCMRepresentabilityStatement`.
