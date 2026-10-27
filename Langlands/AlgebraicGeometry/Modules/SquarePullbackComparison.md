# Pullback comparison around a commutative square

This is an internal coherence construction for actual module-sheaf pullbacks.
Let `p : X → Y`, `p′ : X′ → Y′`, `s : X′ → X`, and `t : Y′ → Y`
be scheme morphisms, with `p′ ≫ t = s ≫ p`. For an actual module `M` on `Y`,
`squarePullbackIso` is the canonical isomorphism
`p′* t* M ≅ s* p* M`. It composes `pullbackComp p′ t`, pullback along the
supplied equality, and the inverse of `pullbackComp s p`.

`squarePullbackIso_comp` says that, after further pullback along any
`a : V → X′`, composing this comparison with the composition comparison
for `a,s` and the generalized comparison to any common composite `z : V → Y`
agrees with the comparison through `a,p′,t`.

For `a,b : V → X′` satisfying `a ≫ p′ = b ≫ p′` and
`(a ≫ s) ≫ p = (b ≫ s) ≫ p`, `equalCompositeIso_square` states

```
a*(square).hom ≫ comp(a,s) ≫ equalComposite(p,a≫s,b≫s).hom
  = equalComposite(p′,a,b).hom ≫ b*(square).hom ≫ comp(b,s).
```

Thus the ordinary equal-composite comparison commutes with the actual square.
Given an actual trivialization `α : p* M ≅ O_X`,
`equalCompositeUnitAut_square` identifies the normalized automorphism for
`p′,a,b` using the pulled-back trivialization
`square ≪≫ s*(α) ≪≫ pullbackUnitIso s` with the normalized automorphism for
`p,a≫s,b≫s` using `α`. It uses the same forward equal-composite comparison
as `EqualCompositePullback` and introduces no inverse convention.

The implementation derives the square composition equation from two instances
of the published generalized associativity lemma `compHom_assoc`.
`pullbackCongr_compHom` is the equality-substitution helper that removes a
change between equal maps before a generalized composition comparison.
Cancellation of the final composition isomorphism proves
`equalCompositeIso_square`. Naturality of `pullbackComp` in `α`, compatibility
of `pullbackUnitIso` with composition, and cancellation of inverse square
isomorphisms prove the normalized automorphism equation.

This unit is derived from the existing module-pullback pseudofunctor and its
proved unit and associativity laws. It is a reusable prerequisite for the
intrinsic kernel character's test-scheme law, with no abelian-scheme,
constant-functions, descent or duality assertion of its own.
