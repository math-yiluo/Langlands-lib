# Cocharacters on canonical finite arithmetic enlargements

This internal construction starts with a supplied generic cocharacter and a
supplied actual integral model. It extends that cocharacter after enlarging a
finite set of places, without replacing the prescribed model by an unrelated
one. All rings, fields, schemes and group schemes use the arbitrary universe `u`.

## A cocharacter from a compatible model homomorphism

Let `R` and `A` be domains with supplied fraction field `K`, and let
`b : Spec A ⟶ Spec R` satisfy
`Spec.algebraMap A K ≫ b = Spec.algebraMap R K`. For an actual model
`M : IntegralModel R K G` and a supplied cocharacter
`χ : Gm(K) ⟶ G`, `cocharacterOfHom` takes an `IntegralModel.Hom` extending `χ`
from the pullback of `multiplicative R K` to the same pullback of `M`.
Its value is the actual group-scheme homomorphism
`(Gm.baseChangeIso b).inv ≫ f.hom`, with source the canonical `Gm` over `A`.

`cocharacterOfHom_generic` proves the exact identity

```text
Dynamic.baseChangeCocharacter (Spec.algebraMap A K) (cocharacterOfHom M b hb f)
  ≫ (M.baseChangeModel b hb).genericIso.hom = χ.
```

The generic comparison is the one already prescribed by `baseChangeModel`.
The proof first establishes coherence of `Gm.baseChangeIso` with the
specified-composite `Descent.pullbackComparison`. It tests the two group
homomorphisms on every test scheme, uses the global-unit descriptions of
multiplicative points and base change, and reduces their equality to the
projection to the original Laurent-spectrum model. This identifies the generic
isomorphism of the pulled-back canonical multiplicative model with the two
successive canonical multiplicative comparisons. Functoriality, `f.generic_comm`
and the inverse-isomorphism identities then prove the displayed equality.

## Finite arithmetic enlargement

Fix a number field `F`, a finite set `S` of its actual finite places, and a model
`M` over the actual subalgebra `(S : Set (FinitePlace F)).integer F`. Assume
`LocallyOfFinitePresentation M.group.X.hom`. For every supplied generic
cocharacter `χ`, `ArithmeticSpreading.enlargedCocharacterData F S M χ` returns:

- a finite set `places` containing `S`;
- an actual cocharacter over its actual S-integer ring, with target exactly
  `ArithmeticSpreading.enlargeModel F M contains`;
- the exact `generic_comm` identity recovering this supplied `χ` through that
  enlarged model's specified generic isomorphism.

The construction applies `enlargedHomData` to the canonical multiplicative model
and `M`, then applies the general adapter and its recovery theorem. Enlargement
uses `numberFieldSIntegersMap`, the literal inclusion of S-integer subrings in `F`;
`integerInclusion_generic` identifies its composite with the original inclusion.
The finite-presentation premise is precisely the target premise of the imported
homomorphism descent theorem. No smoothness or reductivity premise is added here.

## Provenance and scope

These are derived internal constructions from actual multiplicative models,
finite-coefficient homomorphism descent, arithmetic coefficient containment and
pullback coherence. The proof supplies no new external literature theorem.
It assumes the generic cocharacter and initial integral model. It does not
construct a cocharacter presenting a supplied parabolic, prove generic
reductivity openness, or establish the host simultaneous spreading theorem.
