# Locality of character automorphisms of diagonalizable group schemes

Let `R` be any commutative ring and let `M,N` be abelian groups in the scheme
universe, with `N` finitely generated as an additive monoid. For an actual
group-scheme isomorphism `e : D_R(M) ≅ D_R(N)`, each point of `Spec R` has an
affine open neighborhood on which its base change agrees with restriction of
characters along a single additive equivalence `N ≃+ M`.

`exists_away_eq_restrictMap` gives this as a principal localization at an element
outside a specified prime. `exists_open_neighborhood_eq_restrictMap` expresses it
as an actual open immersion from a spectrum whose range contains the point.
`localCharacterModel` chooses that spectrum, open immersion, character equivalence,
and equality of the actual base-changed group morphisms.

The proof first takes Hopf coordinates using the full faithfulness of `hopfSpec`.
The standard Hopf spectrum comparison has the identity underlying scheme map.
The algebraic certificate from `DiagonalAutomorphismLocality` then supplies one
coefficient product and one character equivalence. Equality in scalar-extension
coordinates implies equality of the tensor maps and hence of the actual
base-changed morphisms, using `HopfMorphismBaseChange.tensorSpecIso_naturality`.
The restriction-of-characters morphism has the expected degree-map coordinates
by `restrictMap_left`.

The auxiliary `baseChangeIso_restrictMap` proves naturality of the canonical
diagonalizable base-change comparison with respect to character restriction.
It uses the character-valued points on every test scheme and the base-change
point equivalence.

The result is derived from these imported Library constructions and Mathlib.
It requires no field, reducedness, Noetherian condition, or smoothness. The
arbitrary-test-scheme locality adapter is a separate step.
