# Regularity and local Picard vanishing for smooth valuation algebras

This is an internal derivation from Mathlib's actual local etale polynomial
factorization and the imported etale valuation chart regularity and
localization-Picard theorems. It applies in one arbitrary universe.

`SmoothEtaleNeighborhood` retains an actual element outside a supplied ideal,
a finite number of polynomial variables, and a compatible algebra action
making the corresponding basic-open localization etale over that polynomial
ring. `smoothEtaleNeighborhood` chooses such data at a smooth prime of a
finitely presented algebra using
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`. In particular the
polynomial action is actual algebra data, not an assumed extension theorem.

The ring-isomorphism lemma transports the existing
`FinitelyPresentedRegularRing` predicate. A ring isomorphism makes its target
a free rank-one coefficient module, hence finitely presented. Coherence
passes by the imported module-finite-presentation permanence theorem.
Restriction of scalars makes every finitely presented target module
finitely presented over the source. The identity on its underlying additive
group is an actual semilinear equivalence, which transports the
projective-dimension witness. This also transports regularity to any
algebra model of a localization, by the canonical localization equivalence.

Over an arbitrary valuation domain, the chosen neighborhood has the
imported etale polynomial chart regularity. To apply the common-universe
chart theorem to Mathlib's natural-number-sized index `Fin n`, the proof
renames the variables along `ULift (Fin n) ≃ Fin n`. It composes the
resulting polynomial ring isomorphism with the actual chart algebra map.
The composite remains etale, and its coefficient action is compatible
by the algebra equivalence's commutation with constants. Thus the universe
lift changes no ring or geometric neighborhood. If its element is outside the
prime `p`, the extension of `p` to the neighborhood is prime and contracts
back to `p`. Its local ring is therefore an actual localization model for
`S_p`. Localizing neighborhood regularity and applying the canonical
equivalence proves regularity of `S_p`.

Finally, the imported coherent-local-ring theorem shows that every
localization of `S_p` has trivial module Picard group. All valuation ranks,
fields, and multiplicative sets are included. This module does not construct
a scheme line-bundle extension or a restriction isomorphism.
