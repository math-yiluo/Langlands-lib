# Faithful flatness of diagonalizable group algebras along injective lattice maps

Let `g : Λ' →+ Λ` be an injective homomorphism of additive commutative groups. This module
proves that the group algebra map `mapDomain g : R[Λ'] → R[Λ]` is faithfully flat over every
nonzero commutative ring `R`. It follows that the induced homomorphism `D(Λ) → D(Λ')` of
diagonalizable group schemes ([`Diagonalizable`](Diagonalizable.md)) is flat and surjective.
All declarations are in `Langlands.GroupScheme.Diagonalizable`.

Provenance: these are internal helper results for the proof of
`Langlands.GroupScheme.RelativeRoot.CharacterFpqcStatement`
([`CharacterFpqcProof`](../Rational/CharacterFpqcProof.md)). The algebra is the standard fact
that a group algebra is free over the group algebra of a subgroup, with a basis given by
coset representatives. The module cites no particular source for it.

## Freeness of `R[Λ]` over `R[Λ']`

This section works over any commutative ring `R` and any universe levels.

- `cosetRep q` is the chosen representative `Quotient.out q` of a coset `q ∈ Λ / g(Λ')`.
- `cosetCoord hg l : Λ'` is the unique `l'` with `g l' = -cosetRep [l] + l`. It is defined
  through `AddMonoidHom.ofInjective hg`. `map_cosetCoord` records this equation and
  `cosetRep_add_map_cosetCoord` rearranges it to `cosetRep [l] + g (cosetCoord hg l) = l`.
- `mk_cosetRep_add` and `cosetCoord_cosetRep_add` compute the coset and the coordinate of
  `cosetRep q + g l'`.
- `cosetEquiv hg : Λ ≃ (Λ / g(Λ')) × Λ'` sends `l` to `([l], cosetCoord hg l)`. Its inverse
  sends `(q, l')` to `cosetRep q + g l'` (`cosetEquiv_symm_apply`).
- `cosetLinearEquiv hg R : ((Λ / g(Λ')) →₀ R[Λ']) ≃ₗ[R] R[Λ]` is the `R`-linear equivalence
  of coefficient functions obtained from `cosetEquiv` by currying (Mathlib's
  `Finsupp.curryLinearEquiv`, `Finsupp.domLCongr`, `AddMonoidAlgebra.coeffLinearEquiv`).
  `cosetLinearEquiv_single_single` says it sends `single q (single l' r)` to
  `single (cosetRep q + g l') r`.
- `mapDomainAlgebra R` is the `R[Λ']`-algebra structure on `R[Λ]` given by
  `AddMonoidAlgebra.mapDomainRingHom R g`.
- `cosetLinearMap R` is the `R[Λ']`-linear map `(Λ / g(Λ')) →₀ R[Λ'] → R[Λ]` that sends the
  basis vector at `q` to the monomial `single (cosetRep q) 1`. It is Mathlib's
  `Finsupp.linearCombination`.
- `cosetLinearMap_apply`: `cosetLinearMap R` and `cosetLinearEquiv hg R` agree as functions.
  The proof is by induction on finitely supported functions and on group algebra elements. On
  `single q (single l' a)` both sides equal `single (cosetRep q + g l') a`, because
  `mapDomain g (single l' a) * single (cosetRep q) 1 = single (g l' + cosetRep q) a`.
- `cosetLinearMap_bijective`: hence `cosetLinearMap R` is bijective.
- `free_mapDomainAlgebra`: so `R[Λ]` is a free `R[Λ']`-module along `g`, with basis indexed
  by `Λ / g(Λ')`.
- `faithfullyFlat_mapDomainRingHom`: if moreover `R` is nontrivial, the ring map
  `AddMonoidAlgebra.mapDomainRingHom R g` is faithfully flat. `R[Λ]` is then a nontrivial
  free `R[Λ']`-module, and Mathlib's instance for nontrivial free modules makes it
  faithfully flat. Mathlib's `RingHom.faithfullyFlat_algebraMap_iff` converts this into the
  statement about the ring map.

No hypothesis on `Λ` or `Λ'` is needed beyond injectivity of `g`. In particular neither group
needs to be finitely generated or torsion free, and `R` may have any characteristic.

## The induced morphism of diagonalizable group schemes

Here `R : CommRingCat.{u}`, and `Λ`, `Λ'` are additive commutative groups in universe `u`, so
that `D(Λ)` and `D(Λ')` are defined. `g : Λ' →+ Λ` is any homomorphism.

- `incl_toRingHom`: the published algebra map `incl R g : R[Λ'] → R[Λ]` has underlying ring
  map `mapDomainRingHom R g`. This is the published `incl_apply`.
- `homEquiv_symm_restrict_id`: the published restriction of characters
  `restrict R g : functor R Λ ⟶ functor R Λ'` is classified by `incl R g`. It is the
  published `homEquiv_symm_restrict` applied to the universal character of `R[Λ]`.
- `restrictMap R g : D(Λ) ⟶ D(Λ')` is the group scheme homomorphism
  `Corepresented.groupSchemeMap` induced by `restrict R g`.
- `restrictMap_left`: the underlying scheme morphism of `restrictMap R g` is
  `Spec.map (CommRingCat.ofHom (mapDomainRingHom R g))`. The proof combines the published
  `Corepresented.groupSchemeMap_hom` with the two previous lemmas.
- `flat_and_surjective_restrictMap`: if `R` is nontrivial and `g` is injective, then the
  underlying scheme morphism of `restrictMap R g` is flat and surjective. It is `Spec` of a
  faithfully flat ring map (`faithfullyFlat_mapDomainRingHom`). Mathlib's
  `flat_and_surjective_SpecMap_iff` says exactly that such a `Spec.map` is flat and
  surjective.
- `pointsEquiv_restrictMap`: on points over a test scheme `T`, `restrictMap R g` restricts
  characters along `g`. Write a `T`-point `x` of `D(Λ)` as a character `χ` of `Λ` with values
  in `Γ(T, 𝒪_T)ˣ`, using the published `Corepresented.pointsEquiv`. Then the character of
  `x ≫ restrictMap R g` takes the value `χ(g l')` at `l'`. This is the published
  `Corepresented.groupSchemeMap_points` together with `restrict_app_apply`.
