# Character denominators and local finiteness of the actual affine roots

For supplied `B : ValuationBuildingData G`, the construction
`ValuationBuildingData.rootCharacterDenominator` assigns a positive integer
`d_a` to each character `a` of the actual split torus `B.S`. It has the
following defining property: there is an actual rational character `χ` of
the supplied centralizer `B.centralizer.Z` whose restriction to `B.S` is
`d_a • a`. The construction selects one positive integer from the proved
existence theorem; it does not claim minimality or uniqueness.

For every centralizer point `z`, the theorem
`rootCharacterDenominator_eval_translation` proves that

```text
d_a * a(ν(z))
```

is an integer, where `ν` is the actual centralizer translation supplied by
the existing character-normalized valuation.

With `hF : RelativeRoot.HasOppositeFactorPairs B.i`, the module proves
bounded finiteness of ordinary affine roots at every apartment point:

```text
∀ x bound, {ψ | ψ ∈ B.affineRoots ∧ |ψ x| ≤ bound ψ.linear}.Finite.
```

Here `bound` is any real-valued function on the dual reduced translation
space. Combining this with the four previously derived algebraic arrangement
laws gives
`isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs`, with no
additional geometric premise.

The setting retains arbitrary universe `u`, the nonarchimedean-local-field
instances on `F`, the actual affine group scheme `G`, and the supplied
`ValuationBuildingData`. Neither simple connectedness nor positive relative
rank is assumed.

## Character denominators

The actual factorization `B.centralizer.s : B.S → B.centralizer.Z` is a
central split torus. Closedness follows by factoring the closed split-torus
inclusion through the supplied closed centralizer inclusion. Centrality
follows from `isCentral_of_range_le_torusCentralizer`: the image of the
centralizer inclusion is precisely the actual torus centralizer.

The centralizer is affine and locally of finite type because its inclusion
is a closed immersion and `G` is affine and smooth. The published theorem
`CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict`
therefore applies. Every character of the split torus has a positive
multiple in the restriction range. The existing additive equivalence between
rational characters of a commutative group scheme and its character lattice
transports this assertion to `Cartan.characterRestriction`, giving
`exists_rootCharacterDenominator`.

The construction chooses the positive multiplier from this theorem. Its
positivity and character-extension properties are extracted in the next two
lemmas. The published normalization formula
`eval_centralizerTranslation` says that the evaluation of a restricted
centralizer character on `ν(z)` is the negative of its integer-valued
rational-character valuation. Substituting the character that restricts to
`d_a • a` proves integral evaluation after multiplication by `d_a`.

## Same-root reflection differences

Fix nonidentity points `g₀` and `g` in the same actual root group `U_a`,
together with actual opposite pairs `p₀` and `p`. Write their normalizer
elements as `m₀` and `m`, and their valuation functionals as `ψ₀` and `ψ`.
The existing theorem `reflectionElement_inv_mul_mem_centralizer` puts
`m₀⁻¹ * m` in the actual torus centralizer. The supplied representability
data lift this element to an actual `z ∈ B.centralizer.Z(F)`.

The theorem `reflectionFunctional_reflectionElement_same_root` computes

```text
ψ₀(m • x) = ψ₀(x) - 2 * ψ(x).
```

It uses the actual apartment action formula and the fact that the derivative
`a` takes value `2` on the actual opposite-pair coroot. Applying the same
formula to `m₀`, including its inverse point action, gives

```text
ψ₀((m₀⁻¹ * m) • x) - ψ₀(x) = 2 * (ψ(x) - ψ₀(x)).
```

Full supplied V6 identifies the left side with `a(ν(z))`. Consequently,
`rootValueDifference_integer` proves that

```text
2 * d_a * (ψ(x) - ψ₀(x))
```

is an integer. These comparison lemmas require the displayed actual pairs;
they do not assume a separate relative-root-system predicate, coroot
uniqueness, V7 or an apartment-axiom package.

## Bounded finiteness and facet fixing

For each actual relative root `a` and apartment point `x`, V0 supplies a
nonidentity `g₀ ∈ U_a` with finite valuation. The existence premise supplies
its actual opposite pair and one for every other nonidentity `g ∈ U_a`.
The integer-difference theorem puts every value `ψ_a^g(x)` in

```text
ψ_a^g₀(x) + (1 / (2 * d_a)) * ℤ.
```

If `|ψ_a^g(x)| ≤ b`, the corresponding integer has absolute value at most
`2 * d_a * (b + |ψ_a^g₀(x)|)`. The integers satisfying this bound lie in a
finite integer interval. Each such integer determines at most one affine
functional with derivative `rootForm B.i a` and that value at `x`, by
`AffineMap.ext_linear`. This proves
`finite_bounded_reflectionFunctionals_of_oppositePairs`.

Every ordinary affine root is extended, hence is one of these actual point
functionals by `B.reflectionAffineRoots_eq`. There are finitely many actual
relative roots. Taking the finite union of the bounded families, with bound
`bound (rootForm B.i a)` in direction `a`, proves
`finite_bounded_affineRoots_of_oppositePairs`.

The full local-arrangement theorem then supplies this bounded-finiteness
field to `B.isLocallyFiniteReflectionArrangement_of_oppositePairs`, whose
other four fields were already proved from `hF`.

Finally,
`normalizer_facet_fixing_of_reflections_sup_ker_of_oppositePairs` specializes
the prior actual facet-fixing adapter to this proved arrangement. For an
actual normalizer point `n` supplied with membership in

```text
B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker,
```

preservation of a facet setwise implies that `n` fixes every point of that
facet. This theorem needs `hF` and the stated subgroup membership; it has no
separate local-arrangement premise.

## Provenance and retained obligations

This is an internal derivation from the existing finite-index character
restriction theorem, actual centralizer data and character normalization,
same-root reflection correction, V6, actual point functionals and the
preceding algebraic arrangement and facet-fixing constructions. No new
external source assertion is made.

Actual opposite-pair existence remains an explicit premise. Full simply
connected normalizer generation modulo the actual apartment-action kernel
is still unproved: the final theorem does not establish its subgroup
membership premise for all normalizer points. No V7, AS5 or full
apartment-axiom package is used, and this unit does not prove
`SimplyConnectedFacetFixingStatement`.
