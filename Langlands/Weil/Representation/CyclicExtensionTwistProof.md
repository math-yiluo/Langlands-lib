# Twists of an extension across a finite cyclic quotient: proof

This module proves `Langlands.FiniteRepresentation.cyclicExtensionTwistClassification`,
whose type is the proposition
`Langlands.FiniteRepresentation.CyclicExtensionTwistClassificationStatement.{uK, uG, uV, uW}`
of `Langlands.Weil.Representation.CyclicExtensionTwistStatement`. The statement
module and the modules it imports are used unchanged. The four universes (the
coefficient field, the group and the carriers of `A` and `B`) are independent
throughout, and all equivalences are actual linear intertwining equivalences
`Representation.Equiv` on the given carriers.

## Elementary facts

- `eq_of_forall_smul_eq`: on a nontrivial vector space, `a • v = b • v` for all
  `v` forces `a = b` (apply it to one nonzero vector).
- `nontrivial_of_rank_ne_zero`: the hypothesis `A.rank ≠ 0` makes the carrier of
  `A` nontrivial, by `Module.finrank_pos_iff`.
- `rep_apply_apply`: `ρ g (ρ h v) = ρ (g * h) v`.

## The character of an equivalence on `N`

`exists_twist_equiv_of_restriction_equiv` starts from an equivalence `e` between
the restrictions of `A` and `B` to the normal subgroup `N`. For `g : G` the
operator

`T g = e⁻¹ ∘ B(g) ∘ e ∘ A(g⁻¹)`

on the carrier of `A` commutes with `A(n)` for `n ∈ N`: write
`g⁻¹ n = (g⁻¹ n g) g⁻¹`, use normality (`Subgroup.Normal.conj_mem`) to see
`g⁻¹ n g ∈ N`, move `A(g⁻¹ n g)` through `e`, rewrite `g (g⁻¹ n g) = n g`, and
move `B(n)` back through `e⁻¹`. Hence `T g` is an intertwining endomorphism of
the restriction of `A`, and the hypothesis `HasScalarEndomorphisms` writes it as
`c g • id`. The scalars `c g` are chosen with `choose`. Equivalently
`B(g) (e v) = e (c g • A(g) v)` for all `v`.

Uniqueness of scalars on the nonzero carrier gives `c 1 = 1` and
`c (g h) = c g * c h`: both sides of the second identity are compared after
applying the injective map `e` to `c (g h) • w`, expanding `B(g h) = B(g) B(h)`
and using the displayed relation twice. So `c` is a monoid homomorphism
`G →* K`, and `MonoidHom.toHomUnits` turns it into a character `χ : G →* Kˣ`
(its values are units because `G` is a group; no separate nonvanishing argument
is needed). For `n ∈ N` the operator `T n` is the identity because `e`
intertwines `A(n)` and `B(n)`, so `N ≤ χ.ker`. Finally the same linear
equivalence underlying `e` is an equivalence from `twist χ A` to `B`, by the
displayed relation; the proof first rewrites the carrier of `twist χ A` as that
of `of (Langlands.twist χ A.representation)`, which is the carrier of `A`.

## Restriction of a twist

`restrictionEquivOfTwistEquiv` takes an equivalence from `twist χ A` to `B`,
where `N ≤ χ.ker`, and keeps its linear equivalence: on `n ∈ N` the twisting
scalar `χ n` is `1`, so it intertwines the restrictions to `N`.

## Distinct twists

`eq_of_twist_equiv` shows that an equivalence `φ` from `twist χ A` to `twist ψ A`,
with `χ` and `ψ` trivial on `N`, forces `χ = ψ`. On `N` the two twists are the
restriction of `A`, so `φ` is an intertwining endomorphism of that restriction and
is `a • id`. The scalar `a` is nonzero since `φ` is injective on a nontrivial
space. Applying the intertwining relation of `φ` at `g` to `A(g⁻¹) w` gives
`(χ g * a) • w = (ψ g * a) • w` for every `w`, hence `a * χ g = a * ψ g` and
`χ g = ψ g`.

## The classification

`le_ker_comp_mk'` records that an inflated character `ψ.comp (QuotientGroup.mk' N)`
is trivial on `N` (`QuotientGroup.eq_one_iff`).

In `cyclicExtensionTwistClassification`, `IsCyclic.exists_generator` supplies a
generator `γ` of `G ⧸ N`. By `orderOf_eq_card_of_forall_mem_zpowers` and
`orderOf_injective` (faithfulness of `η`), `η γ` has order `Nat.card (G ⧸ N)`,
which is positive because the quotient is finite (`Subgroup.FiniteIndex`) and
nonempty. So `η γ` is a primitive root of unity of that order
(`IsPrimitiveRoot.orderOf`).

- Every character `ψ : G ⧸ N →* Kˣ` is `η ^ i` for some `i < Nat.card (G ⧸ N)`:
  `ψ γ` is a root of unity of that order (`pow_card_eq_one'`), so
  `IsPrimitiveRoot.eq_pow_of_mem_rootsOfUnity` writes it as `η γ ^ i`, and the two
  homomorphisms agree on every power of the generator (`Subgroup.mem_zpowers_iff`,
  `map_zpow`).
- Distinct exponents below the order give distinct inflated characters:
  evaluating at a lift `g₀` of `γ` (`QuotientGroup.mk_surjective`) gives
  `η γ ^ i = η γ ^ j`, and `pow_injOn_Iio_orderOf` gives `i = j`.

For the forward implication, an equivalence on `N` gives `χ` with `N ≤ χ.ker`
and `twist χ A ≃ B`. The character `QuotientGroup.lift N χ` of the quotient
inflates back to `χ`, and is `η ^ i` for some `i`; this `i` is the existence
witness. If `twist ((η ^ j).comp mk) A ≃ B` as well, composing with the inverse
of the first equivalence and applying `eq_of_twist_equiv` identifies the inflated
characters, so `j = i`. The reverse implication is
`restrictionEquivOfTwistEquiv` applied to the given equivalence.

## Provenance

The statement is the algebraic extension step used in Harris 1998, Lemma 1.6,
pp. 188–189 (`harris-1998-local-langlands`), as described in the Markdown of
`Langlands.Weil.Representation.CyclicExtensionTwistStatement`. The proof here is
an internal argument on actual linear representations using only Mathlib's
representation, quotient-group and roots-of-unity API and the Library
constructions `Langlands.FiniteRepresentation.twist` and
`Langlands.FiniteRepresentation.HasScalarEndomorphisms`; it introduces no new
definitions or assumptions. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
