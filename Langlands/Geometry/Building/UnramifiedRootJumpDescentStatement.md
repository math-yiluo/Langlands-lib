# Unramified descent of vanishing root directions

`Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement` is an
unproved proposition isolating a filtration assertion needed for special-point
descent. It is an internal formulation of the root-hyperplane restriction step
in the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 9.9.2, printed page 380 (PDF page 411). It is not a verbatim numbered
statement of the book. Proposition 9.4.23, printed page 357 (PDF page 388),
identifies roots of the reductive special-fiber quotient with derivatives of
vanishing affine roots; Construction 9.6.1 and Theorem 9.6.5 explain the
underlying descent of the valuation. These are source context for the proposed
assertion, rather than a Lean proof. The authors' corrections of 1 November
2024 do not amend Proposition 9.9.2 or 9.4.23; the correction to Proposition
9.4.8 removes its non-divisibility restriction.

Let `F` be any nonarchimedean local field and `K` its maximal unramified
extension. Let `G` be a connected reductive `F`-group, `iS : S → G` a maximal
split torus, and `f : S → T` a map with `f ≫ iT = iS` such that `T_K` is a
maximal split torus of `G_K`. The statement retains the actual opposite-factor
pairs, supplied apartment data `D`, centralizer datum `C`, and integer-valuation
V 6 compatibility from `UnramifiedSpecialPointDescentStatement`. It imposes no
characteristic restriction.

Write `φ x` for the existing torus-then-field restricted root function family
of an upper apartment point `x`. Let `Q : V S → TranslationSpace iS` be the
quotient map by the common annihilator of the lower roots. Let
`P : V S → TranslationSpace iT_K` be `descentCocharacterMap F K f` followed by
the analogous upper quotient. The helper `torusFieldTranslationMap` defines
this composition for any field extension and any map of the original tori;
it asserts no descent property. Thus the derivatives can be compared on the
same unreduced real cocharacter space, without assuming a map between the two
apartments.

For every `Aut(K/F)`-fixed `x : D.Apartment` and every ordinary affine root
`ψ` of `D` that vanishes at `x`, assume `ψ.linear ∘ P` is nonzero. The asserted
conclusion supplies an actual lower relative root `a` and `g ∈ U_a(F)` with
`(φ x) a g = 0`. Its direction satisfies

```
ker (rootForm iS a ∘ Q) = ker (ψ.linear ∘ P).
```

The value zero is an attained finite root-valuation value, hence an actual
filtration jump. The witness root is allowed to be any root in this direction;
no prescribed short or double root is required. This matters for nonreduced
root systems, whose proportional roots can have different jump sets.

The statement has no specialness hypothesis, no lower apartment datum, and no
carrier-identification premise. It concerns every nonconstant vanishing upper
root at every fixed point. Its assertion still requires a proof of the Galois
filtration-jump step. Subgroup preimage identities alone do not establish this
assertion, because they need not reflect strict subgroup inclusions.
