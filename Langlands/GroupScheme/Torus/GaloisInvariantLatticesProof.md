# Galois descent of characters and cocharacters

`galoisInvariantLattices` proves `GaloisInvariantLatticesStatement.{u}`
with nothing added to the statement. The universe `u` is arbitrary. `K/k` is
any Galois extension and may be infinite. `T` is any commutative group scheme
over `Spec k` whose structure morphism is affine. The proof assumes no finite
type, smoothness, connectedness or torus hypothesis. For both
`characterLattice.baseChangeToInvariants k K T` and
`cocharacterLattice.baseChangeToInvariants k K T`, it proves injectivity and
surjectivity.

## Injectivity

The published theorems `characterLattice.baseChangeToInvariants_injective`
and `cocharacterLattice.baseChangeToInvariants_injective` give the
injectivity clauses. These theorems hold for every field extension.

## Coherence of the `𝔾ₘ` comparison (private lemma `gm_descent_comparison`)

Let `b : S ⟶ B` and `a : S ⟶ S` be scheme morphisms with `a ≫ b = b`. Write
`Gm.baseChangeIso` for the canonical isomorphism from the pullback of `𝔾ₘ` to
`𝔾ₘ`. Write `descentBaseChangeIso b a ha` for the canonical identification of
the pullback along `a` of a pullback along `b` with the pullback along `b`.
The lemma states:

`(baseChange a).map (Gm.baseChangeIso b).hom ≫ (Gm.baseChangeIso a).hom =
 (descentBaseChangeIso b a ha (Gm B)).hom ≫ (Gm.baseChangeIso b).hom`.

To prove it, apply the published
`rationalCharacters.transportCharacter_baseChange` to the identity character
of `𝔾ₘ` over `B`. That lemma says canonical transport along `a` fixes a base
change along `b`. By `rationalCharacters.baseChange_toMul`, the base change of
the identity character is `(baseChange b).map (𝟙 _) ≫
(Gm.baseChangeIso b).hom`, which is `(Gm.baseChangeIso b).hom`. `transportCharacter` is
the composite `(descentBaseChangeIso …).inv ≫ (baseChange a).map χ ≫
(Gm.baseChangeIso a).hom`. Unfolding it and moving the inverse to the other
side gives the displayed equation.

## Surjectivity on characters (private `character_baseChange_surjective`)

Let `b = algebraBaseMap k K` and let `M` be `𝔾ₘ` over `Spec k`. Fix an
invariant character `χ` of `T_K`. Let `c : T_K ⟶ 𝔾ₘ,K` be its actual
homomorphism, and set `f := c ≫ (Gm.baseChangeIso b).inv : T_K ⟶ M_K`.

For `σ : K ≃ₐ[k] K`, let `a = galoisBaseMap k K σ` (`Spec σ`, which lies over
`Spec k`). The Galois action on characters is canonical transport along `a`.
Fixedness of `χ` under `σ` is therefore the equation

`(descentBaseChangeIso b a ha T).inv ≫ (baseChange a).map c ≫
 (Gm.baseChangeIso a).hom = c`.

The proof combines this equation with the coherence lemma, which it uses to
move `Gm.baseChangeIso` across `(baseChange a).map`. This gives the
compatibility hypothesis of `Descent.GaloisHom.exists_hom` for `f`:

`(baseChange a).map f ≫ (descentBaseChangeIso b a ha M).hom =
 (descentBaseChangeIso b a ha T).hom ≫ f`.

The proof verifies this after composing with the isomorphism
`(Gm.baseChangeIso b).hom`, which it may then cancel.

The published `Descent.GaloisHom.exists_hom` applies to any Galois extension
and to groups whose structure morphisms are affine. Here these are `T` and
`M`, and `M` is affine by `isSplitTorus_gm.isAffineHom`. The theorem descends
the closed graph of `f` and returns an actual homomorphism `f₀ : T ⟶ M` over
`k`. Its scalar extension is exactly `f`. The character `Additive.ofMul f₀`
has canonical base change
`(baseChange b).map f₀ ≫ (Gm.baseChangeIso b).hom = f ≫
(Gm.baseChangeIso b).hom = c`. It therefore maps to `χ`.

## Surjectivity on cocharacters (private `cocharacter_baseChange_surjective`)

This argument mirrors the character case. For an invariant cocharacter `ν`
with actual homomorphism `c : 𝔾ₘ,K ⟶ T_K`, set
`f := (Gm.baseChangeIso b).hom ≫ c : M_K ⟶ T_K`. Fixedness of `ν` reads
`(Gm.baseChangeIso a).inv ≫ (baseChange a).map c ≫
(descentBaseChangeIso b a ha T).hom = c`. Rewriting with the same coherence
lemma gives the compatibility hypothesis of `Descent.GaloisHom.exists_hom`.
The descended `f₀ : M ⟶ T` satisfies
`(Gm.baseChangeIso b).inv ≫ (baseChange b).map f₀ = c`, which is the
canonical base change of the cocharacter `Additive.ofMul f₀`.

In both cases the preimage is the actual homomorphism descended to `k`. Its
scalar extension recovers the supplied fixed homomorphism exactly, not only
up to isomorphism.

## Comparison with the source

Chapter 12 of Milne, *Algebraic Groups* (2017), opens on printed p. 230
(PDF p. 246) with the convention that all algebraic groups are affine over
the base field `k`. In that chapter an algebraic group is therefore an affine
group scheme of finite type over `k`, and a character of `G` is a
homomorphism `G → 𝔾ₘ`. In §12.g, printed p. 239 (PDF p. 255), Milne sets
`Γ = Gal(kˢ/k)` and `X*(G) = X(G_{kˢ})`, and states `X*(G)^Γ = X(G)`: the
`Γ`-invariant characters over `kˢ` are exactly the characters defined over
`k`. This formula has no commutativity hypothesis.

Take `K` to be a separable closure of `k`. Mathlib's instance
`IsSepClosure.isGalois` makes it Galois over `k`. The character clause of
this theorem then gives Milne's formula, through the canonical base-change
map, for commutative `G`. The theorem goes beyond that case of the formula
in three ways, none of which Milne states at this place:

- `K/k` may be any Galois extension, finite or infinite;
- `T` may be any commutative group scheme affine over `k`, not necessarily
  of finite type;
- the theorem also proves the cocharacter analogue.

The proof establishes neither of the following:

- Milne's formula for noncommutative affine algebraic groups;
- continuity or finite generation of the Galois action.

Nonaffine group schemes lie outside both Milne's Chapter 12 convention and
this theorem. The proof also says nothing about the classification of groups
of multiplicative type (Milne, Theorem 12.23).
