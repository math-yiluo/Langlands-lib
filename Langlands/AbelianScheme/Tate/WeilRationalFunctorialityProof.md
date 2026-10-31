# Rational dual-homomorphism compatibility of the actual Weil pairing: proof

`Langlands.AbelianScheme.rationalWeilFunctoriality` proves the published
proposition `Langlands.AbelianScheme.RationalWeilFunctorialityStatement`,
unchanged. For a rational homomorphism `f : Hom0 A B`, `x` in the rational
Tate module of `A` and `y` in that of the constructed dual of `B`, it gives

\[
 E_B(V(f)x,y)=E_A(x,V(f^\vee)y),
\]

where `E_A`, `E_B` are the published `rationalWeilBilinearMap`s, `V` is
`Tate.rationalHomMap` and `f^\vee` is `dualHom0`. The module adds no
definitions. It contains four auxiliary theorems and the final theorem.
Every hypothesis of the statement stays an explicit input: the seven
coherence propositions, the finite Weil transition proposition, the
`HasDualScheme` witnesses, the `DualSchemeGeometry` inputs, the inverse
Poincaré bundles with their evaluation isomorphisms, and the
`DualSchemeMapAdditivity` proposition. None of them is proved here. The
axioms are `propext`, `Classical.choice` and `Quot.sound`.

The route is the reduction proposed in the statement's Markdown. It
evaluates the Library's relative finite functoriality theorem on kernel
lifts, passes coordinatewise to the inverse limit, and then uses tensor
induction in both Tate arguments and in `f`. The mathematical source is the
one cited there: Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
Proposition (11.21)(i) and paragraph (11.23). The relative rational
extension is an internal deduction from the Library's constructions.

## Finite level

`finiteWeilLevelBilinearMap_levelMap` holds for an integral homomorphism
`f : A ⟶ B`, a level `n`, a test object `T` and level elements `x` of `A`
and `y` of the dual `GB` of `B`. It states that the finite level pairing of
`B` at `(levelMap f x, y)` equals the finite level pairing of `A` at
`(x, levelMap (dualMap f) y)`.

The proof writes `x` and `y` as kernel points through the surjective
`GroupScheme.Tate.kernelLevelEquiv`. The published
`GroupScheme.Tate.kernelLevelEquiv_map` turns `levelMap` into composition
with `Tate.kernelLevelMap`. `finiteWeilLevelBilinearMap_apply` then
rewrites both sides as `mu.pointsLevelEquiv n T` of `prod.lift` of the
kernel points followed by `finiteWeilPairing`. The Library theorem
`finiteWeilPairing_dualMap` (in
`Langlands.AlgebraicGeometry.Picard.FiniteWeilFunctorialityProof`) is the
scheme-level identity

```
prod.map (kernelLevelMap f n) (𝟙 _) ≫ finiteWeilPairing_B n =
  prod.map (𝟙 _) (kernelLevelMap (dualMap f) n) ≫ finiteWeilPairing_A n.
```

The proof precomposes it with `prod.lift` of the two kernel points and
simplifies with `prod.lift_map_assoc` and `Category.comp_id`. Because the
identities are typed at definitionally equal but syntactically different
kernel objects, `Category.comp_id` is applied with `erw`. Applying
`mu.pointsLevelEquiv n T ∘ Additive.ofMul` gives the result.

## Integral and rational levels

`integralWeilBilinearMap_map` proves the same identity for the integral
pairings and the integral Tate maps `GroupScheme.Tate.map` of `f` and
`dualMap f`. Two elements of the twist inverse limit are equal when their
coordinates agree, and each coordinate is the finite-level identity.

`rationalWeilBilinearMap_rationalMap` proves it for the rational pairings
and the rational Tate maps `GroupScheme.Tate.rationalMap` of `f` and
`dualMap f`. Both sides are additive in `x` and in `y`, so
`TensorProduct.inductionOn` in both arguments reduces it to pure tensors
`q ⊗ x` and `r ⊗ y`. There `GroupScheme.Tate.rationalMap_tmul` and
`rationalWeilBilinearMap_tmul` give `(q * r) ⊗ₜ` of the two integral
values, which agree by the integral lemma.

## Rational homomorphisms

`rationalWeilBilinearMap_rationalHomMap` proves the identity for every
`f : Hom0 A B = ℚ ⊗ (A ⟶ B)`, with `Tate.rationalHomMap` on both sides and
the dual `dualHom0`. Both sides are additive in `f`, so tensor induction
on `f` reduces to `q ⊗ g` with `g : A ⟶ B`. `dualHom0_tmul` gives
`dualHom0 (q ⊗ g) = q ⊗ dualMap g`. `Tate.rationalHomMap_tmul` gives
`rationalHomMap (q ⊗ g) = q • rationalMap g` on both sides. After moving
the scalar `q` out of both rational pairings, the claim is the previous
lemma for `g`.

`rationalWeilFunctoriality` introduces the statement's binders and applies
this lemma. The statement's `let` bindings `DB` (the constructed dual of
`B`) and `df` (`dualHom0` of `f`) are introduced as local definitions,
and the lemma's type matches the goal after unfolding them.

## Scope

The proof uses the actual constructed Weil pairing, dual abelian scheme,
dual map and rational dual. It assumes no pairing compatibility. It does
not prove nondegeneracy, alternation, or any polarization or adelic
statement. It proves none of the explicit hypotheses of the statement.
