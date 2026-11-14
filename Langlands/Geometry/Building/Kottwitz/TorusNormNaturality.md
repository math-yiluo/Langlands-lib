# Torus naturality from the norm characterization

This is a derived component of the cocenter construction in Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), section 11.5 before Lemma 11.5.1,
printed pp.429–430 / PDF pp.460–461. The torus norm characterization is
Proposition 11.1.1, printed pp.421–422 / PDF pp.452–453. The November 2024
corrections, Chapter 11 at PDF pp.43–45, concern section 11.7 and do not change
these passages. The new lemmas below are internal deductions using the Library's
actual group schemes and cocharacters, rather than additional source axioms.

All declarations are in `Langlands.Geometry.Building.Kottwitz`. The main
naturality theorem assumes `TorusKottwitzExistenceStatement`; it does not prove
existence of the torus Kottwitz homomorphism. The final cocenter reduction
retains this premise and five comparison statements, so it does not prove the
unconditional host statement.

`relativeNorm_natural` concerns commutative affine group schemes over `k` and a
compatible tower `k → K → L` with `L/K` finite Galois. Every actual morphism
commutes with the relative norm. The proof extends coefficients to `L`, uses
injectivity of that extension on the target, and compares the finite Galois
products term by term using point-map naturality.

`splitValuation_natural` concerns two split tori over a field, an arbitrary
integer-valued valuation on that field, and an actual morphism between the
tori. Applying the target split valuation after mapping a point equals
postcomposition of the source valuation cocharacter. The proof pairs with every
character, uses associativity to move the morphism into the character, and
applies the character-evaluation restriction law. Injectivity of the perfect
character/cocharacter pairing proves equality. No normalization or surjectivity
hypothesis on the valuation is needed for this naturality lemma.

`towerBaseChangeIso_natural` proves naturality of the canonical comparison
between iterated and direct base change through `k → L → E`. The proof uses
naturality of the pullback-composition natural isomorphism, then the elementary
naturality square for transport along equality of base maps.
`extendGeometricCocharacters_natural` applies this comparison to actual
cocharacters. Base-changing postcomposition and then identifying the iterated
base change gives exactly postcomposition by `geometricCocharacterMap` after
extending the source cocharacter.

Let `F` be any nonarchimedean local field, `K = UnramifiedClosure F`, and
`E = SeparableClosure F`. Let `k` map to `K` and `E` in a compatible scalar
tower with `Normal k K`. For tori `S,T` over `k` and an actual morphism
`f : S ⟶ T`, `torusKottwitzPushforward` is the selected homomorphism of `S`
followed by the actual integral inertia map induced by `f`. The definition
needs the source torus hypothesis and uses `Multiplicative` solely to change
the notation on the additive target.

`torusKottwitz_natural_of_existence` assumes the universal
`TorusKottwitzExistenceStatement` and proves, for every actual `K`-coefficient
point `x` of `S`, that

```
(torusKottwitz T (f(x))).toAdd = torusInertiaMap f ((torusKottwitz S x).toAdd).
```

The Lean statement supplies the full field tower, actual point map, torus
hypotheses, and selected maps. It does not require `IsSepClosure k E`.
The proof chooses a common finite Galois splitting field `L/K` inside `E`
for the two base-changed tori. The existence statement supplies surjectivity
of the source relative norm, so every `x` lifts to an `L`-point. Relative norm
naturality and the rational/coefficient point comparison identify the target
norm. Applying the two selected norm laws reduces the equality to split
valuation naturality, tower cocharacter naturality, and the representative law
for the induced inertia map. Thus the whole equality is integral, including
any torsion in the coinvariants. `torusKottwitzPushforward_eq` packages it as
an equality of homomorphisms.

Finally, `simplyConnectedDerivedKottwitz_of_norm_inputs` applies the existing
complete cocenter reduction using the naturality theorem just proved. Its
conclusion is exactly `SimplyConnectedDerivedKottwitzStatement`, and its
remaining explicit premises are:

- `AlgebraicFundamentalGroupComparisonStatement`;
- `AlgebraicFundamentalGroupMapStatement`;
- `TorusFundamentalComparisonStatement`;
- `FundamentalInertiaMapStatement`;
- `TorusInertiaComparisonStatement`;
- `TorusKottwitzExistenceStatement`.

The imported cocenter reduction supplies unique existence for all actual
cocenter squares, the selected-map specification and surjectivity, bijectivity
of every cocenter target map, and uniqueness from each individual square once
these premises hold. This module discharges the previously separate torus
naturality premise. It does not discharge any of the six statements listed
above and does not change the existing target or any of its imported pairs.
